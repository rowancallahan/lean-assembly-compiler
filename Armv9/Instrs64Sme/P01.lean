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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SDOT_ZA_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
def execute_USDOT_ZA_ZZV_S2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
def execute_SUDOT_ZA_ZZV_S2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_UDOT_ZA_ZZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SDOT_ZA_ZZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_USDOT_ZA_ZZW_S4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_UDOT_ZA_ZZV_4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SDOT_ZA_ZZV_4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_USDOT_ZA_ZZV_S4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SUDOT_ZA_ZZV_S4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UDOT_ZA_ZZi_S2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SDOT_ZA_ZZi_S2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_USDOT_ZA_ZZi_S2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SUDOT_ZA_ZZi_S2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_UDOT_ZA_ZZi_D2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_SDOT_ZA_ZZi_D2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UDOT_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SDOT_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_USDOT_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SUDOT_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_UDOT_ZA_ZZi_D4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_SDOT_ZA_ZZi_D4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UVDOT_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name 4)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 3
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let operand1 ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i r) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SVDOT_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name 4)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 3
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let operand1 ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i r) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_USVDOT_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name 4)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 3
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let operand1 ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i r) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SUVDOT_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name 4)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 3
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let operand1 ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i r) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_UVDOT_ZA_ZZi_D4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name 4)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 3
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let operand1 ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i r) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_SVDOT_ZA_ZZi_D4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name 4)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 3
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 3
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let operand1 ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i r) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i s) +i i) (Int.ediv esize 4)))))
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
def execute_UDOT_ZA32_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
                let loop_i_upper := 1
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
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
def execute_SDOT_ZA32_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
                let loop_i_upper := 1
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
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
def execute_UDOT_ZA32_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
                let loop_i_upper := 1
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
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
def execute_SDOT_ZA32_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
                let loop_i_upper := 1
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UDOT_ZA32_ZZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
                let loop_i_upper := 1
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SDOT_ZA32_ZZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
                let loop_i_upper := 1
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UDOT_ZA32_ZZV_4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
                let loop_i_upper := 1
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SDOT_ZA32_ZZV_4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
                let loop_i_upper := 1
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UDOT_ZA32_ZZi_2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 1
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i s) +i i) (Int.ediv esize 2)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SDOT_ZA32_ZZi_2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 1
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i i) (Int.ediv esize 2)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UDOT_ZA32_ZZi_4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 1
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i s) +i i) (Int.ediv esize 2)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SDOT_ZA32_ZZi_4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 1
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i i) (Int.ediv esize 2)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UVDOT_ZA32_ZZi_2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name 2)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 1
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 1
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let operand1 ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i r) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i s) +i i) (Int.ediv esize 2)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SVDOT_ZA32_ZZi_2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name 2)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 1
    let mut loop_vars := (result, vec)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result, vec) := loop_vars
      loop_vars ← do
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
              let sum ← (( do (Elem_read operand3 e esize) ) : SailM (BitVec esize) )
              let sum ← (( do
                let loop_i_lower := 0
                let loop_i_upper := 1
                let mut loop_vars_2 := sum
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let sum := loop_vars_2
                  loop_vars_2 ← do
                    let operand1 ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i r) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i s) +i i) (Int.ediv esize 2)))))
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_UMLALL_ZA_ZZV_1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_UMLSLL_ZA_ZZV_1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SMLALL_ZA_ZZV_1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SMLSLL_ZA_ZZV_1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_USMLALL_ZA_ZZV_S (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_UMLALL_ZA_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_UMLSLL_ZA_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SMLALL_ZA_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SMLSLL_ZA_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_USMLALL_ZA_ZZW_S2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_UMLALL_ZA_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_UMLSLL_ZA_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SMLALL_ZA_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SMLSLL_ZA_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_USMLALL_ZA_ZZV_S2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SUMLALL_ZA_ZZV_S2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_UMLALL_ZA_ZZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_UMLSLL_ZA_ZZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SMLALL_ZA_ZZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SMLSLL_ZA_ZZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_USMLALL_ZA_ZZW_S4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_UMLALL_ZA_ZZV_4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_UMLSLL_ZA_ZZV_4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SMLALL_ZA_ZZV_4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_SMLSLL_ZA_ZZV_4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_USMLALL_ZA_ZZV_S4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SUMLALL_ZA_ZZV_S4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLALL_ZA_ZZi_S (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLSLL_ZA_ZZi_S (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLALL_ZA_ZZi_S (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLSLL_ZA_ZZi_S (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_USMLALL_ZA_ZZi_S (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SUMLALL_ZA_ZZi_S (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_UMLALL_ZA_ZZi_D (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_UMLSLL_ZA_ZZi_D (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_SMLALL_ZA_ZZi_D (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_SMLSLL_ZA_ZZi_D (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLALL_ZA_ZZi_S2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLSLL_ZA_ZZi_S2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLALL_ZA_ZZi_S2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLSLL_ZA_ZZi_S2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_USMLALL_ZA_ZZi_S2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SUMLALL_ZA_ZZi_S2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_UMLALL_ZA_ZZi_D2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_UMLSLL_ZA_ZZi_D2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_SMLALL_ZA_ZZi_D2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_SMLSLL_ZA_ZZi_D2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLALL_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLSLL_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLALL_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLSLL_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_USMLALL_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ index ∧ index ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SUMLALL_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_UMLALL_ZA_ZZi_D4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_UMLSLL_ZA_ZZi_D4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_SMLALL_ZA_ZZi_D4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_SMLSLL_ZA_ZZi_D4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 4))
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
          let loop_i_upper := 3
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
                    let s := ((4 *i segmentbase) +i index)
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((4 *i e) +i i) (Int.ediv esize 4)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 4)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLAL_ZA_ZZV_1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLSL_ZA_ZZV_1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLAL_ZA_ZZV_1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLSL_ZA_ZZV_1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLAL_ZA_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLSL_ZA_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLAL_ZA_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLSL_ZA_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLAL_ZA_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLSL_ZA_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLAL_ZA_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLSL_ZA_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLAL_ZA_ZZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLSL_ZA_ZZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLAL_ZA_ZZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLSL_ZA_ZZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLAL_ZA_ZZV_4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLSL_ZA_ZZV_4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLAL_ZA_ZZV_4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLSL_ZA_ZZV_4x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLAL_ZA_ZZi_1 (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLSL_ZA_ZZi_1 (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLAL_ZA_ZZi_1 (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLSL_ZA_ZZi_1 (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLAL_ZA_ZZi_2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLSL_ZA_ZZi_2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLAL_ZA_ZZi_2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLSL_ZA_ZZi_2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLAL_ZA_ZZi_4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_UMLSL_ZA_ZZi_4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
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
                    let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 s (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLAL_ZA_ZZi_4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_SMLSL_ZA_ZZi_4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 esize)
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
                    let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 ((2 *i e) +i i) (Int.ediv esize 2)))))
                    let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 s (Int.ediv esize 2)))))
                    let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
                    (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product))
                (pure loop_vars_2) ) : SailM (BitVec VL) )
              (ZAvector_set (vec +i i) VL result)
              (pure result)
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMAX_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let res := (Max.max element1 element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMAX_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let res := (Max.max element1 element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMAX_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let res := (Max.max element1 element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMAX_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let res := (Max.max element1 element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMAX_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let res := (Max.max element1 element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMAX_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let res := (Max.max element1 element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMAX_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let res := (Max.max element1 element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMAX_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let res := (Max.max element1 element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMIN_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let res := (Min.min element1 element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMIN_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let res := (Min.min element1 element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMIN_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let res := (Min.min element1 element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMIN_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let res := (Min.min element1 element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMIN_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let res := (Min.min element1 element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMIN_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let res := (Min.min element1 element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMIN_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let res := (Min.min element1 element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMIN_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
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
            let element1 ← do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
            let element2 ← do (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
            let res := (Min.min element1 element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
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
def execute_URSHL_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
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
def execute_SRSHL_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
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
def execute_URSHL_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
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
def execute_SRSHL_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
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
def execute_URSHL_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
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
def execute_SRSHL_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
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
def execute_URSHL_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
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
def execute_SRSHL_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
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
def execute_SQDMULH_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
            let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
            let res := ((2 *i element1) *i element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (SignedSat (Int.shiftr res esize) esize))))))
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
def execute_SQDMULH_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
            let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
            let res := ((2 *i element1) *i element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (SignedSat (Int.shiftr res esize) esize))))))
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
def execute_SQDMULH_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
            let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
            let res := ((2 *i element1) *i element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (SignedSat (Int.shiftr res esize) esize))))))
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
def execute_SQDMULH_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
            let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
            let res := ((2 *i element1) *i element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (SignedSat (Int.shiftr res esize) esize))))))
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
def execute_ADD_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (element1 + element2)))))
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
def execute_ADD_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (element1 + element2)))))
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
def execute_UCLAMP_MZ_ZZ_2 (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
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
            let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
            let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
            let element3 ← do (pure (BitVec.toNat (← (Elem_read operand3 e esize))))
            let res := (Min.min (Max.max element1 element3) element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCLAMP_MZ_ZZ_2 (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
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
            let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
            let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
            let element3 ← do (pure (BitVec.toInt (← (Elem_read operand3 e esize))))
            let res := (Min.min (Max.max element1 element3) element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
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
def execute_UCLAMP_MZ_ZZ_4 (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
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
            let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
            let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 e esize))))
            let element3 ← do (pure (BitVec.toNat (← (Elem_read operand3 e esize))))
            let res := (Min.min (Max.max element1 element3) element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
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
def execute_SCLAMP_MZ_ZZ_4 (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
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
            let element1 ← do (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
            let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
            let element3 ← do (pure (BitVec.toInt (← (Elem_read operand3 e esize))))
            let res := (Min.min (Max.max element1 element3) element2)
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (integer_subrange res (esize -i 1) 0)))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UUNPK_MZ_Z_2 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let hsize := (Int.ediv esize 2)
  let sreg := (Int.ediv nreg 2)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (sreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_i_lower := 0
        let loop_i_upper := 1
        let mut loop_vars_1 := results
        for i in [loop_i_lower:loop_i_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let loop_e_lower := 0
            let loop_e_upper := (elements -i 1)
            let mut loop_vars_2 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_2
              loop_vars_2 ← do
                let element ← (( do (Elem_read operand ((i *i elements) +i e) hsize) ) : SailM (BitVec hsize) )
                (pure (vectorUpdate results ((2 *i r) +i i) (← (Elem_set (GetElem?.getElem! results ((2 *i r) +i i)) e esize (← (Extend element esize is_unsigned))))))
            (pure loop_vars_2)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_3 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_3
    loop_vars_3 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_3)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SUNPK_MZ_Z_2 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let hsize := (Int.ediv esize 2)
  let sreg := (Int.ediv nreg 2)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (sreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_i_lower := 0
        let loop_i_upper := 1
        let mut loop_vars_1 := results
        for i in [loop_i_lower:loop_i_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let loop_e_lower := 0
            let loop_e_upper := (elements -i 1)
            let mut loop_vars_2 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_2
              loop_vars_2 ← do
                let element ← (( do (Elem_read operand ((i *i elements) +i e) hsize) ) : SailM (BitVec hsize) )
                (pure (vectorUpdate results ((2 *i r) +i i) (← (Elem_set (GetElem?.getElem! results ((2 *i r) +i i)) e esize (← (Extend element esize is_unsigned))))))
            (pure loop_vars_2)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_3 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_3
    loop_vars_3 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_3)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UUNPK_MZ_Z_4 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let hsize := (Int.ediv esize 2)
  let sreg := (Int.ediv nreg 2)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (sreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_i_lower := 0
        let loop_i_upper := 1
        let mut loop_vars_1 := results
        for i in [loop_i_lower:loop_i_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let loop_e_lower := 0
            let loop_e_upper := (elements -i 1)
            let mut loop_vars_2 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_2
              loop_vars_2 ← do
                let element ← (( do (Elem_read operand ((i *i elements) +i e) hsize) ) : SailM (BitVec hsize) )
                (pure (vectorUpdate results ((2 *i r) +i i) (← (Elem_set (GetElem?.getElem! results ((2 *i r) +i i)) e esize (← (Extend element esize is_unsigned))))))
            (pure loop_vars_2)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_3 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_3
    loop_vars_3 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_3)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SUNPK_MZ_Z_4 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let hsize := (Int.ediv esize 2)
  let sreg := (Int.ediv nreg 2)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (sreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_i_lower := 0
        let loop_i_upper := 1
        let mut loop_vars_1 := results
        for i in [loop_i_lower:loop_i_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            let loop_e_lower := 0
            let loop_e_upper := (elements -i 1)
            let mut loop_vars_2 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_2
              loop_vars_2 ← do
                let element ← (( do (Elem_read operand ((i *i elements) +i e) hsize) ) : SailM (BitVec hsize) )
                (pure (vectorUpdate results ((2 *i r) +i i) (← (Elem_set (GetElem?.getElem! results ((2 *i r) +i i)) e esize (← (Extend element esize is_unsigned))))))
            (pure loop_vars_2)
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_3 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_3
    loop_vars_3 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_3)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHR_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (2 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 1
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
            let res := (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1))) shift)
            (Elem_set result ((r *i elements) +i e) esize (← (SignedSat res esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQRSHR_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (2 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 1
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
            let res := (_shr_int_general ((BitVec.toNat element) +i (_shl_int_general 1 (shift -i 1))) shift)
            (Elem_set result ((r *i elements) +i e) esize (← (UnsignedSat res esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRU_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (2 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 1
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
            let res := (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1))) shift)
            (Elem_set result ((r *i elements) +i e) esize (← (UnsignedSat res esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRN_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (4 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_i_lower := 0
        let loop_i_upper := 3
        let mut loop_vars_1 := result
        for i in [loop_i_lower:loop_i_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let operand ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
            let element ← (( do (Elem_read operand e (4 *i esize)) ) : SailM (BitVec (4 * esize)) )
            let res := (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1))) shift)
            (Elem_set result ((4 *i e) +i i) esize (← (SignedSat res esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQRSHRN_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (4 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_i_lower := 0
        let loop_i_upper := 3
        let mut loop_vars_1 := result
        for i in [loop_i_lower:loop_i_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let operand ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
            let element ← (( do (Elem_read operand e (4 *i esize)) ) : SailM (BitVec (4 * esize)) )
            let res := (_shr_int_general ((BitVec.toNat element) +i (_shl_int_general 1 (shift -i 1))) shift)
            (Elem_set result ((4 *i e) +i i) esize (← (UnsignedSat res esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRUN_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (4 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_i_lower := 0
        let loop_i_upper := 3
        let mut loop_vars_1 := result
        for i in [loop_i_lower:loop_i_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let operand ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
            let element ← (( do (Elem_read operand e (4 *i esize)) ) : SailM (BitVec (4 * esize)) )
            let res := (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1))) shift)
            (Elem_set result ((4 *i e) +i i) esize (← (UnsignedSat res esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHR_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (4 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 3
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e (4 *i esize)) ) : SailM (BitVec (4 * esize)) )
            let res := (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1))) shift)
            (Elem_set result ((r *i elements) +i e) esize (← (SignedSat res esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQRSHR_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (4 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 3
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e (4 *i esize)) ) : SailM (BitVec (4 * esize)) )
            let res := (_shr_int_general ((BitVec.toNat element) +i (_shl_int_general 1 (shift -i 1))) shift)
            (Elem_set result ((r *i elements) +i e) esize (← (UnsignedSat res esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRU_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (4 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 3
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element ← (( do (Elem_read operand e (4 *i esize)) ) : SailM (BitVec (4 * esize)) )
            let res := (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1))) shift)
            (Elem_set result ((r *i elements) +i e) esize (← (UnsignedSat res esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVT_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (2 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 1
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element ← do (pure (BitVec.toInt (← (Elem_read operand e (2 *i esize)))))
            (Elem_set result ((r *i elements) +i e) esize (← (SignedSat element esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQCVT_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (2 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 1
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element ← do (pure (BitVec.toNat (← (Elem_read operand e (2 *i esize)))))
            (Elem_set result ((r *i elements) +i e) esize (← (UnsignedSat element esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVTU_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (2 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 1
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element ← do (pure (BitVec.toInt (← (Elem_read operand e (2 *i esize)))))
            (Elem_set result ((r *i elements) +i e) esize (← (UnsignedSat element esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVTN_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (4 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_i_lower := 0
        let loop_i_upper := 3
        let mut loop_vars_1 := result
        for i in [loop_i_lower:loop_i_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let operand ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
            let element ← do (pure (BitVec.toInt (← (Elem_read operand e (4 *i esize)))))
            (Elem_set result ((4 *i e) +i i) esize (← (SignedSat element esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQCVTN_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (4 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_i_lower := 0
        let loop_i_upper := 3
        let mut loop_vars_1 := result
        for i in [loop_i_lower:loop_i_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let operand ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
            let element ← do (pure (BitVec.toNat (← (Elem_read operand e (4 *i esize)))))
            (Elem_set result ((4 *i e) +i i) esize (← (UnsignedSat element esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVTUN_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (4 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let loop_i_lower := 0
        let loop_i_upper := 3
        let mut loop_vars_1 := result
        for i in [loop_i_lower:loop_i_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let operand ← (( do (Z_read (n +i i) VL) ) : SailM (BitVec VL) )
            let element ← do (pure (BitVec.toInt (← (Elem_read operand e (4 *i esize)))))
            (Elem_set result ((4 *i e) +i i) esize (← (UnsignedSat element esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVT_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (4 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 3
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element ← do (pure (BitVec.toInt (← (Elem_read operand e (4 *i esize)))))
            (Elem_set result ((r *i elements) +i e) esize (← (SignedSat element esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQCVT_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (4 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 3
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element ← do (pure (BitVec.toNat (← (Elem_read operand e (4 *i esize)))))
            (Elem_set result ((r *i elements) +i e) esize (← (UnsignedSat element esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVTU_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL (4 *i esize))
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 3
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element ← do (pure (BitVec.toInt (← (Elem_read operand e (4 *i esize)))))
            (Elem_set result ((r *i elements) +i e) esize (← (UnsignedSat element esize)))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set d VL result)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIP_MZ_ZZ_2 (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let pairs := (Int.ediv VL (esize *i 2))
  let operand0 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand1 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 1
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let base := (r *i pairs)
        let result ← (( do
          let loop_p_lower := 0
          let loop_p_upper := (pairs -i 1)
          let mut loop_vars_1 := result
          for p in [loop_p_lower:loop_p_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let result ← (Elem_set result ((2 *i p) +i 0) esize (← (Elem_read operand0 (base +i p) esize)))
              (Elem_set result ((2 *i p) +i 1) esize (← (Elem_read operand1 (base +i p) esize)))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        (Z_set (d +i r) VL result)
        (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZP_MZ_ZZ_2 (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let pairs := (Int.ediv VL (esize *i 2))
  let result0 ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result1 ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result0, result1) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 1
    let mut loop_vars := (result0, result1)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result0, result1) := loop_vars
      loop_vars ← do
        let base := (r *i pairs)
        let operand ← (( do
          if ((r == 0) : Bool)
          then (Z_read n VL)
          else (Z_read m VL) ) : SailM (BitVec VL) )
        let (result0, result1) ← (( do
          let loop_p_lower := 0
          let loop_p_upper := (pairs -i 1)
          let mut loop_vars_1 := (result0, result1)
          for p in [loop_p_lower:loop_p_upper:1]i do
            let (result0, result1) := loop_vars_1
            loop_vars_1 ← do
              let result0 ← (Elem_set result0 (base +i p) esize (← (Elem_read operand ((2 *i p) +i 0) esize)))
              let result1 ← (Elem_set result1 (base +i p) esize (← (Elem_read operand ((2 *i p) +i 1) esize)))
              (pure (result0, result1))
          (pure loop_vars_1) ) : SailM ((BitVec VL) × (BitVec VL)) )
        (pure (result0, result1))
    (pure loop_vars) ) : SailM ((BitVec VL) × (BitVec VL)) )
  (Z_set (d +i 0) VL result0)
  (Z_set (d +i 1) VL result1)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIP_MZ_ZZ_2Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  if ((VL <b (esize *i 2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let pairs := (Int.ediv VL (esize *i 2))
  let operand0 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand1 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 1
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let base := (r *i pairs)
        let result ← (( do
          let loop_p_lower := 0
          let loop_p_upper := (pairs -i 1)
          let mut loop_vars_1 := result
          for p in [loop_p_lower:loop_p_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let result ← (Elem_set result ((2 *i p) +i 0) esize (← (Elem_read operand0 (base +i p) esize)))
              (Elem_set result ((2 *i p) +i 1) esize (← (Elem_read operand1 (base +i p) esize)))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        (Z_set (d +i r) VL result)
        (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZP_MZ_ZZ_2Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  if ((VL <b (esize *i 2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let pairs := (Int.ediv VL (esize *i 2))
  let result0 ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result1 ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result0, result1) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 1
    let mut loop_vars := (result0, result1)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result0, result1) := loop_vars
      loop_vars ← do
        let base := (r *i pairs)
        let operand ← (( do
          if ((r == 0) : Bool)
          then (Z_read n VL)
          else (Z_read m VL) ) : SailM (BitVec VL) )
        let (result0, result1) ← (( do
          let loop_p_lower := 0
          let loop_p_upper := (pairs -i 1)
          let mut loop_vars_1 := (result0, result1)
          for p in [loop_p_lower:loop_p_upper:1]i do
            let (result0, result1) := loop_vars_1
            loop_vars_1 ← do
              let result0 ← (Elem_set result0 (base +i p) esize (← (Elem_read operand ((2 *i p) +i 0) esize)))
              let result1 ← (Elem_set result1 (base +i p) esize (← (Elem_read operand ((2 *i p) +i 1) esize)))
              (pure (result0, result1))
          (pure loop_vars_1) ) : SailM ((BitVec VL) × (BitVec VL)) )
        (pure (result0, result1))
    (pure loop_vars) ) : SailM ((BitVec VL) × (BitVec VL)) )
  (Z_set (d +i 0) VL result0)
  (Z_set (d +i 1) VL result1)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIP_MZ_Z_4 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  if ((VL <b (esize *i 4)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let quads := (Int.ediv VL (esize *i 4))
  let operand0 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand1 ← (( do (Z_read (n +i 1) VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read (n +i 2) VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read (n +i 3) VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 3
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let base := (r *i quads)
        let result ← (( do
          let loop_q_lower := 0
          let loop_q_upper := (quads -i 1)
          let mut loop_vars_1 := result
          for q in [loop_q_lower:loop_q_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let result ← (Elem_set result ((4 *i q) +i 0) esize (← (Elem_read operand0 (base +i q) esize)))
              let result ← (Elem_set result ((4 *i q) +i 1) esize (← (Elem_read operand1 (base +i q) esize)))
              let result ← (Elem_set result ((4 *i q) +i 2) esize (← (Elem_read operand2 (base +i q) esize)))
              (Elem_set result ((4 *i q) +i 3) esize (← (Elem_read operand3 (base +i q) esize)))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        (Z_set (d +i r) VL result)
        (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZP_MZ_Z_4 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  if ((VL <b (esize *i 4)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let quads := (Int.ediv VL (esize *i 4))
  let result0 ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result1 ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result2 ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result3 ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result0, result1, result2, result3) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 3
    let mut loop_vars := (result0, result1, result2, result3)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result0, result1, result2, result3) := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let base := (r *i quads)
        let (result0, result1, result2, result3) ← (( do
          let loop_q_lower := 0
          let loop_q_upper := (quads -i 1)
          let mut loop_vars_1 := (result0, result1, result2, result3)
          for q in [loop_q_lower:loop_q_upper:1]i do
            let (result0, result1, result2, result3) := loop_vars_1
            loop_vars_1 ← do
              let result0 ← (Elem_set result0 (base +i q) esize (← (Elem_read operand ((4 *i q) +i 0) esize)))
              let result1 ← (Elem_set result1 (base +i q) esize (← (Elem_read operand ((4 *i q) +i 1) esize)))
              let result2 ← (Elem_set result2 (base +i q) esize (← (Elem_read operand ((4 *i q) +i 2) esize)))
              let result3 ← (Elem_set result3 (base +i q) esize (← (Elem_read operand ((4 *i q) +i 3) esize)))
              (pure (result0, result1, result2, result3))
          (pure loop_vars_1) ) : SailM ((BitVec VL) × (BitVec VL) × (BitVec VL) × (BitVec VL)) )
        (pure (result0, result1, result2, result3))
    (pure loop_vars) ) : SailM ((BitVec VL) × (BitVec VL) × (BitVec VL) × (BitVec VL)) )
  (Z_set (d +i 0) VL result0)
  (Z_set (d +i 1) VL result1)
  (Z_set (d +i 2) VL result2)
  (Z_set (d +i 3) VL result3)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIP_MZ_Z_4Q (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  if ((VL <b (esize *i 4)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let quads := (Int.ediv VL (esize *i 4))
  let operand0 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand1 ← (( do (Z_read (n +i 1) VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read (n +i 2) VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (Z_read (n +i 3) VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 3
    let mut loop_vars := result
    for r in [loop_r_lower:loop_r_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let base := (r *i quads)
        let result ← (( do
          let loop_q_lower := 0
          let loop_q_upper := (quads -i 1)
          let mut loop_vars_1 := result
          for q in [loop_q_lower:loop_q_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let result ← (Elem_set result ((4 *i q) +i 0) esize (← (Elem_read operand0 (base +i q) esize)))
              let result ← (Elem_set result ((4 *i q) +i 1) esize (← (Elem_read operand1 (base +i q) esize)))
              let result ← (Elem_set result ((4 *i q) +i 2) esize (← (Elem_read operand2 (base +i q) esize)))
              (Elem_set result ((4 *i q) +i 3) esize (← (Elem_read operand3 (base +i q) esize)))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        (Z_set (d +i r) VL result)
        (pure result)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZP_MZ_Z_4Q (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  if ((VL <b (esize *i 4)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let quads := (Int.ediv VL (esize *i 4))
  let result0 ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result1 ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result2 ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result3 ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let (result0, result1, result2, result3) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := 3
    let mut loop_vars := (result0, result1, result2, result3)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (result0, result1, result2, result3) := loop_vars
      loop_vars ← do
        let operand ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let base := (r *i quads)
        let (result0, result1, result2, result3) ← (( do
          let loop_q_lower := 0
          let loop_q_upper := (quads -i 1)
          let mut loop_vars_1 := (result0, result1, result2, result3)
          for q in [loop_q_lower:loop_q_upper:1]i do
            let (result0, result1, result2, result3) := loop_vars_1
            loop_vars_1 ← do
              let result0 ← (Elem_set result0 (base +i q) esize (← (Elem_read operand ((4 *i q) +i 0) esize)))
              let result1 ← (Elem_set result1 (base +i q) esize (← (Elem_read operand ((4 *i q) +i 1) esize)))
              let result2 ← (Elem_set result2 (base +i q) esize (← (Elem_read operand ((4 *i q) +i 2) esize)))
              let result3 ← (Elem_set result3 (base +i q) esize (← (Elem_read operand ((4 *i q) +i 3) esize)))
              (pure (result0, result1, result2, result3))
          (pure loop_vars_1) ) : SailM ((BitVec VL) × (BitVec VL) × (BitVec VL) × (BitVec VL)) )
        (pure (result0, result1, result2, result3))
    (pure loop_vars) ) : SailM ((BitVec VL) × (BitVec VL) × (BitVec VL) × (BitVec VL)) )
  (Z_set (d +i 0) VL result0)
  (Z_set (d +i 1) VL result1)
  (Z_set (d +i 2) VL result2)
  (Z_set (d +i 3) VL result3)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SEL_MZ_P_ZZ_2 (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then (do (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (Elem_read operand1 e esize)))))))
            else (do (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (Elem_read operand2 e esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SEL_MZ_P_ZZ_4 (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let results ← (( do (undefined_vector 4 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 4) )
  let pred ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mask ← (( do (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0) (PL *i nreg)) ) : SailM (BitVec (PL * nreg)) )
  let results ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := results
    for r in [loop_r_lower:loop_r_upper:1]i do
      let results := loop_vars
      loop_vars ← do
        let operand1 ← (( do (Z_read (n +i r) VL) ) : SailM (BitVec VL) )
        let operand2 ← (( do (Z_read (m +i r) VL) ) : SailM (BitVec VL) )
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := results
        for e in [loop_e_lower:loop_e_upper:1]i do
          let results := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask ((r *i elements) +i e) esize)) : Bool)
            then (do (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (Elem_read operand1 e esize)))))))
            else (do (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e esize (← (Elem_read operand2 e esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (d +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_BMOPA_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 row esize) ) : SailM (BitVec esize) )
        let loop_col_lower := 0
        let loop_col_upper := (dim -i 1)
        let mut loop_vars_1 := result
        for col in [loop_col_lower:loop_col_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element2 ← (( do (Elem_read operand2 col esize) ) : SailM (BitVec esize) )
            let element3 ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
            if ((←((ActivePredicateElement mask1 row esize) <&&> (do
                 (ActivePredicateElement mask2 col esize)))) : Bool)
            then
              (do
                let res : Int := (BitCount (Complement.complement (element1 ^^^ element2)))
                let res : Int :=
                  if (sub_op : Bool)
                  then (Neg.neg res)
                  else res
                let res := res
                (Elem_set result ((row *i dim) +i col) esize (BitVec.addInt element3 res)))
            else (do (Elem_set result ((row *i dim) +i col) esize element3))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_BMOPS_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
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
        let element1 ← (( do (Elem_read operand1 row esize) ) : SailM (BitVec esize) )
        let loop_col_lower := 0
        let loop_col_upper := (dim -i 1)
        let mut loop_vars_1 := result
        for col in [loop_col_lower:loop_col_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let element2 ← (( do (Elem_read operand2 col esize) ) : SailM (BitVec esize) )
            let element3 ← (( do (Elem_read operand3 ((row *i dim) +i col) esize) ) : SailM (BitVec esize) )
            if ((←((ActivePredicateElement mask1 row esize) <&&> (do
                 (ActivePredicateElement mask2 col esize)))) : Bool)
            then
              (do
                let res : Int := (BitCount (Complement.complement (element1 ^^^ element2)))
                let res : Int :=
                  if (sub_op : Bool)
                  then (Neg.neg res)
                  else res
                let res := res
                (Elem_set result ((row *i dim) +i col) esize (BitVec.addInt element3 res)))
            else (do (Elem_set result ((row *i dim) +i col) esize element3))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SMOPA_ZA32_PP_ZZ_16 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
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
                let loop_k_upper := 1
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((2 *i row) +i k) (Int.ediv esize 2)) <&&> (do
                           (ActivePredicateElement mask2 ((2 *i col) +i k) (Int.ediv esize 2))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((2 *i row) +i k) (Int.ediv esize 2))) is_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((2 *i col) +i k) (Int.ediv esize 2))) is_unsigned))))
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

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_UMOPA_ZA32_PP_ZZ_16 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
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
                let loop_k_upper := 1
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((2 *i row) +i k) (Int.ediv esize 2)) <&&> (do
                           (ActivePredicateElement mask2 ((2 *i col) +i k) (Int.ediv esize 2))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((2 *i row) +i k) (Int.ediv esize 2))) is_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((2 *i col) +i k) (Int.ediv esize 2))) is_unsigned))))
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

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SMOPS_ZA32_PP_ZZ_16 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
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
                let loop_k_upper := 1
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((2 *i row) +i k) (Int.ediv esize 2)) <&&> (do
                           (ActivePredicateElement mask2 ((2 *i col) +i k) (Int.ediv esize 2))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((2 *i row) +i k) (Int.ediv esize 2))) is_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((2 *i col) +i k) (Int.ediv esize 2))) is_unsigned))))
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

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem da [0, 1, 2, 3] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_UMOPS_ZA32_PP_ZZ_16 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
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
                let loop_k_upper := 1
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let (prod, sum) ← (( do
                      if ((←((ActivePredicateElement mask1 ((2 *i row) +i k) (Int.ediv esize 2)) <&&> (do
                           (ActivePredicateElement mask2 ((2 *i col) +i k) (Int.ediv esize 2))))) : Bool)
                      then
                        (do
                          let prod ← (pure ((← (asl_Int (← (Elem_read operand1 ((2 *i row) +i k) (Int.ediv esize 2))) is_unsigned)) *i (← (asl_Int (← (Elem_read operand2 ((2 *i col) +i k) (Int.ediv esize 2))) is_unsigned))))
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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, isize : Nat, n : Nat, nreg : Nat, nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ isize = 2 ∧ 0 ≤ imm ∧ imm ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI2_Z_ZTZ__ (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let segments := (Int.ediv esize (isize *i nreg))
  let segment := (Nat.mod imm segments)
  let indexes ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let base := (((segment *i nreg) +i r) *i elements)
      let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
      let result ← (( do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let index ← do (pure (BitVec.toNat (← (Elem_read indexes (base +i e) isize))))
            sail_assert ((esize -i 1) <b 32) "src/instrs64_sme.sail:35958.46-35958.47"
            (Elem_set result e esize (Sail.BitVec.extractLsb (← (Elem_read table index 32)) (esize -i 1) 0))
        (pure loop_vars_1) ) : SailM (BitVec VL) )
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, isize : Nat, n : Nat, nreg : Nat, nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ isize = 4 ∧ List.elem imm [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI4_Z_ZTZ__ (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let segments := (Int.ediv esize (isize *i nreg))
  let segment := (Nat.mod imm segments)
  let indexes ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      let base := (((segment *i nreg) +i r) *i elements)
      let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
      let result ← (( do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars_1 := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars_1
          loop_vars_1 ← do
            let index ← do (pure (BitVec.toNat (← (Elem_read indexes (base +i e) isize))))
            sail_assert ((esize -i 1) <b 32) "src/instrs64_sme.sail:36028.46-36028.47"
            (Elem_set result e esize (Sail.BitVec.extractLsb (← (Elem_read table index 32)) (esize -i 1) 0))
        (pure loop_vars_1) ) : SailM (BitVec VL) )
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ isize = 2 ∧ List.elem imm [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ dstride = 1 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI2_MZ2_ZTZ_1 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let segments := (Int.ediv esize (isize *i nreg))
  let segment := (Nat.mod imm segments)
  let indexes ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := d
    for r in [loop_r_lower:loop_r_upper:1]i do
      let d := loop_vars
      loop_vars ← do
        let base := (((segment *i nreg) +i r) *i elements)
        let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let index ← do (pure (BitVec.toNat (← (Elem_read indexes (base +i e) isize))))
              sail_assert ((esize -i 1) <b 32) "src/instrs64_sme.sail:36099.46-36099.47"
              (Elem_set result e esize (Sail.BitVec.extractLsb (← (Elem_read table index 32)) (esize -i 1) 0))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        (Z_set d VL result)
        (pure (d +i dstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ isize = 4 ∧ List.elem imm [0, 1, 2, 3] ∧ List.elem esize [8, 16, 32, 64] ∧ dstride = 1 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI4_MZ2_ZTZ_1 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let segments := (Int.ediv esize (isize *i nreg))
  let segment := (Nat.mod imm segments)
  let indexes ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := d
    for r in [loop_r_lower:loop_r_upper:1]i do
      let d := loop_vars
      loop_vars ← do
        let base := (((segment *i nreg) +i r) *i elements)
        let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let index ← do (pure (BitVec.toNat (← (Elem_read indexes (base +i e) isize))))
              sail_assert ((esize -i 1) <b 32) "src/instrs64_sme.sail:36172.46-36172.47"
              (Elem_set result e esize (Sail.BitVec.extractLsb (← (Elem_read table index 32)) (esize -i 1) 0))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        (Z_set d VL result)
        (pure (d +i dstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ isize = 2 ∧ List.elem imm [0, 1, 2, 3] ∧ List.elem esize [8, 16, 32, 64] ∧ dstride = 1 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI2_MZ4_ZTZ_1 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let segments := (Int.ediv esize (isize *i nreg))
  let segment := (Nat.mod imm segments)
  let indexes ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := d
    for r in [loop_r_lower:loop_r_upper:1]i do
      let d := loop_vars
      loop_vars ← do
        let base := (((segment *i nreg) +i r) *i elements)
        let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let index ← do (pure (BitVec.toNat (← (Elem_read indexes (base +i e) isize))))
              sail_assert ((esize -i 1) <b 32) "src/instrs64_sme.sail:36245.46-36245.47"
              (Elem_set result e esize (Sail.BitVec.extractLsb (← (Elem_read table index 32)) (esize -i 1) 0))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        (Z_set d VL result)
        (pure (d +i dstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ isize = 4 ∧ List.elem imm [0, 1] ∧ List.elem esize [8, 16, 32, 64] ∧ dstride = 1 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI4_MZ4_ZTZ_1 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let segments := (Int.ediv esize (isize *i nreg))
  let segment := (fmod_int imm segments)
  let indexes ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := d
    for r in [loop_r_lower:loop_r_upper:1]i do
      let d := loop_vars
      loop_vars ← do
        let base := (((segment *i nreg) +i r) *i elements)
        let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let index ← do (pure (BitVec.toNat (← (Elem_read indexes (base +i e) isize))))
              sail_assert ((esize -i 1) <b 32) "src/instrs64_sme.sail:36318.46-36318.47"
              (Elem_set result e esize (Sail.BitVec.extractLsb (← (Elem_read table index 32)) (esize -i 1) 0))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        (Z_set d VL result)
        (pure (d +i dstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 31 -/
def execute_LDR_ZT_BR__ (n : Nat) : SailM Unit := do
  (CheckSMEEnabled ())
  (CheckSMEZT0Enabled ())
  let elements := (Int.ediv 512 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 512) ) : SailM (BitVec 512) )
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
  let aligned : Bool := (IsAligned__1 base 16)
  if ((←((pure (! aligned)) <&&> (do
       (AlignmentEnforced ())))) : Bool)
  then (AArch64_Abort base (← (AlignmentFault accdesc)))
  else (pure ())
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e 8 (← (AArch64_MemSingle_read (BitVec.addInt base e) 1 accdesc aligned)))
    (pure loop_vars) ) : SailM (BitVec 512) )
  (ZT0_set 512 result)

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 31 -/
def execute_STR_ZT_BR__ (n : Nat) : SailM Unit := do
  (CheckSMEEnabled ())
  (CheckSMEZT0Enabled ())
  let elements := (Int.ediv 512 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
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
  let aligned : Bool := (IsAligned__1 base 16)
  if ((←((pure (! aligned)) <&&> (do
       (AlignmentEnforced ())))) : Bool)
  then (AArch64_Abort base (← (AlignmentFault accdesc)))
  else (pure ())
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do (AArch64_MemSingle_set (BitVec.addInt base e) 1 accdesc aligned (← (Elem_read table e 8)))
  (pure loop_vars)

def execute_ZERO_ZT_I__ (_ : Unit) : SailM Unit := do
  (CheckSMEEnabled ())
  (CheckSMEZT0Enabled ())
  if ((←((HaveTME ()) <&&> (do
       (pure ((← readReg TSTATE).depth >b 0))))) : Bool)
  then (FailTransaction TMFailure_ERR false)
  else (pure ())
  (ZT0_set 512 (Zeros (n := 512)))

/-- Type quantifiers: offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_MOVT_R_ZT__ (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckSMEEnabled ())
  (CheckSMEZT0Enabled ())
  let operand ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  (X_set t 64 (← (Elem_read operand offset 64)))

/-- Type quantifiers: offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_MOVT_ZT_R__ (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckSMEEnabled ())
  (CheckSMEZT0Enabled ())
  let result ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let result ← (Elem_set result offset 64 (← (X_read t 64)))
  (ZT0_set 512 result)

/-- Type quantifiers: SVL : Nat, d : Nat, imm : Int, 0 ≤ d ∧ d ≤ 31 ∧ (is_VL SVL) -/
def execute_RDSVL_R_I__ (SVL : Nat) (d : Nat) (imm : Int) : SailM Unit := do
  (CheckSMEEnabled ())
  let SVL := SVL
  let len := (imm *i (Int.ediv SVL 8))
  (X_set d 64 (integer_subrange len 63 0))

/-- Type quantifiers: SVL : Nat, d : Nat, imm : Int, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL SVL) -/
def execute_ADDSPL_R_RI__ (SVL : Nat) (d : Nat) (imm : Int) (n : Nat) : SailM Unit := do
  (CheckSMEEnabled ())
  let SVL := SVL
  let len := (imm *i (Int.ediv SVL 64))
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then (SP_read ())
    else (X_read n 64) ) : SailM (BitVec 64) )
  let result : (BitVec 64) := (BitVec.addInt operand1 len)
  if ((d == 31) : Bool)
  then (SP_set result)
  else (X_set d 64 result)

/-- Type quantifiers: SVL : Nat, d : Nat, imm : Int, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL SVL) -/
def execute_ADDSVL_R_RI__ (SVL : Nat) (d : Nat) (imm : Int) (n : Nat) : SailM Unit := do
  (CheckSMEEnabled ())
  let SVL := SVL
  let len := (imm *i (Int.ediv SVL 8))
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then (SP_read ())
    else (X_read n 64) ) : SailM (BitVec 64) )
  let result : (BitVec 64) := (BitVec.addInt operand1 len)
  if ((d == 31) : Bool)
  then (SP_set result)
  else (X_set d 64 result)

/-- Type quantifiers: VL : Nat, ngrp : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ ngrp = 2 ∧ (is_VL VL) -/
def execute_ZERO_ZA1_RI_2 (VL : Nat) (ngrp : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name ngrp)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let vec ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (ngrp -i 1)
    let mut loop_vars := vec
    for r in [loop_r_lower:loop_r_upper:1]i do
      let vec := loop_vars
      loop_vars ← do
        let vec := vec
        (ZAvector_set vec VL (Zeros (n := VL)))
        (pure (vec +i vstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, ngrp : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ ngrp = 4 ∧ (is_VL VL) -/
def execute_ZERO_ZA1_RI_4 (VL : Nat) (ngrp : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name ngrp)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let vec ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (ngrp -i 1)
    let mut loop_vars := vec
    for r in [loop_r_lower:loop_r_upper:1]i do
      let vec := loop_vars
      loop_vars ← do
        let vec := vec
        (ZAvector_set vec VL (Zeros (n := VL)))
        (pure (vec +i vstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, ngrp : Nat, nvec : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nvec = 2 ∧ ngrp = 1 ∧ (is_VL VL) -/
def execute_ZERO_ZA2_RI_1 (VL : Nat) (ngrp : Nat) (nvec : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name ngrp)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let vec : Int := (vec -i (fmod_int vec nvec))
  let vec ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (ngrp -i 1)
    let mut loop_vars := vec
    for r in [loop_r_lower:loop_r_upper:1]i do
      let vec := loop_vars
      loop_vars ← do
        let vec := vec
        let loop_i_lower := 0
        let loop_i_upper := (nvec -i 1)
        let mut loop_vars_1 := ()
        for i in [loop_i_lower:loop_i_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do (ZAvector_set (vec +i i) VL (Zeros (n := VL)))
        (pure loop_vars_1)
        (pure (vec +i vstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, ngrp : Nat, nvec : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nvec = 2 ∧ ngrp = 2 ∧ (is_VL VL) -/
def execute_ZERO_ZA2_RI_2 (VL : Nat) (ngrp : Nat) (nvec : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name ngrp)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let vec : Int := (vec -i (fmod_int vec nvec))
  let vec ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (ngrp -i 1)
    let mut loop_vars := vec
    for r in [loop_r_lower:loop_r_upper:1]i do
      let vec := loop_vars
      loop_vars ← do
        let vec := vec
        let loop_i_lower := 0
        let loop_i_upper := (nvec -i 1)
        let mut loop_vars_1 := ()
        for i in [loop_i_lower:loop_i_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do (ZAvector_set (vec +i i) VL (Zeros (n := VL)))
        (pure loop_vars_1)
        (pure (vec +i vstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, ngrp : Nat, nvec : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nvec = 2 ∧ ngrp = 4 ∧ (is_VL VL) -/
def execute_ZERO_ZA2_RI_4 (VL : Nat) (ngrp : Nat) (nvec : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name ngrp)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let vec : Int := (vec -i (fmod_int vec nvec))
  let vec ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (ngrp -i 1)
    let mut loop_vars := vec
    for r in [loop_r_lower:loop_r_upper:1]i do
      let vec := loop_vars
      loop_vars ← do
        let vec := vec
        let loop_i_lower := 0
        let loop_i_upper := (nvec -i 1)
        let mut loop_vars_1 := ()
        for i in [loop_i_lower:loop_i_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do (ZAvector_set (vec +i i) VL (Zeros (n := VL)))
        (pure loop_vars_1)
        (pure (vec +i vstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, ngrp : Nat, nvec : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nvec = 4 ∧ ngrp = 1 ∧ (is_VL VL) -/
def execute_ZERO_ZA4_RI_1 (VL : Nat) (ngrp : Nat) (nvec : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name ngrp)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let vec : Int := (vec -i (fmod_int vec nvec))
  let vec ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (ngrp -i 1)
    let mut loop_vars := vec
    for r in [loop_r_lower:loop_r_upper:1]i do
      let vec := loop_vars
      loop_vars ← do
        let vec := vec
        let loop_i_lower := 0
        let loop_i_upper := (nvec -i 1)
        let mut loop_vars_1 := ()
        for i in [loop_i_lower:loop_i_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do (ZAvector_set (vec +i i) VL (Zeros (n := VL)))
        (pure loop_vars_1)
        (pure (vec +i vstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, ngrp : Nat, nvec : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nvec = 4 ∧ ngrp = 2 ∧ (is_VL VL) -/
def execute_ZERO_ZA4_RI_2 (VL : Nat) (ngrp : Nat) (nvec : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name ngrp)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let vec : Int := (vec -i (fmod_int vec nvec))
  let vec ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (ngrp -i 1)
    let mut loop_vars := vec
    for r in [loop_r_lower:loop_r_upper:1]i do
      let vec := loop_vars
      loop_vars ← do
        let vec := vec
        let loop_i_lower := 0
        let loop_i_upper := (nvec -i 1)
        let mut loop_vars_1 := ()
        for i in [loop_i_lower:loop_i_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do (ZAvector_set (vec +i i) VL (Zeros (n := VL)))
        (pure loop_vars_1)
        (pure (vec +i vstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, ngrp : Nat, nvec : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nvec = 4 ∧ ngrp = 4 ∧ (is_VL VL) -/
def execute_ZERO_ZA4_RI_4 (VL : Nat) (ngrp : Nat) (nvec : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name ngrp)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod ((BitVec.toNat vbase) +i offset) vstride)
  let vec : Int := (vec -i (fmod_int vec nvec))
  let vec ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (ngrp -i 1)
    let mut loop_vars := vec
    for r in [loop_r_lower:loop_r_upper:1]i do
      let vec := loop_vars
      loop_vars ← do
        let vec := vec
        let loop_i_lower := 0
        let loop_i_upper := (nvec -i 1)
        let mut loop_vars_1 := ()
        for i in [loop_i_lower:loop_i_upper:1]i do
          let () := loop_vars_1
          loop_vars_1 ← do (ZAvector_set (vec +i i) VL (Zeros (n := VL)))
        (pure loop_vars_1)
        (pure (vec +i vstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ isize = 2 ∧ List.elem imm [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ dstride = 8 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI2_MZ2_ZTZ_8 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let segments := (Int.ediv esize (isize *i nreg))
  let segment := (Nat.mod imm segments)
  let indexes ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := d
    for r in [loop_r_lower:loop_r_upper:1]i do
      let d := loop_vars
      loop_vars ← do
        let base := (((segment *i nreg) +i r) *i elements)
        let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let index ← do (pure (BitVec.toNat (← (Elem_read indexes (base +i e) isize))))
              sail_assert ((esize -i 1) <b 32) "src/instrs64_sme.sail:37205.46-37205.47"
              (Elem_set result e esize (Sail.BitVec.extractLsb (← (Elem_read table index 32)) (esize -i 1) 0))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        (Z_set d VL result)
        (pure (d +i dstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ isize = 4 ∧ List.elem imm [0, 1, 2, 3] ∧ List.elem esize [8, 16, 32, 64] ∧ dstride = 8 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI4_MZ2_ZTZ_8 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let segments := (Int.ediv esize (isize *i nreg))
  let segment := (Nat.mod imm segments)
  let indexes ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := d
    for r in [loop_r_lower:loop_r_upper:1]i do
      let d := loop_vars
      loop_vars ← do
        let base := (((segment *i nreg) +i r) *i elements)
        let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let index ← do (pure (BitVec.toNat (← (Elem_read indexes (base +i e) isize))))
              sail_assert ((esize -i 1) <b 32) "src/instrs64_sme.sail:37279.46-37279.47"
              (Elem_set result e esize (Sail.BitVec.extractLsb (← (Elem_read table index 32)) (esize -i 1) 0))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        (Z_set d VL result)
        (pure (d +i dstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ isize = 2 ∧ List.elem imm [0, 1, 2, 3] ∧ List.elem esize [8, 16, 32, 64] ∧ dstride = 4 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI2_MZ4_ZTZ_4 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let segments := (Int.ediv esize (isize *i nreg))
  let segment := (Nat.mod imm segments)
  let indexes ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := d
    for r in [loop_r_lower:loop_r_upper:1]i do
      let d := loop_vars
      loop_vars ← do
        let base := (((segment *i nreg) +i r) *i elements)
        let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let index ← do (pure (BitVec.toNat (← (Elem_read indexes (base +i e) isize))))
              sail_assert ((esize -i 1) <b 32) "src/instrs64_sme.sail:37353.46-37353.47"
              (Elem_set result e esize (Sail.BitVec.extractLsb (← (Elem_read table index 32)) (esize -i 1) 0))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        (Z_set d VL result)
        (pure (d +i dstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ isize = 4 ∧ List.elem imm [0, 1] ∧ List.elem esize [8, 16, 32, 64] ∧ dstride = 4 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI4_MZ4_ZTZ_4 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL := VL
  let elements := (Int.ediv VL esize)
  let segments := (Int.ediv esize (isize *i nreg))
  let segment := (fmod_int imm segments)
  let indexes ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := d
    for r in [loop_r_lower:loop_r_upper:1]i do
      let d := loop_vars
      loop_vars ← do
        let base := (((segment *i nreg) +i r) *i elements)
        let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
        let result ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars_1
            loop_vars_1 ← do
              let index ← do (pure (BitVec.toNat (← (Elem_read indexes (base +i e) isize))))
              sail_assert ((esize -i 1) <b 32) "src/instrs64_sme.sail:37427.46-37427.47"
              (Elem_set result e esize (Sail.BitVec.extractLsb (← (Elem_read table index 32)) (esize -i 1) 0))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        (Z_set d VL result)
        (pure (d +i dstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ n = 0 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_Z_RZA_B (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let operand ← (( do (ZAslice_read n esize vertical slice_name VL) ) : SailM (BitVec VL) )
  (ZAslice_set n esize vertical slice_name VL (Zeros (n := VL)))
  (Z_set d VL operand)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem n [0, 1] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_Z_RZA_H (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let operand ← (( do (ZAslice_read n esize vertical slice_name VL) ) : SailM (BitVec VL) )
  (ZAslice_set n esize vertical slice_name VL (Zeros (n := VL)))
  (Z_set d VL operand)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3] ∧ List.elem n [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_Z_RZA_W (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let operand ← (( do (ZAslice_read n esize vertical slice_name VL) ) : SailM (BitVec VL) )
  (ZAslice_set n esize vertical slice_name VL (Zeros (n := VL)))
  (Z_set d VL operand)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1] ∧ List.elem n [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_Z_RZA_D (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let operand ← (( do (ZAslice_read n esize vertical slice_name VL) ) : SailM (BitVec VL) )
  (ZAslice_set n esize vertical slice_name VL (Zeros (n := VL)))
  (Z_set d VL operand)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ offset = 0 ∧ 0 ≤ n ∧ n ≤ 15 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_Z_RZA_Q (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL esize)
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name := (Nat.mod ((BitVec.toNat index) +i offset) dim)
  let operand ← (( do (ZAslice_read n esize vertical slice_name VL) ) : SailM (BitVec VL) )
  (ZAslice_set n esize vertical slice_name VL (Zeros (n := VL)))
  (Z_set d VL operand)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 2 ∧ n = 0 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ2_ZA_B1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
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
      (ZAslice_set n esize vertical (slice_name +i r) VL (Zeros (n := VL)))
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ List.elem n [0, 1] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ2_ZA_H1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
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
      (ZAslice_set n esize vertical (slice_name +i r) VL (Zeros (n := VL)))
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3] ∧ nreg = 2 ∧ List.elem n [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ2_ZA_W1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
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
      (ZAslice_set n esize vertical (slice_name +i r) VL (Zeros (n := VL)))
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ offset = 0 ∧ nreg = 2 ∧ List.elem n [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ2_ZA_D1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
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
      (ZAslice_set n esize vertical (slice_name +i r) VL (Zeros (n := VL)))
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ nreg = 4 ∧ n = 0 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ4_ZA_B1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
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
      (ZAslice_set n esize vertical (slice_name +i r) VL (Zeros (n := VL)))
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ List.elem n [0, 1] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ4_ZA_H1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
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
      (ZAslice_set n esize vertical (slice_name +i r) VL (Zeros (n := VL)))
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ offset = 0 ∧ nreg = 4 ∧ List.elem n [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ4_ZA_W1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
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
      (ZAslice_set n esize vertical (slice_name +i r) VL (Zeros (n := VL)))
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical : Bool, 0 ≤ s ∧ s ≤ 31 ∧ offset = 0 ∧ nreg = 4 ∧ List.elem n [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ4_ZA_D1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
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
      (ZAslice_set n esize vertical (slice_name +i r) VL (Zeros (n := VL)))
      (Z_set (d +i r) VL result)
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, d : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ_ZA2_1 (VL : Nat) (d : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
        let vec := vec
        (ZAvector_set vec VL (Zeros (n := VL)))
        (Z_set (d +i r) VL result)
        (pure (vec +i vstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, d : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ_ZA4_1 (VL : Nat) (d : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
        let vec := vec
        (ZAvector_set vec VL (Zeros (n := VL)))
        (Z_set (d +i r) VL result)
        (pure (vec +i vstride))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 16 ∧ List.elem da [0, 1] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_FMOPA_ZA_PP_ZZ_16 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 16 ∧ List.elem da [0, 1] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_FMOPS_ZA_PP_ZZ_16 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_16 : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem da [0, 1] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_16 = (VL / 16 * (VL / 16 * 16)) -/
def execute_BFMOPA_ZA_PP_ZZ_16 (VL : Nat) (dim_dim_16 : Nat) (a : Nat) (b : Nat) (da : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL 16)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da 16 dim_dim_16) ) : SailM (BitVec dim_dim_16) )
  let result ← (( do (undefined_bitvector dim_dim_16) ) : SailM (BitVec dim_dim_16) )
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
            let element1 ← (( do (Elem_read operand1 row 16) ) : SailM (BitVec 16) )
            let element2 ← (( do (Elem_read operand2 col 16) ) : SailM (BitVec 16) )
            let element3 ← (( do (Elem_read operand3 ((row *i dim) +i col) 16) ) : SailM (BitVec 16) )
            if ((←((ActivePredicateElement mask1 row 16) <&&> (do
                 (ActivePredicateElement mask2 col 16)))) : Bool)
            then
              (do
                let element1 ← (( do
                  if (sub_op : Bool)
                  then (do (BFNeg element1))
                  else (pure element1) ) : SailM (BitVec 16) )
                (Elem_set result ((row *i dim) +i col) 16 (← (BFMulAdd_ZA element3 element1 element2 (← (FPCR_read ()))))))
            else (do (Elem_set result ((row *i dim) +i col) 16 element3))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec dim_dim_16) )
  (ZAtile_set VL da 16 dim_dim_16 result)

/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_16 : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem da [0, 1] ∧ List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_16 = (VL / 16 * (VL / 16 * 16)) -/
def execute_BFMOPS_ZA_PP_ZZ_16 (VL : Nat) (dim_dim_16 : Nat) (a : Nat) (b : Nat) (da : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let dim := (Int.ediv VL 16)
  let mask1 ← (( do (P_read a PL) ) : SailM (BitVec PL) )
  let mask2 ← (( do (P_read b PL) ) : SailM (BitVec PL) )
  let operand1 ← (( do (Z_read n VL) ) : SailM (BitVec VL) )
  let operand2 ← (( do (Z_read m VL) ) : SailM (BitVec VL) )
  let operand3 ← (( do (ZAtile_read VL da 16 dim_dim_16) ) : SailM (BitVec dim_dim_16) )
  let result ← (( do (undefined_bitvector dim_dim_16) ) : SailM (BitVec dim_dim_16) )
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
            let element1 ← (( do (Elem_read operand1 row 16) ) : SailM (BitVec 16) )
            let element2 ← (( do (Elem_read operand2 col 16) ) : SailM (BitVec 16) )
            let element3 ← (( do (Elem_read operand3 ((row *i dim) +i col) 16) ) : SailM (BitVec 16) )
            if ((←((ActivePredicateElement mask1 row 16) <&&> (do
                 (ActivePredicateElement mask2 col 16)))) : Bool)
            then
              (do
                let element1 ← (( do
                  if (sub_op : Bool)
                  then (do (BFNeg element1))
                  else (pure element1) ) : SailM (BitVec 16) )
                (Elem_set result ((row *i dim) +i col) 16 (← (BFMulAdd_ZA element3 element1 element2 (← (FPCR_read ()))))))
            else (do (Elem_set result ((row *i dim) +i col) 16 element3))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (BitVec dim_dim_16) )
  (ZAtile_set VL da 16 dim_dim_16 result)

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_FADD_ZA_ZW_2x2_16 (VL : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_FSUB_ZA_ZW_2x2_16 (VL : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFADD_ZA_ZW_2x2_16 (VL : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              (Elem_set result e 16 (← (BFAdd_ZA element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFSUB_ZA_ZW_2x2_16 (VL : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              (Elem_set result e 16 (← (BFSub_ZA element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_FADD_ZA_ZW_4x4_16 (VL : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_FSUB_ZA_ZW_4x4_16 (VL : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFADD_ZA_ZW_4x4_16 (VL : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              (Elem_set result e 16 (← (BFAdd_ZA element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFSUB_ZA_ZW_4x4_16 (VL : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              (Elem_set result e 16 (← (BFSub_ZA element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZW_2x2_16 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZW_2x2_16 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLA_ZA_ZZW_2x2_16 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (BFNeg element1))
                else (pure element1) ) : SailM (BitVec 16) )
              (Elem_set result e 16 (← (BFMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLS_ZA_ZZW_2x2_16 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (BFNeg element1))
                else (pure element1) ) : SailM (BitVec 16) )
              (Elem_set result e 16 (← (BFMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZV_2x1_16 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZV_2x1_16 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLA_ZA_ZZV_2x1_16 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (BFNeg element1))
                else (pure element1) ) : SailM (BitVec 16) )
              (Elem_set result e 16 (← (BFMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLS_ZA_ZZV_2x1_16 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (BFNeg element1))
                else (pure element1) ) : SailM (BitVec 16) )
              (Elem_set result e 16 (← (BFMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZW_4x4_16 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZW_4x4_16 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLA_ZA_ZZW_4x4_16 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (BFNeg element1))
                else (pure element1) ) : SailM (BitVec 16) )
              (Elem_set result e 16 (← (BFMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLS_ZA_ZZW_4x4_16 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (BFNeg element1))
                else (pure element1) ) : SailM (BitVec 16) )
              (Elem_set result e 16 (← (BFMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZV_4x1_16 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZV_4x1_16 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLA_ZA_ZZV_4x1_16 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (BFNeg element1))
                else (pure element1) ) : SailM (BitVec 16) )
              (Elem_set result e 16 (← (BFMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLS_ZA_ZZV_4x1_16 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
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
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (BFNeg element1))
                else (pure element1) ) : SailM (BitVec 16) )
              (Elem_set result e 16 (← (BFMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZi_H2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZi_H2xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_BFMLA_ZA_ZZi_H2xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 16)
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
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
              let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (BFNeg element1))
                else (pure element1) ) : SailM (BitVec 16) )
              (Elem_set result e 16 (← (BFMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_BFMLS_ZA_ZZi_H2xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 16)
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
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
              let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (BFNeg element1))
                else (pure element1) ) : SailM (BitVec 16) )
              (Elem_set result e 16 (← (BFMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZi_H4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZi_H4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_BFMLA_ZA_ZZi_H4xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 16)
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
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
              let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (BFNeg element1))
                else (pure element1) ) : SailM (BitVec 16) )
              (Elem_set result e 16 (← (BFMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0 ≤ v ∧ v ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_BFMLS_ZA_ZZi_H4xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 16)
  let vectors_name := (Int.ediv VL 8)
  let vstride := (Int.ediv vectors_name nreg)
  let eltspersegment := (Int.ediv 128 16)
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
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let segmentbase := (e -i (Nat.mod e eltspersegment))
              let s := (segmentbase +i index)
              let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
              let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
              let element1 ← (( do
                if (sub_op : Bool)
                then (do (BFNeg element1))
                else (pure element1) ) : SailM (BitVec 16) )
              (Elem_set result e 16 (← (BFMulAdd_ZA element3 element1 element2 (← (FPCR_read ())))))
          (pure loop_vars_1) ) : SailM (BitVec VL) )
        let vec := vec
        (ZAvector_set vec VL result)
        let vec : Int := (vec +i vstride)
        (pure (result, vec))
    (pure loop_vars) ) : SailM ((BitVec VL) × Int) )
  (pure ())

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMAX_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 16 (← (BFMax element1 element2 (← (FPCR_read ()))))))))
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
def execute_BFMAX_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 16 (← (BFMax element1 element2 (← (FPCR_read ()))))))))
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
def execute_BFMIN_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, nreg : Nat, nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMIN_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, nreg : Nat, nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMAX_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 16 (← (BFMax element1 element2 (← (FPCR_read ()))))))))
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
def execute_BFMAX_MZ_ZZV_4x1 (VL : Nat) (dn : Nat) (m : Nat) (nreg : Nat) : SailM Unit := do
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
            (pure (vectorUpdate results r (← (Elem_set (GetElem?.getElem! results r) e 16 (← (BFMax element1 element2 (← (FPCR_read ()))))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (dn +i r) VL (GetElem?.getElem! results r))
  (pure loop_vars_2)


