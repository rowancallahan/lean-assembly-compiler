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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 1 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1H_Z_P_BZ_S_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:58968.24-58968.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 1 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1SH_Z_P_BZ_S_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:59085.24-59085.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 2 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1W_Z_P_BZ_S_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 2 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1W_Z_P_BZ_S_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:59295.24-59295.25"
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

/-- Type quantifiers: VL : Nat, imm : Int, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 ∧ (is_VL VL) -/
def execute_LDR_P_BI__ (VL : Nat) (imm : Int) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv PL 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset : Int := (imm *i elements)
  let result ← (( do (undefined_bitvector PL) ) : SailM (BitVec PL) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let aligned : Bool := (IsAligned__1 (BitVec.addInt base offset) 2)
  if ((←((pure (! aligned)) <&&> (do
       (AlignmentEnforced ())))) : Bool)
  then (AArch64_Abort (BitVec.addInt base offset) (← (AlignmentFault accdesc)))
  else (pure ())
  let (offset, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (offset, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (offset, result) := loop_vars
      loop_vars ← do
        let result ← (( do
          let offset := offset
          (Elem_set result e 8 (← (AArch64_MemSingle_read (BitVec.addInt base offset) 1 accdesc aligned))) ) : SailM (BitVec PL) )
        let offset : Int := (offset +i 1)
        (pure (offset, result))
    (pure loop_vars) ) : SailM (Int × (BitVec PL)) )
  (P_set t PL result)

/-- Type quantifiers: VL : Nat, imm : Int, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ (is_VL VL) -/
def execute_LDR_Z_BI__ (VL : Nat) (imm : Int) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset : Int := (imm *i elements)
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let aligned : Bool := (IsAligned__1 (BitVec.addInt base offset) 16)
  if ((←((pure (! aligned)) <&&> (do
       (AlignmentEnforced ())))) : Bool)
  then (AArch64_Abort (BitVec.addInt base offset) (← (AlignmentFault accdesc)))
  else (pure ())
  let (offset, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (offset, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (offset, result) := loop_vars
      loop_vars ← do
        let result ← (( do
          let offset := offset
          (Elem_set result e 8 (← (AArch64_MemSingle_read (BitVec.addInt base offset) 1 accdesc aligned))) ) : SailM (BitVec VL) )
        let offset : Int := (offset +i 1)
        (pure (offset, result))
    (pure loop_vars) ) : SailM (Int × (BitVec VL)) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Int, scale : Nat, k_stream : Bool, scale = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_PRFB_I_P_BI_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Int) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64))
    else (pure base) ) : SailM (BitVec 64) )
  let base := base
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (let eoff := ((offset *i elements) +i e)
        let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl eoff scale))
        (pure (Hint_Prefetch addr pref_hint level stream)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Int, scale : Nat, k_stream : Bool, scale = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_PRFH_I_P_BI_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Int) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64))
    else (pure base) ) : SailM (BitVec 64) )
  let base := base
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (let eoff := ((offset *i elements) +i e)
        let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl eoff scale))
        (pure (Hint_Prefetch addr pref_hint level stream)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Int, scale : Nat, k_stream : Bool, scale = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFW_I_P_BI_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Int) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64))
    else (pure base) ) : SailM (BitVec 64) )
  let base := base
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (let eoff := ((offset *i elements) +i e)
        let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl eoff scale))
        (pure (Hint_Prefetch addr pref_hint level stream)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Int, scale : Nat, k_stream : Bool, scale = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_PRFD_I_P_BI_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Int) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        if ((n == 31) : Bool)
        then (SP_read ())
        else (X_read n 64))
    else (pure base) ) : SailM (BitVec 64) )
  let base := base
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (let eoff := ((offset *i elements) +i e)
        let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl eoff scale))
        (pure (Hint_Prefetch addr pref_hint level stream)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, scale : Nat, k_stream : Bool, scale = 0 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_PRFB_I_P_BR_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec 64) × (BitVec 64)) )
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
        (let eoff := ((BitVec.toNat offset) +i e)
        let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl eoff scale))
        (pure (Hint_Prefetch addr pref_hint level stream)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, scale : Nat, k_stream : Bool, scale = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_PRFH_I_P_BR_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec 64) × (BitVec 64)) )
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
        (let eoff := ((BitVec.toNat offset) +i e)
        let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl eoff scale))
        (pure (Hint_Prefetch addr pref_hint level stream)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, scale : Nat, k_stream : Bool, scale = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFW_I_P_BR_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec 64) × (BitVec 64)) )
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
        (let eoff := ((BitVec.toNat offset) +i e)
        let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl eoff scale))
        (pure (Hint_Prefetch addr pref_hint level stream)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, scale : Nat, k_stream : Bool, scale = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_PRFD_I_P_BR_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec 64) × (BitVec 64)) )
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
        (let eoff := ((BitVec.toNat offset) +i e)
        let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl eoff scale))
        (pure (Hint_Prefetch addr pref_hint level stream)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Nat, scale : Nat, k_stream : Bool, scale = 0 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFB_I_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Nat) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (do (Z_read n VL))
    else (pure base) ) : SailM (BitVec VL) )
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
          let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (Int.shiftl offset scale))) ) : SailM (BitVec 64) )
          (pure (Hint_Prefetch addr pref_hint level stream)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Nat, scale : Nat, k_stream : Bool, scale = 1 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFH_I_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Nat) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (do (Z_read n VL))
    else (pure base) ) : SailM (BitVec VL) )
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
          let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (Int.shiftl offset scale))) ) : SailM (BitVec 64) )
          (pure (Hint_Prefetch addr pref_hint level stream)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Nat, scale : Nat, k_stream : Bool, scale = 2 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFW_I_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Nat) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (do (Z_read n VL))
    else (pure base) ) : SailM (BitVec VL) )
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
          let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (Int.shiftl offset scale))) ) : SailM (BitVec 64) )
          (pure (Hint_Prefetch addr pref_hint level stream)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Nat, scale : Nat, k_stream : Bool, scale = 3 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFD_I_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Nat) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (do (Z_read n VL))
    else (pure base) ) : SailM (BitVec VL) )
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
          let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (Int.shiftl offset scale))) ) : SailM (BitVec 64) )
          (pure (Hint_Prefetch addr pref_hint level stream)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1B_Z_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (do (Z_read n VL))
    else (pure base) ) : SailM (BitVec VL) )
  let base := base
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
              let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1SB_Z_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (do (Z_read n VL))
    else (pure base) ) : SailM (BitVec VL) )
  let base := base
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
              let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1B_Z_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
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
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (do (Z_read n VL))
    else (pure base) ) : SailM (BitVec VL) )
  let base := base
  sail_assert accdesc.first "src/instrs64_sve.sail:60585.24-60585.25"
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
              let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1SB_Z_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
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
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (do (Z_read n VL))
    else (pure base) ) : SailM (BitVec VL) )
  let base := base
  sail_assert accdesc.first "src/instrs64_sve.sail:60689.24-60689.25"
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
              let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1H_Z_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (do (Z_read n VL))
    else (pure base) ) : SailM (BitVec VL) )
  let base := base
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
              let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1SH_Z_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (do (Z_read n VL))
    else (pure base) ) : SailM (BitVec VL) )
  let base := base
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
              let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1H_Z_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
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
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (do (Z_read n VL))
    else (pure base) ) : SailM (BitVec VL) )
  let base := base
  sail_assert accdesc.first "src/instrs64_sve.sail:60953.24-60953.25"
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
              let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1SH_Z_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
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
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (do (Z_read n VL))
    else (pure base) ) : SailM (BitVec VL) )
  let base := base
  sail_assert accdesc.first "src/instrs64_sve.sail:61057.24-61057.25"
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
              let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1W_Z_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (do (Z_read n VL))
    else (pure base) ) : SailM (BitVec VL) )
  let base := base
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
              let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1W_Z_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
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
  let base ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then (do (Z_read n VL))
    else (pure base) ) : SailM (BitVec VL) )
  let base := base
  sail_assert accdesc.first "src/instrs64_sve.sail:61241.24-61241.25"
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
              let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1RB_Z_P_BI_U8 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure data))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ← (( do
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64) ) : SailM (BitVec 64) )
        let addr : (BitVec 64) := (BitVec.addInt base (offset *i mbytes))
        (Mem_read addr mbytes accdesc)) ) : SailM (BitVec msize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1RB_Z_P_BI_U16 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure data))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ← (( do
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64) ) : SailM (BitVec 64) )
        let addr : (BitVec 64) := (BitVec.addInt base (offset *i mbytes))
        (Mem_read addr mbytes accdesc)) ) : SailM (BitVec msize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1RB_Z_P_BI_U32 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure data))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ← (( do
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64) ) : SailM (BitVec 64) )
        let addr : (BitVec 64) := (BitVec.addInt base (offset *i mbytes))
        (Mem_read addr mbytes accdesc)) ) : SailM (BitVec msize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1RB_Z_P_BI_U64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure data))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ← (( do
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64) ) : SailM (BitVec 64) )
        let addr : (BitVec 64) := (BitVec.addInt base (offset *i mbytes))
        (Mem_read addr mbytes accdesc)) ) : SailM (BitVec msize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1RSW_Z_P_BI_S64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure data))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ← (( do
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64) ) : SailM (BitVec 64) )
        let addr : (BitVec 64) := (BitVec.addInt base (offset *i mbytes))
        (Mem_read addr mbytes accdesc)) ) : SailM (BitVec msize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1RH_Z_P_BI_U16 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure data))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ← (( do
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64) ) : SailM (BitVec 64) )
        let addr : (BitVec 64) := (BitVec.addInt base (offset *i mbytes))
        (Mem_read addr mbytes accdesc)) ) : SailM (BitVec msize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1RH_Z_P_BI_U32 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure data))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ← (( do
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64) ) : SailM (BitVec 64) )
        let addr : (BitVec 64) := (BitVec.addInt base (offset *i mbytes))
        (Mem_read addr mbytes accdesc)) ) : SailM (BitVec msize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1RH_Z_P_BI_U64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure data))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ← (( do
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64) ) : SailM (BitVec 64) )
        let addr : (BitVec 64) := (BitVec.addInt base (offset *i mbytes))
        (Mem_read addr mbytes accdesc)) ) : SailM (BitVec msize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1RSH_Z_P_BI_S64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure data))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ← (( do
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64) ) : SailM (BitVec 64) )
        let addr : (BitVec 64) := (BitVec.addInt base (offset *i mbytes))
        (Mem_read addr mbytes accdesc)) ) : SailM (BitVec msize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1RSH_Z_P_BI_S32 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure data))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ← (( do
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64) ) : SailM (BitVec 64) )
        let addr : (BitVec 64) := (BitVec.addInt base (offset *i mbytes))
        (Mem_read addr mbytes accdesc)) ) : SailM (BitVec msize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1RW_Z_P_BI_U32 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure data))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ← (( do
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64) ) : SailM (BitVec 64) )
        let addr : (BitVec 64) := (BitVec.addInt base (offset *i mbytes))
        (Mem_read addr mbytes accdesc)) ) : SailM (BitVec msize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1RW_Z_P_BI_U64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure data))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ← (( do
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64) ) : SailM (BitVec 64) )
        let addr : (BitVec 64) := (BitVec.addInt base (offset *i mbytes))
        (Mem_read addr mbytes accdesc)) ) : SailM (BitVec msize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1RSB_Z_P_BI_S64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure data))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ← (( do
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64) ) : SailM (BitVec 64) )
        let addr : (BitVec 64) := (BitVec.addInt base (offset *i mbytes))
        (Mem_read addr mbytes accdesc)) ) : SailM (BitVec msize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1RSB_Z_P_BI_S32 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure data))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ← (( do
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64) ) : SailM (BitVec 64) )
        let addr : (BitVec 64) := (BitVec.addInt base (offset *i mbytes))
        (Mem_read addr mbytes accdesc)) ) : SailM (BitVec msize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1RSB_Z_P_BI_S16 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure data))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ← (( do
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64) ) : SailM (BitVec 64) )
        let addr : (BitVec 64) := (BitVec.addInt base (offset *i mbytes))
        (Mem_read addr mbytes accdesc)) ) : SailM (BitVec msize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1RD_Z_P_BI_U64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure data))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ← (( do
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64) ) : SailM (BitVec 64) )
        let addr : (BitVec 64) := (BitVec.addInt base (offset *i mbytes))
        (Mem_read addr mbytes accdesc)) ) : SailM (BitVec msize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e esize)) : Bool)
        then (do (Elem_set result e esize (← (Extend data esize is_unsigned))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1B_Z_P_BR_U8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1B_Z_P_BR_U16 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1B_Z_P_BR_U32 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1B_Z_P_BR_U64 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SW_Z_P_BR_S64 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1H_Z_P_BR_U16 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1H_Z_P_BR_U32 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1H_Z_P_BR_U64 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SH_Z_P_BR_S64 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1SH_Z_P_BR_S32 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1W_Z_P_BR_U32 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1W_Z_P_BR_U64 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SB_Z_P_BR_S64 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1SB_Z_P_BR_S32 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1SB_Z_P_BR_S16 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_Z_P_BR_U64 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_LD1W_Z_P_BR_U128 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_LD1D_Z_P_BR_U128 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LDFF1B_Z_P_BR_U8 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:64370.24-64370.25"
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDFF1B_Z_P_BR_U16 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:64481.24-64481.25"
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1B_Z_P_BR_U32 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:64592.24-64592.25"
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1B_Z_P_BR_U64 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:64703.24-64703.25"
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SW_Z_P_BR_S64 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:64814.24-64814.25"
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDFF1H_Z_P_BR_U16 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:64925.24-64925.25"
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1H_Z_P_BR_U32 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:65036.24-65036.25"
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1H_Z_P_BR_U64 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:65147.24-65147.25"
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SH_Z_P_BR_S64 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:65258.24-65258.25"
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1SH_Z_P_BR_S32 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:65369.24-65369.25"
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1W_Z_P_BR_U32 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:65480.24-65480.25"
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1W_Z_P_BR_U64 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:65591.24-65591.25"
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SB_Z_P_BR_S64 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:65702.24-65702.25"
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDFF1SB_Z_P_BR_S32 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:65813.24-65813.25"
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDFF1SB_Z_P_BR_S16 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:65924.24-65924.25"
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1D_Z_P_BR_U64 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
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
        let offset ← (X_read m 64)
        (pure (base, offset))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  sail_assert accdesc.first "src/instrs64_sve.sail:66035.24-66035.25"
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
              let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LDNT1B_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv esize 8)
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
            let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDNT1H_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv esize 8)
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
            let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNT1W_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv esize 8)
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
            let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNT1D_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv esize 8)
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
            let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD2B_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 2 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 2) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD2H_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 2 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 2) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD2W_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 2 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 2) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD2D_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 2 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 2) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD3B_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 3 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 3) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD3H_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 3 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 3) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD3W_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 3 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 3) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD3D_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 3 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 3) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD4B_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD4H_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD4W_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD4D_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_LD2Q_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 2 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 2) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_LD3Q_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 3 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 3) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_LD4Q_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1RQB_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv 128 esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let mbytes := (Int.ediv esize 8)
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
            let eoff := ((BitVec.toNat offset) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec 128) )
  (Z_set t VL (BitVec.replicateBits result (Int.ediv VL 128)))

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1RQH_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv 128 esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let mbytes := (Int.ediv esize 8)
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
            let eoff := ((BitVec.toNat offset) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec 128) )
  (Z_set t VL (BitVec.replicateBits result (Int.ediv VL 128)))

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1RQW_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv 128 esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let mbytes := (Int.ediv esize 8)
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
            let eoff := ((BitVec.toNat offset) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec 128) )
  (Z_set t VL (BitVec.replicateBits result (Int.ediv VL 128)))

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1RQD_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv 128 esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let mbytes := (Int.ediv esize 8)
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
            let eoff := ((BitVec.toNat offset) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec 128) )
  (Z_set t VL (BitVec.replicateBits result (Int.ediv VL 128)))

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1ROB_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  if ((VL <b 256) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let elements := (Int.ediv 256 esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 256) ) : SailM (BitVec 256) )
  let mbytes := (Int.ediv esize 8)
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
            let eoff := ((BitVec.toNat offset) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec 256) )
  (Z_set t VL (Sail.BitVec.zeroExtend (BitVec.replicateBits result (Int.ediv VL 256)) VL))

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1ROH_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  if ((VL <b 256) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let elements := (Int.ediv 256 esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 256) ) : SailM (BitVec 256) )
  let mbytes := (Int.ediv esize 8)
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
            let eoff := ((BitVec.toNat offset) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec 256) )
  (Z_set t VL (Sail.BitVec.zeroExtend (BitVec.replicateBits result (Int.ediv VL 256)) VL))

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1ROW_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  if ((VL <b 256) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let elements := (Int.ediv 256 esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 256) ) : SailM (BitVec 256) )
  let mbytes := (Int.ediv esize 8)
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
            let eoff := ((BitVec.toNat offset) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec 256) )
  (Z_set t VL (Sail.BitVec.zeroExtend (BitVec.replicateBits result (Int.ediv VL 256)) VL))

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1ROD_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  if ((VL <b 256) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let elements := (Int.ediv 256 esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector 256) ) : SailM (BitVec 256) )
  let mbytes := (Int.ediv esize 8)
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
            let eoff := ((BitVec.toNat offset) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec 256) )
  (Z_set t VL (Sail.BitVec.zeroExtend (BitVec.replicateBits result (Int.ediv VL 256)) VL))

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1B_Z_P_BI_U8 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1B_Z_P_BI_U16 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1B_Z_P_BI_U32 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1B_Z_P_BI_U64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SW_Z_P_BI_S64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1H_Z_P_BI_U16 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1H_Z_P_BI_U32 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1H_Z_P_BI_U64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SH_Z_P_BI_S64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1SH_Z_P_BI_S32 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1W_Z_P_BI_U32 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1W_Z_P_BI_U64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SB_Z_P_BI_S64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1SB_Z_P_BI_S32 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1SB_Z_P_BI_S16 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_Z_P_BI_U64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LDNF1B_Z_P_BI_U8 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure (data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (data, fault))) ) : SailM ((BitVec msize) × Bool) )
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
        (pure (data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDNF1B_Z_P_BI_U16 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure (data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (data, fault))) ) : SailM ((BitVec msize) × Bool) )
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
        (pure (data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNF1B_Z_P_BI_U32 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure (data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (data, fault))) ) : SailM ((BitVec msize) × Bool) )
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
        (pure (data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNF1B_Z_P_BI_U64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure (data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (data, fault))) ) : SailM ((BitVec msize) × Bool) )
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
        (pure (data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNF1SW_Z_P_BI_S64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure (data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (data, fault))) ) : SailM ((BitVec msize) × Bool) )
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
        (pure (data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDNF1H_Z_P_BI_U16 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure (data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (data, fault))) ) : SailM ((BitVec msize) × Bool) )
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
        (pure (data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNF1H_Z_P_BI_U32 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure (data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (data, fault))) ) : SailM ((BitVec msize) × Bool) )
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
        (pure (data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNF1H_Z_P_BI_U64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure (data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (data, fault))) ) : SailM ((BitVec msize) × Bool) )
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
        (pure (data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNF1SH_Z_P_BI_S64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure (data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (data, fault))) ) : SailM ((BitVec msize) × Bool) )
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
        (pure (data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNF1SH_Z_P_BI_S32 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure (data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (data, fault))) ) : SailM ((BitVec msize) × Bool) )
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
        (pure (data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNF1W_Z_P_BI_U32 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure (data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (data, fault))) ) : SailM ((BitVec msize) × Bool) )
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
        (pure (data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNF1W_Z_P_BI_U64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure (data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (data, fault))) ) : SailM ((BitVec msize) × Bool) )
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
        (pure (data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNF1SB_Z_P_BI_S64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure (data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (data, fault))) ) : SailM ((BitVec msize) × Bool) )
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
        (pure (data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNF1SB_Z_P_BI_S32 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure (data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (data, fault))) ) : SailM ((BitVec msize) × Bool) )
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
        (pure (data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDNF1SB_Z_P_BI_S16 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure (data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (data, fault))) ) : SailM ((BitVec msize) × Bool) )
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
        (pure (data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNF1D_Z_P_BI_U64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let orig ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (data, fault, faulted, result, unknown)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (data, fault, faulted, result, unknown) := loop_vars
      loop_vars ← do
        let (data, fault) ← (( do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let (tup__0, tup__1) ← do (MemNF_read addr mbytes accdesc)
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure (data, fault)))
          else
            (let (tup__0, tup__1) := (((Zeros (n := msize)), false) : ((BitVec msize) × Bool))
            let data : (BitVec msize) := tup__0
            let fault : Bool := tup__1
            (pure (data, fault))) ) : SailM ((BitVec msize) × Bool) )
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
        (pure (data, fault, faulted, result, unknown))
    (pure loop_vars) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_LD1W_Z_P_BI_U128 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_LD1D_Z_P_BI_U128 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
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
              let eoff := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LDNT1B_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv esize 8)
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
            let eoff := ((offset *i elements) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDNT1H_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv esize 8)
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
            let eoff := ((offset *i elements) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNT1W_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv esize 8)
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
            let eoff := ((offset *i elements) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNT1D_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv esize 8)
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
            let eoff := ((offset *i elements) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD2B_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 2 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 2) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD2H_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 2 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 2) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD2W_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 2 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 2) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD2D_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 2 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 2) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD3B_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 3 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 3) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD3H_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 3 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 3) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD3W_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 3 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 3) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD3D_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 3 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 3) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD4B_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD4H_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD4W_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD4D_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_LD2Q_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 2 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 2) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_LD3Q_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
  let values_name ← (( do (undefined_vector 3 (← (undefined_bitvector VL))) ) : SailM (Vector (BitVec VL) 3) )
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_LD4Q_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
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
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := values_name
    for e in [loop_e_lower:loop_e_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do
        let loop_r_lower := 0
        let loop_r_upper := (nreg -i 1)
        let mut loop_vars_1 := values_name
        for r in [loop_r_lower:loop_r_upper:1]i do
          let values_name := loop_vars_1
          loop_vars_1 ← do
            if ((← (ActivePredicateElement mask e esize)) : Bool)
            then
              (do
                let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (← (Mem_read addr mbytes accdesc)))))))
            else (do (pure (vectorUpdate values_name r (← (Elem_set (GetElem?.getElem! values_name r) e esize (Zeros (n := esize)))))))
        (pure loop_vars_1)
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (Nat.mod (t +i r) 32) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1RQB_Z_P_BI_U8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv 128 esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let mbytes := (Int.ediv esize 8)
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
            let addr : (BitVec 64) := (BitVec.addInt (BitVec.addInt base (offset *i 16)) (e *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec 128) )
  (Z_set t VL (BitVec.replicateBits result (Int.ediv VL 128)))

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1RQH_Z_P_BI_U16 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv 128 esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let mbytes := (Int.ediv esize 8)
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
            let addr : (BitVec 64) := (BitVec.addInt (BitVec.addInt base (offset *i 16)) (e *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec 128) )
  (Z_set t VL (BitVec.replicateBits result (Int.ediv VL 128)))

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1RQW_Z_P_BI_U32 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv 128 esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let mbytes := (Int.ediv esize 8)
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
            let addr : (BitVec 64) := (BitVec.addInt (BitVec.addInt base (offset *i 16)) (e *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec 128) )
  (Z_set t VL (BitVec.replicateBits result (Int.ediv VL 128)))

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1RQD_Z_P_BI_U64 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv 128 esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let mbytes := (Int.ediv esize 8)
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
            let addr : (BitVec 64) := (BitVec.addInt (BitVec.addInt base (offset *i 16)) (e *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec 128) )
  (Z_set t VL (BitVec.replicateBits result (Int.ediv VL 128)))

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1ROB_Z_P_BI_U8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  if ((VL <b 256) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let elements := (Int.ediv 256 esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector 256) ) : SailM (BitVec 256) )
  let mbytes := (Int.ediv esize 8)
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
            let eoff := ((offset *i elements) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec 256) )
  (Z_set t VL (Sail.BitVec.zeroExtend (BitVec.replicateBits result (Int.ediv VL 256)) VL))

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1ROH_Z_P_BI_U16 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  if ((VL <b 256) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let elements := (Int.ediv 256 esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector 256) ) : SailM (BitVec 256) )
  let mbytes := (Int.ediv esize 8)
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
            let eoff := ((offset *i elements) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec 256) )
  (Z_set t VL (Sail.BitVec.zeroExtend (BitVec.replicateBits result (Int.ediv VL 256)) VL))

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1ROW_Z_P_BI_U32 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  if ((VL <b 256) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let elements := (Int.ediv 256 esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector 256) ) : SailM (BitVec 256) )
  let mbytes := (Int.ediv esize 8)
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
            let eoff := ((offset *i elements) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec 256) )
  (Z_set t VL (Sail.BitVec.zeroExtend (BitVec.replicateBits result (Int.ediv VL 256)) VL))

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1ROD_Z_P_BI_U64 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  if ((VL <b 256) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let elements := (Int.ediv 256 esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let result ← (( do (undefined_bitvector 256) ) : SailM (BitVec 256) )
  let mbytes := (Int.ediv esize 8)
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
            let eoff := ((offset *i elements) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            (Elem_set result e esize (← (Mem_read addr mbytes accdesc))))
        else (do (Elem_set result e esize (Zeros (n := esize))))
    (pure loop_vars) ) : SailM (BitVec 256) )
  (Z_set t VL (Sail.BitVec.zeroExtend (BitVec.replicateBits result (Int.ediv VL 256)) VL))

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1B_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SB_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1B_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:74311.24-74311.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SB_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:74429.24-74429.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1H_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SH_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1H_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:74735.24-74735.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SH_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:74853.24-74853.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1W_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SW_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1W_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:75159.24-75159.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SW_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:75277.24-75277.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1D_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:75489.24-75489.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, k_stream : Bool, scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_PRFB_I_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, k_stream : Bool, scale = 1 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_PRFH_I_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, k_stream : Bool, scale = 2 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_PRFW_I_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, k_stream : Bool, scale = 3 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_PRFD_I_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 1 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1H_Z_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 1 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SH_Z_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 1 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1H_Z_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:76101.24-76101.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 1 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SH_Z_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:76218.24-76218.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 2 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1W_Z_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 2 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SW_Z_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 2 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1W_Z_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:76521.24-76521.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 2 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SW_Z_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:76638.24-76638.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 3 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_Z_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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


