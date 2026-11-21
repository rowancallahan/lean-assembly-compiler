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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 3 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1D_Z_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:76848.24-76848.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Nat, scale : Nat, k_stream : Bool, scale = 0 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_PRFB_I_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Nat) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Nat, scale : Nat, k_stream : Bool, scale = 1 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_PRFH_I_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Nat) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Nat, scale : Nat, k_stream : Bool, scale = 2 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_PRFW_I_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Nat) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, n : Nat, offset : Nat, scale : Nat, k_stream : Bool, scale = 3 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_PRFD_I_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (n : Nat) (offset : Nat) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1B_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SB_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1B_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:77396.24-77396.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SB_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:77500.24-77500.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1H_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SH_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1H_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:77764.24-77764.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SH_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:77868.24-77868.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1W_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SW_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1W_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:78132.24-78132.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SW_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:78236.24-78236.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1D_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:78420.24-78420.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1B_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SB_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1B_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:78719.24-78719.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SB_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:78836.24-78836.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1H_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SH_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1H_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:79139.24-79139.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SH_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:79256.24-79256.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1W_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SW_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1W_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:79559.24-79559.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SW_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:79676.24-79676.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1D_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:79886.24-79886.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, k_stream : Bool, scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_PRFB_I_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, k_stream : Bool, scale = 1 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_PRFH_I_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, k_stream : Bool, scale = 2 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_PRFW_I_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, k_stream : Bool, scale = 3 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem level [0, 1, 2, 3] ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_PRFD_I_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 1 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1H_Z_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 1 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SH_Z_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 1 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1H_Z_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:80491.24-80491.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 1 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SH_Z_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:80607.24-80607.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 2 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1W_Z_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 2 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SW_Z_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 2 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1W_Z_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:80907.24-80907.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 2 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SW_Z_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:81023.24-81023.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 3 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_Z_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 3 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1D_Z_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
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
  sail_assert accdesc.first "src/instrs64_sve.sail:81231.24-81231.25"
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ (is_VL VL) -/
def execute_ST1B_Z_P_BR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ (is_VL VL) -/
def execute_ST1H_Z_P_BR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
          sail_assert ((0 ≤b (msize -i 1)) && ((msize -i 1) <b esize)) "src/instrs64_sve.sail:81433.70-81433.71"
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_ST1W_Z_P_BR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_Z_P_BR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_ST1W_Z_P_BR_U128 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_ST1D_Z_P_BR_U128 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, imm : Int, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 ∧ (is_VL VL) -/
def execute_STR_P_BI__ (VL : Nat) (imm : Int) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv PL 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset : Int := (imm *i elements)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let src ← (( do (P_read t PL) ) : SailM (BitVec PL) )
  let aligned : Bool := (IsAligned__1 (BitVec.addInt base offset) 2)
  if ((←((pure (! aligned)) <&&> (do
       (AlignmentEnforced ())))) : Bool)
  then (AArch64_Abort (BitVec.addInt base offset) (← (AlignmentFault accdesc)))
  else (pure ())
  let offset ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := offset
    for e in [loop_e_lower:loop_e_upper:1]i do
      let offset := loop_vars
      loop_vars ← do
        let offset := offset
        (AArch64_MemSingle_set (BitVec.addInt base offset) 1 accdesc aligned (← (Elem_read src e 8)))
        (pure (offset +i 1))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, imm : Int, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ (is_VL VL) -/
def execute_STR_Z_BI__ (VL : Nat) (imm : Int) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let elements := (Int.ediv VL 8)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset : Int := (imm *i elements)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let src ← (( do (Z_read t VL) ) : SailM (BitVec VL) )
  let aligned : Bool := (IsAligned__1 (BitVec.addInt base offset) 16)
  if ((←((pure (! aligned)) <&&> (do
       (AlignmentEnforced ())))) : Bool)
  then (AArch64_Abort (BitVec.addInt base offset) (← (AlignmentFault accdesc)))
  else (pure ())
  let offset ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := offset
    for e in [loop_e_lower:loop_e_upper:1]i do
      let offset := loop_vars
      loop_vars ← do
        let offset := offset
        (AArch64_MemSingle_set (BitVec.addInt base offset) 1 accdesc aligned (← (Elem_read src e 8)))
        (pure (offset +i 1))
    (pure loop_vars) ) : SailM Int )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_STNT1B_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
          (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_STNT1H_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
          (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1W_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
          (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1D_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let mbytes := (Int.ediv esize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
          (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST2B_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST2H_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST2W_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST2D_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST3B_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST3H_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST3W_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST3D_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST4B_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST4H_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST4W_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST4D_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_ST2Q_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_ST3Q_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_ST4Q_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := (((BitVec.toNat offset) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1B_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1H_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1W_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_Z_P_BZ_D_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1B_Z_P_BZ_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1H_Z_P_BZ_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1W_Z_P_BZ_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 1 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1H_Z_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 2 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1W_Z_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 3 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_Z_P_BZ_D_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 1 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1H_Z_P_BZ_S_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 2 ∧ offs_size = 32 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1W_Z_P_BZ_S_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1B_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1H_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1W_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 0 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_Z_P_BZ_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 1 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1H_Z_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 2 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1W_Z_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ scale = 3 ∧ offs_size = 64 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_Z_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let offset ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, offset, src)))
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
        let src ← (Z_read t VL)
        (pure (base, offset, src))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1B_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let src ← (Z_read t VL)
        (pure (base, src)))
    else (pure (base, src)) ) : SailM ((BitVec VL) × (BitVec VL)) )
  let src := src
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
          let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1H_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let src ← (Z_read t VL)
        (pure (base, src)))
    else (pure (base, src)) ) : SailM ((BitVec VL) × (BitVec VL)) )
  let src := src
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
          let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1W_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let src ← (Z_read t VL)
        (pure (base, src)))
    else (pure (base, src)) ) : SailM ((BitVec VL) × (BitVec VL)) )
  let src := src
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
          let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let src ← (Z_read t VL)
        (pure (base, src)))
    else (pure (base, src)) ) : SailM ((BitVec VL) × (BitVec VL)) )
  let src := src
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
          let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1B_Z_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let src ← (Z_read t VL)
        (pure (base, src)))
    else (pure (base, src)) ) : SailM ((BitVec VL) × (BitVec VL)) )
  let src := src
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
          let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1H_Z_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let src ← (Z_read t VL)
        (pure (base, src)))
    else (pure (base, src)) ) : SailM ((BitVec VL) × (BitVec VL)) )
  let src := src
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
          let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1W_Z_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let src ← (Z_read t VL)
        (pure (base, src)))
    else (pure (base, src)) ) : SailM ((BitVec VL) × (BitVec VL)) )
  let src := src
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
          let addr ← (( do (pure (BitVec.addInt (Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) (offset *i mbytes))) ) : SailM (BitVec 64) )
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ (is_VL VL) -/
def execute_ST1B_Z_P_BI__ (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, src)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let src ← (Z_read t VL)
        (pure (base, src))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let eoff := ((offset *i elements) +i e)
          let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ (is_VL VL) -/
def execute_ST1H_Z_P_BI__ (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, src)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let src ← (Z_read t VL)
        (pure (base, src))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let eoff := ((offset *i elements) +i e)
          let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
          sail_assert ((0 ≤b (msize -i 1)) && ((msize -i 1) <b esize)) "src/instrs64_sve.sail:86003.70-86003.71"
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_ST1W_Z_P_BI__ (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, src)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let src ← (Z_read t VL)
        (pure (base, src))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let eoff := ((offset *i elements) +i e)
          let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_Z_P_BI__ (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, src)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let src ← (Z_read t VL)
        (pure (base, src))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let eoff := ((offset *i elements) +i e)
          let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_ST1W_Z_P_BI_U128 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, src)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let src ← (Z_read t VL)
        (pure (base, src))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let eoff := ((offset *i elements) +i e)
          let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_ST1D_Z_P_BI_U128 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, src)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let src ← (Z_read t VL)
        (pure (base, src))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let eoff := ((offset *i elements) +i e)
          let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_STNT1B_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, src)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let src ← (Z_read t VL)
        (pure (base, src))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let eoff := ((offset *i elements) +i e)
          let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
          (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_STNT1H_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, src)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let src ← (Z_read t VL)
        (pure (base, src))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let eoff := ((offset *i elements) +i e)
          let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
          (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1W_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, src)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let src ← (Z_read t VL)
        (pure (base, src))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let eoff := ((offset *i elements) +i e)
          let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
          (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1D_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let base ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let mbytes := (Int.ediv esize 8)
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, src) ← (( do
    if ((! (← (AnyActiveElement mask esize))) : Bool)
    then
      (do
        if ((←((pure (n == 31)) <&&> (do
             (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE)))) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (pure (base, src)))
    else
      (do
        if ((n == 31) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        let base ←
          if ((n == 31) : Bool)
          then (SP_read ())
          else (X_read n 64)
        let src ← (Z_read t VL)
        (pure (base, src))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e esize)) : Bool)
      then
        (do
          let eoff := ((offset *i elements) +i e)
          let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
          (Mem_set addr mbytes accdesc (← (Elem_read src e esize))))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST2B_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST2H_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST2W_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST2D_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST3B_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST3H_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST3W_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST3D_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST4B_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST4H_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST4W_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST4D_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_ST2Q_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 2) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 3 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_ST3Q_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 3) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_ST4Q_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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
  let values_name ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := values_name
    for r in [loop_r_lower:loop_r_upper:1]i do
      let values_name := loop_vars
      loop_vars ← do (pure (vectorUpdate values_name r (← (Z_read (Nat.mod (t +i r) 32) VL))))
    (pure loop_vars) ) : SailM (Vector (BitVec VL) 4) )
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars_1 := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      let loop_r_lower := 0
      let loop_r_upper := (nreg -i 1)
      let mut loop_vars_2 := ()
      for r in [loop_r_lower:loop_r_upper:1]i do
        let () := loop_vars_2
        loop_vars_2 ← do
          if ((← (ActivePredicateElement mask e esize)) : Bool)
          then
            (do
              let eoff := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              (Mem_set addr mbytes accdesc (← (Elem_read (GetElem?.getElem! values_name r) e esize))))
          else (pure ())
      (pure loop_vars_2)
  (pure loop_vars_1)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNT1B_Z_P_AR_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec VL) × (BitVec 64)) )
  let offset := offset
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
              let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
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
def execute_LDNT1H_Z_P_AR_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec VL) × (BitVec 64)) )
  let offset := offset
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
              let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
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
def execute_LDNT1W_Z_P_AR_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec VL) × (BitVec 64)) )
  let offset := offset
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
              let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
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
def execute_LDNT1SB_Z_P_AR_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec VL) × (BitVec 64)) )
  let offset := offset
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
              let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
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
def execute_LDNT1SH_Z_P_AR_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec VL) × (BitVec 64)) )
  let offset := offset
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
              let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
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
def execute_LDNT1B_Z_P_AR_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec VL) × (BitVec 64)) )
  let offset := offset
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
              let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
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
def execute_LDNT1H_Z_P_AR_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec VL) × (BitVec 64)) )
  let offset := offset
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
              let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
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
def execute_LDNT1W_Z_P_AR_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec VL) × (BitVec 64)) )
  let offset := offset
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
              let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
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
def execute_LDNT1D_Z_P_AR_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec VL) × (BitVec 64)) )
  let offset := offset
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
              let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
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
def execute_LDNT1SB_Z_P_AR_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec VL) × (BitVec 64)) )
  let offset := offset
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
              let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
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
def execute_LDNT1SH_Z_P_AR_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec VL) × (BitVec 64)) )
  let offset := offset
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
              let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
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
def execute_LDNT1SW_Z_P_AR_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let data ← (( do (undefined_bitvector msize) ) : SailM (BitVec msize) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec VL) × (BitVec 64)) )
  let offset := offset
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
              let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1B_Z_P_AR_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        let src ← (Z_read t VL)
        (pure (base, offset, src)))
    else (pure (base, offset, src)) ) : SailM ((BitVec VL) × (BitVec 64) × (BitVec VL)) )
  let src := src
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
          let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1H_Z_P_AR_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        let src ← (Z_read t VL)
        (pure (base, offset, src)))
    else (pure (base, offset, src)) ) : SailM ((BitVec VL) × (BitVec 64) × (BitVec VL)) )
  let src := src
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
          let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1W_Z_P_AR_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        let src ← (Z_read t VL)
        (pure (base, offset, src)))
    else (pure (base, offset, src)) ) : SailM ((BitVec VL) × (BitVec 64) × (BitVec VL)) )
  let src := src
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
          let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 8 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1B_Z_P_AR_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        let src ← (Z_read t VL)
        (pure (base, offset, src)))
    else (pure (base, offset, src)) ) : SailM ((BitVec VL) × (BitVec 64) × (BitVec VL)) )
  let src := src
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
          let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 16 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1H_Z_P_AR_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        let src ← (Z_read t VL)
        (pure (base, offset, src)))
    else (pure (base, offset, src)) ) : SailM ((BitVec VL) × (BitVec 64) × (BitVec VL)) )
  let src := src
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
          let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 32 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1W_Z_P_AR_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        let src ← (Z_read t VL)
        (pure (base, offset, src)))
    else (pure (base, offset, src)) ) : SailM ((BitVec VL) × (BitVec 64) × (BitVec VL)) )
  let src := src
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
          let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ msize = 64 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1D_Z_P_AR_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL := VL
  let PL := (Int.ediv VL 8)
  let elements := (Int.ediv VL esize)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let mbytes := (Int.ediv msize 8)
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((← (AnyActiveElement mask esize)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        let src ← (Z_read t VL)
        (pure (base, offset, src)))
    else (pure (base, offset, src)) ) : SailM ((BitVec VL) × (BitVec 64) × (BitVec VL)) )
  let src := src
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
          let addr ← (( do (pure ((Sail.BitVec.zeroExtend (← (Elem_read base e esize)) 64) + offset)) ) : SailM (BitVec 64) )
          (Mem_set addr mbytes accdesc (Sail.BitVec.extractLsb (← (Elem_read src e esize)) (msize -i 1) 0)))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_LD1Q_Z_P_AR_D_64_unscaled (VL : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  let VL := VL
  let PL := (Int.ediv VL 8)
  (CheckNonStreamingSVEEnabled ())
  let elements := (Int.ediv VL 128)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset) ← (( do
    if ((← (AnyActiveElement mask 128)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        (pure (base, offset)))
    else (pure (base, offset)) ) : SailM ((BitVec VL) × (BitVec 64)) )
  let offset := offset
  let base := base
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        if ((← (ActivePredicateElement mask e 128)) : Bool)
        then
          (do
            let addr ← (( do (pure ((← (Elem_read base (2 *i e) 64)) + offset)) ) : SailM (BitVec 64) )
            (Elem_set result e 128 (← (Mem_read addr 16 accdesc))))
        else (do (Elem_set result e 128 (Zeros (n := 128))))
    (pure loop_vars) ) : SailM (BitVec VL) )
  (Z_set t VL result)

/-- Type quantifiers: VL : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_ST1Q_Z_P_AR_D_64_unscaled (VL : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  let VL := VL
  let PL := (Int.ediv VL 8)
  (CheckNonStreamingSVEEnabled ())
  let elements := (Int.ediv VL 128)
  let mask ← (( do (P_read g PL) ) : SailM (BitVec PL) )
  let base ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let src ← (( do (undefined_bitvector VL) ) : SailM (BitVec VL) )
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM AccessDescriptor )
  let (base, offset, src) ← (( do
    if ((← (AnyActiveElement mask 128)) : Bool)
    then
      (do
        let base ← (Z_read n VL)
        let offset ← (X_read m 64)
        let src ← (Z_read t VL)
        (pure (base, offset, src)))
    else (pure (base, offset, src)) ) : SailM ((BitVec VL) × (BitVec 64) × (BitVec VL)) )
  let src := src
  let offset := offset
  let base := base
  let loop_e_lower := 0
  let loop_e_upper := (elements -i 1)
  let mut loop_vars := ()
  for e in [loop_e_lower:loop_e_upper:1]i do
    let () := loop_vars
    loop_vars ← do
      if ((← (ActivePredicateElement mask e 128)) : Bool)
      then
        (do
          let addr ← (( do (pure ((← (Elem_read base (2 *i e) 64)) + offset)) ) : SailM (BitVec 64) )
          (Mem_set addr 16 accdesc (← (Elem_read src e 128))))
      else (pure ())
  (pure loop_vars)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1B_MZ_P_BR_2 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1H_MZ_P_BR_2 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1W_MZ_P_BR_2 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_MZ_P_BR_2 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1B_MZ_P_BR_4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1H_MZ_P_BR_4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1W_MZ_P_BR_4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_MZ_P_BR_4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LDNT1B_MZ_P_BR_2 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDNT1H_MZ_P_BR_2 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNT1W_MZ_P_BR_2 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNT1D_MZ_P_BR_2 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LDNT1B_MZ_P_BR_4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDNT1H_MZ_P_BR_4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNT1W_MZ_P_BR_4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNT1D_MZ_P_BR_4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST1B_MZ_P_BR_2 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST1H_MZ_P_BR_2 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1W_MZ_P_BR_2 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_MZ_P_BR_2 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST1B_MZ_P_BR_4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST1H_MZ_P_BR_4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1W_MZ_P_BR_4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_MZ_P_BR_4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_STNT1B_MZ_P_BR_2 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_STNT1H_MZ_P_BR_2 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1W_MZ_P_BR_2 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1D_MZ_P_BR_2 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_STNT1B_MZ_P_BR_4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_STNT1H_MZ_P_BR_4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1W_MZ_P_BR_4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, nreg : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1D_MZ_P_BR_4 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (nreg : Nat) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1B_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1H_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1W_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1B_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1H_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1W_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LDNT1B_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDNT1H_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNT1W_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNT1D_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LDNT1B_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDNT1H_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNT1W_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNT1D_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let loop_r_lower := 0
  let loop_r_upper := (nreg -i 1)
  let mut loop_vars_2 := ()
  for r in [loop_r_lower:loop_r_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do (Z_set (t +i r) VL (GetElem?.getElem! values_name r))
  (pure loop_vars_2)

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST1B_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST1H_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1W_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST1B_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST1H_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1W_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_STNT1B_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_STNT1H_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1W_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1D_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  if ((← (HaveSVE2p1 ())) : Bool)
  then (CheckSVEEnabled ())
  else (CheckStreamingSVEEnabled ())
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
  let src ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (nreg -i 1)
    let mut loop_vars := src
    for r in [loop_r_lower:loop_r_upper:1]i do
      let src := loop_vars
      loop_vars ← do
        let src ← (Z_read (t +i r) VL)
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
        (pure src)
    (pure loop_vars) ) : SailM (BitVec VL) )
  (pure ())


