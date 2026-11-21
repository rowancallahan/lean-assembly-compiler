import Armv9.Armv9
import Armv9.Flow
import Armv9.Arith
import Armv9.Vector
import Armv9.MonoRewrites
import Armv9.Prelude
import Armv9.Builtins
import Armv9.V8Base
import Armv9.Instrs64Sve.P00
import Armv9.Instrs64Sve.P01

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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_STNT1B_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_STNT1H_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1W_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1D_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
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

def decode_FADD_Z_P_ZS__ (size : (BitVec 2)) (Pg : (BitVec 3)) (i1 : (BitVec 1)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let imm ← (( do
    if ((i1 == 0#1) : Bool)
    then
      (do
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:79.49-79.50"
        (FPPointFive 0#1 esize))
    else
      (do
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:82.49-82.50"
        (FPOne 0#1 esize)) ) : SailM (BitVec esize) )
  match VL with
  | 128 => (execute_FADD_Z_P_ZS__ 128 dn esize g imm)
  | 256 => (execute_FADD_Z_P_ZS__ 256 dn esize g imm)
  | 512 => (execute_FADD_Z_P_ZS__ 512 dn esize g imm)
  | 1024 => (execute_FADD_Z_P_ZS__ 1024 dn esize g imm)
  | 2048 => (execute_FADD_Z_P_ZS__ 2048 dn esize g imm)
  | _ => (pure ())

def decode_FSUB_Z_P_ZS__ (size : (BitVec 2)) (Pg : (BitVec 3)) (i1 : (BitVec 1)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let imm ← (( do
    if ((i1 == 0#1) : Bool)
    then
      (do
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:152.49-152.50"
        (FPPointFive 0#1 esize))
    else
      (do
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:155.49-155.50"
        (FPOne 0#1 esize)) ) : SailM (BitVec esize) )
  match VL with
  | 128 => (execute_FSUB_Z_P_ZS__ 128 dn esize g imm)
  | 256 => (execute_FSUB_Z_P_ZS__ 256 dn esize g imm)
  | 512 => (execute_FSUB_Z_P_ZS__ 512 dn esize g imm)
  | 1024 => (execute_FSUB_Z_P_ZS__ 1024 dn esize g imm)
  | 2048 => (execute_FSUB_Z_P_ZS__ 2048 dn esize g imm)
  | _ => (pure ())

def decode_FMUL_Z_P_ZS__ (size : (BitVec 2)) (Pg : (BitVec 3)) (i1 : (BitVec 1)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let imm ← (( do
    if ((i1 == 0#1) : Bool)
    then
      (do
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:225.49-225.50"
        (FPPointFive 0#1 esize))
    else
      (do
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:228.49-228.50"
        (FPTwo 0#1 esize)) ) : SailM (BitVec esize) )
  match VL with
  | 128 => (execute_FMUL_Z_P_ZS__ 128 dn esize g imm)
  | 256 => (execute_FMUL_Z_P_ZS__ 256 dn esize g imm)
  | 512 => (execute_FMUL_Z_P_ZS__ 512 dn esize g imm)
  | 1024 => (execute_FMUL_Z_P_ZS__ 1024 dn esize g imm)
  | 2048 => (execute_FMUL_Z_P_ZS__ 2048 dn esize g imm)
  | _ => (pure ())

def decode_FSUBR_Z_P_ZS__ (size : (BitVec 2)) (Pg : (BitVec 3)) (i1 : (BitVec 1)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let imm ← (( do
    if ((i1 == 0#1) : Bool)
    then
      (do
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:298.49-298.50"
        (FPPointFive 0#1 esize))
    else
      (do
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:301.49-301.50"
        (FPOne 0#1 esize)) ) : SailM (BitVec esize) )
  match VL with
  | 128 => (execute_FSUBR_Z_P_ZS__ 128 dn esize g imm)
  | 256 => (execute_FSUBR_Z_P_ZS__ 256 dn esize g imm)
  | 512 => (execute_FSUBR_Z_P_ZS__ 512 dn esize g imm)
  | 1024 => (execute_FSUBR_Z_P_ZS__ 1024 dn esize g imm)
  | 2048 => (execute_FSUBR_Z_P_ZS__ 2048 dn esize g imm)
  | _ => (pure ())

def decode_FMAXNM_Z_P_ZS__ (size : (BitVec 2)) (Pg : (BitVec 3)) (i1 : (BitVec 1)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let imm ← (( do
    if ((i1 == 0#1) : Bool)
    then (pure (Zeros (n := esize)))
    else
      (do
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:371.49-371.50"
        (FPOne 0#1 esize)) ) : SailM (BitVec esize) )
  match VL with
  | 128 => (execute_FMAXNM_Z_P_ZS__ 128 dn esize g imm)
  | 256 => (execute_FMAXNM_Z_P_ZS__ 256 dn esize g imm)
  | 512 => (execute_FMAXNM_Z_P_ZS__ 512 dn esize g imm)
  | 1024 => (execute_FMAXNM_Z_P_ZS__ 1024 dn esize g imm)
  | 2048 => (execute_FMAXNM_Z_P_ZS__ 2048 dn esize g imm)
  | _ => (pure ())

def decode_FMINNM_Z_P_ZS__ (size : (BitVec 2)) (Pg : (BitVec 3)) (i1 : (BitVec 1)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let imm ← (( do
    if ((i1 == 0#1) : Bool)
    then (pure (Zeros (n := esize)))
    else
      (do
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:441.49-441.50"
        (FPOne 0#1 esize)) ) : SailM (BitVec esize) )
  match VL with
  | 128 => (execute_FMINNM_Z_P_ZS__ 128 dn esize g imm)
  | 256 => (execute_FMINNM_Z_P_ZS__ 256 dn esize g imm)
  | 512 => (execute_FMINNM_Z_P_ZS__ 512 dn esize g imm)
  | 1024 => (execute_FMINNM_Z_P_ZS__ 1024 dn esize g imm)
  | 2048 => (execute_FMINNM_Z_P_ZS__ 2048 dn esize g imm)
  | _ => (pure ())

def decode_FMAX_Z_P_ZS__ (size : (BitVec 2)) (Pg : (BitVec 3)) (i1 : (BitVec 1)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let imm ← (( do
    if ((i1 == 0#1) : Bool)
    then (pure (Zeros (n := esize)))
    else
      (do
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:511.49-511.50"
        (FPOne 0#1 esize)) ) : SailM (BitVec esize) )
  match VL with
  | 128 => (execute_FMAX_Z_P_ZS__ 128 dn esize g imm)
  | 256 => (execute_FMAX_Z_P_ZS__ 256 dn esize g imm)
  | 512 => (execute_FMAX_Z_P_ZS__ 512 dn esize g imm)
  | 1024 => (execute_FMAX_Z_P_ZS__ 1024 dn esize g imm)
  | 2048 => (execute_FMAX_Z_P_ZS__ 2048 dn esize g imm)
  | _ => (pure ())

def decode_FMIN_Z_P_ZS__ (size : (BitVec 2)) (Pg : (BitVec 3)) (i1 : (BitVec 1)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let imm ← (( do
    if ((i1 == 0#1) : Bool)
    then (pure (Zeros (n := esize)))
    else
      (do
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:581.49-581.50"
        (FPOne 0#1 esize)) ) : SailM (BitVec esize) )
  match VL with
  | 128 => (execute_FMIN_Z_P_ZS__ 128 dn esize g imm)
  | 256 => (execute_FMIN_Z_P_ZS__ 256 dn esize g imm)
  | 512 => (execute_FMIN_Z_P_ZS__ 512 dn esize g imm)
  | 1024 => (execute_FMIN_Z_P_ZS__ 1024 dn esize g imm)
  | 2048 => (execute_FMIN_Z_P_ZS__ 2048 dn esize g imm)
  | _ => (pure ())

def decode_FCMGE_P_P_Z0__ (size : (BitVec 2)) (eq : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GE
  match VL with
  | 128 => (execute_FCMGE_P_P_Z0__ 128 d esize g n op)
  | 256 => (execute_FCMGE_P_P_Z0__ 256 d esize g n op)
  | 512 => (execute_FCMGE_P_P_Z0__ 512 d esize g n op)
  | 1024 => (execute_FCMGE_P_P_Z0__ 1024 d esize g n op)
  | 2048 => (execute_FCMGE_P_P_Z0__ 2048 d esize g n op)
  | _ => (pure ())

def decode_FCMGT_P_P_Z0__ (size : (BitVec 2)) (eq : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GT
  match VL with
  | 128 => (execute_FCMGT_P_P_Z0__ 128 d esize g n op)
  | 256 => (execute_FCMGT_P_P_Z0__ 256 d esize g n op)
  | 512 => (execute_FCMGT_P_P_Z0__ 512 d esize g n op)
  | 1024 => (execute_FCMGT_P_P_Z0__ 1024 d esize g n op)
  | 2048 => (execute_FCMGT_P_P_Z0__ 2048 d esize g n op)
  | _ => (pure ())

def decode_FCMLT_P_P_Z0__ (size : (BitVec 2)) (eq : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_LT
  match VL with
  | 128 => (execute_FCMLT_P_P_Z0__ 128 d esize g n op)
  | 256 => (execute_FCMLT_P_P_Z0__ 256 d esize g n op)
  | 512 => (execute_FCMLT_P_P_Z0__ 512 d esize g n op)
  | 1024 => (execute_FCMLT_P_P_Z0__ 1024 d esize g n op)
  | 2048 => (execute_FCMLT_P_P_Z0__ 2048 d esize g n op)
  | _ => (pure ())

def decode_FCMLE_P_P_Z0__ (size : (BitVec 2)) (eq : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_LE
  match VL with
  | 128 => (execute_FCMLE_P_P_Z0__ 128 d esize g n op)
  | 256 => (execute_FCMLE_P_P_Z0__ 256 d esize g n op)
  | 512 => (execute_FCMLE_P_P_Z0__ 512 d esize g n op)
  | 1024 => (execute_FCMLE_P_P_Z0__ 1024 d esize g n op)
  | 2048 => (execute_FCMLE_P_P_Z0__ 2048 d esize g n op)
  | _ => (pure ())

def decode_FCMEQ_P_P_Z0__ (size : (BitVec 2)) (eq : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_EQ
  match VL with
  | 128 => (execute_FCMEQ_P_P_Z0__ 128 d esize g n op)
  | 256 => (execute_FCMEQ_P_P_Z0__ 256 d esize g n op)
  | 512 => (execute_FCMEQ_P_P_Z0__ 512 d esize g n op)
  | 1024 => (execute_FCMEQ_P_P_Z0__ 1024 d esize g n op)
  | 2048 => (execute_FCMEQ_P_P_Z0__ 2048 d esize g n op)
  | _ => (pure ())

def decode_FCMNE_P_P_Z0__ (size : (BitVec 2)) (eq : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_NE
  match VL with
  | 128 => (execute_FCMNE_P_P_Z0__ 128 d esize g n op)
  | 256 => (execute_FCMNE_P_P_Z0__ 256 d esize g n op)
  | 512 => (execute_FCMNE_P_P_Z0__ 512 d esize g n op)
  | 1024 => (execute_FCMNE_P_P_Z0__ 1024 d esize g n op)
  | 2048 => (execute_FCMNE_P_P_Z0__ 2048 d esize g n op)
  | _ => (pure ())

def decode_FADDA_V_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Vdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Vdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_FADDA_V_P_Z__ 128 dn esize g m)
  | 256 => (execute_FADDA_V_P_Z__ 256 dn esize g m)
  | 512 => (execute_FADDA_V_P_Z__ 512 dn esize g m)
  | 1024 => (execute_FADDA_V_P_Z__ 1024 dn esize g m)
  | 2048 => (execute_FADDA_V_P_Z__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FCVTZU_Z_P_Z_D2X (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 64
  let d_esize := 64
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZU_Z_P_Z_D2X 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_FCVTZU_Z_P_Z_D2X 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_FCVTZU_Z_P_Z_D2X 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_FCVTZU_Z_P_Z_D2X 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_FCVTZU_Z_P_Z_D2X 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_FCVTZU_Z_P_Z_D2W (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 64
  let d_esize := 32
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZU_Z_P_Z_D2W 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_FCVTZU_Z_P_Z_D2W 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_FCVTZU_Z_P_Z_D2W 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_FCVTZU_Z_P_Z_D2W 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_FCVTZU_Z_P_Z_D2W 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_FCVTZU_Z_P_Z_S2W (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 32
  let d_esize := 32
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZU_Z_P_Z_S2W 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_FCVTZU_Z_P_Z_S2W 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_FCVTZU_Z_P_Z_S2W 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_FCVTZU_Z_P_Z_S2W 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_FCVTZU_Z_P_Z_S2W 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_FCVTZU_Z_P_Z_S2X (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 32
  let d_esize := 64
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZU_Z_P_Z_S2X 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_FCVTZU_Z_P_Z_S2X 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_FCVTZU_Z_P_Z_S2X 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_FCVTZU_Z_P_Z_S2X 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_FCVTZU_Z_P_Z_S2X 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_FCVTZS_Z_P_Z_D2X (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 64
  let d_esize := 64
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZS_Z_P_Z_D2X 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_FCVTZS_Z_P_Z_D2X 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_FCVTZS_Z_P_Z_D2X 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_FCVTZS_Z_P_Z_D2X 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_FCVTZS_Z_P_Z_D2X 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_FCVTZS_Z_P_Z_D2W (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 64
  let d_esize := 32
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZS_Z_P_Z_D2W 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_FCVTZS_Z_P_Z_D2W 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_FCVTZS_Z_P_Z_D2W 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_FCVTZS_Z_P_Z_D2W 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_FCVTZS_Z_P_Z_D2W 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_FCVTZS_Z_P_Z_S2W (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 32
  let d_esize := 32
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZS_Z_P_Z_S2W 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_FCVTZS_Z_P_Z_S2W 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_FCVTZS_Z_P_Z_S2W 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_FCVTZS_Z_P_Z_S2W 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_FCVTZS_Z_P_Z_S2W 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_FCVTZS_Z_P_Z_S2X (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 32
  let d_esize := 64
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZS_Z_P_Z_S2X 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_FCVTZS_Z_P_Z_S2X 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_FCVTZS_Z_P_Z_S2X 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_FCVTZS_Z_P_Z_S2X 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_FCVTZS_Z_P_Z_S2X 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_FCVTZS_Z_P_Z_FP162H (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 16
  let d_esize := 16
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZS_Z_P_Z_FP162H 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_FCVTZS_Z_P_Z_FP162H 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_FCVTZS_Z_P_Z_FP162H 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_FCVTZS_Z_P_Z_FP162H 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_FCVTZS_Z_P_Z_FP162H 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_FCVTZS_Z_P_Z_FP162W (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 16
  let d_esize := 32
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZS_Z_P_Z_FP162W 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_FCVTZS_Z_P_Z_FP162W 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_FCVTZS_Z_P_Z_FP162W 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_FCVTZS_Z_P_Z_FP162W 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_FCVTZS_Z_P_Z_FP162W 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_FCVTZS_Z_P_Z_FP162X (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 16
  let d_esize := 64
  let is_unsigned : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZS_Z_P_Z_FP162X 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_FCVTZS_Z_P_Z_FP162X 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_FCVTZS_Z_P_Z_FP162X 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_FCVTZS_Z_P_Z_FP162X 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_FCVTZS_Z_P_Z_FP162X 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_FCVTZU_Z_P_Z_FP162H (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 16
  let d_esize := 16
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZU_Z_P_Z_FP162H 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_FCVTZU_Z_P_Z_FP162H 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_FCVTZU_Z_P_Z_FP162H 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_FCVTZU_Z_P_Z_FP162H 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_FCVTZU_Z_P_Z_FP162H 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_FCVTZU_Z_P_Z_FP162W (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 16
  let d_esize := 32
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZU_Z_P_Z_FP162W 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_FCVTZU_Z_P_Z_FP162W 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_FCVTZU_Z_P_Z_FP162W 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_FCVTZU_Z_P_Z_FP162W 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_FCVTZU_Z_P_Z_FP162W 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_FCVTZU_Z_P_Z_FP162X (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 16
  let d_esize := 64
  let is_unsigned : Bool := true
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FCVTZU_Z_P_Z_FP162X 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_FCVTZU_Z_P_Z_FP162X 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_FCVTZU_Z_P_Z_FP162X 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_FCVTZU_Z_P_Z_FP162X 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_FCVTZU_Z_P_Z_FP162X 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_SCVTF_Z_P_Z_H2FP16 (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 16
  let d_esize := 16
  let is_unsigned : Bool := false
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_SCVTF_Z_P_Z_H2FP16 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_SCVTF_Z_P_Z_H2FP16 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_SCVTF_Z_P_Z_H2FP16 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_SCVTF_Z_P_Z_H2FP16 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_SCVTF_Z_P_Z_H2FP16 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_SCVTF_Z_P_Z_W2FP16 (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 32
  let d_esize := 16
  let is_unsigned : Bool := false
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_SCVTF_Z_P_Z_W2FP16 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_SCVTF_Z_P_Z_W2FP16 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_SCVTF_Z_P_Z_W2FP16 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_SCVTF_Z_P_Z_W2FP16 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_SCVTF_Z_P_Z_W2FP16 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_SCVTF_Z_P_Z_X2FP16 (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 64
  let d_esize := 16
  let is_unsigned : Bool := false
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_SCVTF_Z_P_Z_X2FP16 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_SCVTF_Z_P_Z_X2FP16 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_SCVTF_Z_P_Z_X2FP16 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_SCVTF_Z_P_Z_X2FP16 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_SCVTF_Z_P_Z_X2FP16 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_UCVTF_Z_P_Z_H2FP16 (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 16
  let d_esize := 16
  let is_unsigned : Bool := true
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_UCVTF_Z_P_Z_H2FP16 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_UCVTF_Z_P_Z_H2FP16 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_UCVTF_Z_P_Z_H2FP16 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_UCVTF_Z_P_Z_H2FP16 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_UCVTF_Z_P_Z_H2FP16 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_UCVTF_Z_P_Z_W2FP16 (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 32
  let d_esize := 16
  let is_unsigned : Bool := true
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_UCVTF_Z_P_Z_W2FP16 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_UCVTF_Z_P_Z_W2FP16 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_UCVTF_Z_P_Z_W2FP16 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_UCVTF_Z_P_Z_W2FP16 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_UCVTF_Z_P_Z_W2FP16 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_UCVTF_Z_P_Z_X2FP16 (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 64
  let d_esize := 16
  let is_unsigned : Bool := true
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_UCVTF_Z_P_Z_X2FP16 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_UCVTF_Z_P_Z_X2FP16 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_UCVTF_Z_P_Z_X2FP16 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_UCVTF_Z_P_Z_X2FP16 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_UCVTF_Z_P_Z_X2FP16 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_FCVT_Z_P_Z_D2S (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 64
  let d_esize := 32
  match VL with
  | 128 => (execute_FCVT_Z_P_Z_D2S 128 d d_esize esize g n s_esize)
  | 256 => (execute_FCVT_Z_P_Z_D2S 256 d d_esize esize g n s_esize)
  | 512 => (execute_FCVT_Z_P_Z_D2S 512 d d_esize esize g n s_esize)
  | 1024 => (execute_FCVT_Z_P_Z_D2S 1024 d d_esize esize g n s_esize)
  | 2048 => (execute_FCVT_Z_P_Z_D2S 2048 d d_esize esize g n s_esize)
  | _ => (pure ())

def decode_FCVT_Z_P_Z_D2H (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 64
  let d_esize := 16
  match VL with
  | 128 => (execute_FCVT_Z_P_Z_D2H 128 d d_esize esize g n s_esize)
  | 256 => (execute_FCVT_Z_P_Z_D2H 256 d d_esize esize g n s_esize)
  | 512 => (execute_FCVT_Z_P_Z_D2H 512 d d_esize esize g n s_esize)
  | 1024 => (execute_FCVT_Z_P_Z_D2H 1024 d d_esize esize g n s_esize)
  | 2048 => (execute_FCVT_Z_P_Z_D2H 2048 d d_esize esize g n s_esize)
  | _ => (pure ())

def decode_FCVT_Z_P_Z_S2D (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 32
  let d_esize := 64
  match VL with
  | 128 => (execute_FCVT_Z_P_Z_S2D 128 d d_esize esize g n s_esize)
  | 256 => (execute_FCVT_Z_P_Z_S2D 256 d d_esize esize g n s_esize)
  | 512 => (execute_FCVT_Z_P_Z_S2D 512 d d_esize esize g n s_esize)
  | 1024 => (execute_FCVT_Z_P_Z_S2D 1024 d d_esize esize g n s_esize)
  | 2048 => (execute_FCVT_Z_P_Z_S2D 2048 d d_esize esize g n s_esize)
  | _ => (pure ())

def decode_FCVT_Z_P_Z_H2D (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 16
  let d_esize := 64
  match VL with
  | 128 => (execute_FCVT_Z_P_Z_H2D 128 d d_esize esize g n s_esize)
  | 256 => (execute_FCVT_Z_P_Z_H2D 256 d d_esize esize g n s_esize)
  | 512 => (execute_FCVT_Z_P_Z_H2D 512 d d_esize esize g n s_esize)
  | 1024 => (execute_FCVT_Z_P_Z_H2D 1024 d d_esize esize g n s_esize)
  | 2048 => (execute_FCVT_Z_P_Z_H2D 2048 d d_esize esize g n s_esize)
  | _ => (pure ())

def decode_FCVT_Z_P_Z_H2S (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 16
  let d_esize := 32
  match VL with
  | 128 => (execute_FCVT_Z_P_Z_H2S 128 d d_esize esize g n s_esize)
  | 256 => (execute_FCVT_Z_P_Z_H2S 256 d d_esize esize g n s_esize)
  | 512 => (execute_FCVT_Z_P_Z_H2S 512 d d_esize esize g n s_esize)
  | 1024 => (execute_FCVT_Z_P_Z_H2S 1024 d d_esize esize g n s_esize)
  | 2048 => (execute_FCVT_Z_P_Z_H2S 2048 d d_esize esize g n s_esize)
  | _ => (pure ())

def decode_FCVT_Z_P_Z_S2H (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 32
  let d_esize := 16
  match VL with
  | 128 => (execute_FCVT_Z_P_Z_S2H 128 d d_esize esize g n s_esize)
  | 256 => (execute_FCVT_Z_P_Z_S2H 256 d d_esize esize g n s_esize)
  | 512 => (execute_FCVT_Z_P_Z_S2H 512 d d_esize esize g n s_esize)
  | 1024 => (execute_FCVT_Z_P_Z_S2H 1024 d d_esize esize g n s_esize)
  | 2048 => (execute_FCVT_Z_P_Z_S2H 2048 d d_esize esize g n s_esize)
  | _ => (pure ())

def decode_FRECPE_Z_Z__ (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FRECPE_Z_Z__ 128 d esize n)
  | 256 => (execute_FRECPE_Z_Z__ 256 d esize n)
  | 512 => (execute_FRECPE_Z_Z__ 512 d esize n)
  | 1024 => (execute_FRECPE_Z_Z__ 1024 d esize n)
  | 2048 => (execute_FRECPE_Z_Z__ 2048 d esize n)
  | _ => (pure ())

def decode_FRSQRTE_Z_Z__ (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FRSQRTE_Z_Z__ 128 d esize n)
  | 256 => (execute_FRSQRTE_Z_Z__ 256 d esize n)
  | 512 => (execute_FRSQRTE_Z_Z__ 512 d esize n)
  | 1024 => (execute_FRSQRTE_Z_Z__ 1024 d esize n)
  | 2048 => (execute_FRSQRTE_Z_Z__ 2048 d esize n)
  | _ => (pure ())

def decode_FRECPX_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FRECPX_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_FRECPX_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_FRECPX_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_FRECPX_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_FRECPX_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_FSQRT_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FSQRT_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_FSQRT_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_FSQRT_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_FSQRT_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_FSQRT_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_FRINTA_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_TIEAWAY
  match VL with
  | 128 => (execute_FRINTA_Z_P_Z__ 128 d esize exact g n rounding)
  | 256 => (execute_FRINTA_Z_P_Z__ 256 d esize exact g n rounding)
  | 512 => (execute_FRINTA_Z_P_Z__ 512 d esize exact g n rounding)
  | 1024 => (execute_FRINTA_Z_P_Z__ 1024 d esize exact g n rounding)
  | 2048 => (execute_FRINTA_Z_P_Z__ 2048 d esize exact g n rounding)
  | _ => (pure ())

def decode_FRINTI_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let exact : Bool := false
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_FRINTI_Z_P_Z__ 128 d esize exact g n rounding)
  | 256 => (execute_FRINTI_Z_P_Z__ 256 d esize exact g n rounding)
  | 512 => (execute_FRINTI_Z_P_Z__ 512 d esize exact g n rounding)
  | 1024 => (execute_FRINTI_Z_P_Z__ 1024 d esize exact g n rounding)
  | 2048 => (execute_FRINTI_Z_P_Z__ 2048 d esize exact g n rounding)
  | _ => (pure ())

def decode_FRINTM_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_NEGINF
  match VL with
  | 128 => (execute_FRINTM_Z_P_Z__ 128 d esize exact g n rounding)
  | 256 => (execute_FRINTM_Z_P_Z__ 256 d esize exact g n rounding)
  | 512 => (execute_FRINTM_Z_P_Z__ 512 d esize exact g n rounding)
  | 1024 => (execute_FRINTM_Z_P_Z__ 1024 d esize exact g n rounding)
  | 2048 => (execute_FRINTM_Z_P_Z__ 2048 d esize exact g n rounding)
  | _ => (pure ())

def decode_FRINTN_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_TIEEVEN
  match VL with
  | 128 => (execute_FRINTN_Z_P_Z__ 128 d esize exact g n rounding)
  | 256 => (execute_FRINTN_Z_P_Z__ 256 d esize exact g n rounding)
  | 512 => (execute_FRINTN_Z_P_Z__ 512 d esize exact g n rounding)
  | 1024 => (execute_FRINTN_Z_P_Z__ 1024 d esize exact g n rounding)
  | 2048 => (execute_FRINTN_Z_P_Z__ 2048 d esize exact g n rounding)
  | _ => (pure ())

def decode_FRINTP_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_POSINF
  match VL with
  | 128 => (execute_FRINTP_Z_P_Z__ 128 d esize exact g n rounding)
  | 256 => (execute_FRINTP_Z_P_Z__ 256 d esize exact g n rounding)
  | 512 => (execute_FRINTP_Z_P_Z__ 512 d esize exact g n rounding)
  | 1024 => (execute_FRINTP_Z_P_Z__ 1024 d esize exact g n rounding)
  | 2048 => (execute_FRINTP_Z_P_Z__ 2048 d esize exact g n rounding)
  | _ => (pure ())

def decode_FRINTX_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let exact : Bool := true
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_FRINTX_Z_P_Z__ 128 d esize exact g n rounding)
  | 256 => (execute_FRINTX_Z_P_Z__ 256 d esize exact g n rounding)
  | 512 => (execute_FRINTX_Z_P_Z__ 512 d esize exact g n rounding)
  | 1024 => (execute_FRINTX_Z_P_Z__ 1024 d esize exact g n rounding)
  | 2048 => (execute_FRINTX_Z_P_Z__ 2048 d esize exact g n rounding)
  | _ => (pure ())

def decode_FRINTZ_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_ZERO
  match VL with
  | 128 => (execute_FRINTZ_Z_P_Z__ 128 d esize exact g n rounding)
  | 256 => (execute_FRINTZ_Z_P_Z__ 256 d esize exact g n rounding)
  | 512 => (execute_FRINTZ_Z_P_Z__ 512 d esize exact g n rounding)
  | 1024 => (execute_FRINTZ_Z_P_Z__ 1024 d esize exact g n rounding)
  | 2048 => (execute_FRINTZ_Z_P_Z__ 2048 d esize exact g n rounding)
  | _ => (pure ())

def decode_UCVTF_Z_P_Z_X2S (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 64
  let d_esize := 32
  let is_unsigned : Bool := true
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_UCVTF_Z_P_Z_X2S 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_UCVTF_Z_P_Z_X2S 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_UCVTF_Z_P_Z_X2S 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_UCVTF_Z_P_Z_X2S 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_UCVTF_Z_P_Z_X2S 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_UCVTF_Z_P_Z_X2D (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 64
  let d_esize := 64
  let is_unsigned : Bool := true
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_UCVTF_Z_P_Z_X2D 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_UCVTF_Z_P_Z_X2D 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_UCVTF_Z_P_Z_X2D 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_UCVTF_Z_P_Z_X2D 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_UCVTF_Z_P_Z_X2D 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_UCVTF_Z_P_Z_W2S (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 32
  let d_esize := 32
  let is_unsigned : Bool := true
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_UCVTF_Z_P_Z_W2S 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_UCVTF_Z_P_Z_W2S 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_UCVTF_Z_P_Z_W2S 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_UCVTF_Z_P_Z_W2S 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_UCVTF_Z_P_Z_W2S 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_UCVTF_Z_P_Z_W2D (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 32
  let d_esize := 64
  let is_unsigned : Bool := true
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_UCVTF_Z_P_Z_W2D 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_UCVTF_Z_P_Z_W2D 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_UCVTF_Z_P_Z_W2D 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_UCVTF_Z_P_Z_W2D 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_UCVTF_Z_P_Z_W2D 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_SCVTF_Z_P_Z_X2S (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 64
  let d_esize := 32
  let is_unsigned : Bool := false
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_SCVTF_Z_P_Z_X2S 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_SCVTF_Z_P_Z_X2S 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_SCVTF_Z_P_Z_X2S 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_SCVTF_Z_P_Z_X2S 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_SCVTF_Z_P_Z_X2S 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_SCVTF_Z_P_Z_X2D (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 64
  let d_esize := 64
  let is_unsigned : Bool := false
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_SCVTF_Z_P_Z_X2D 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_SCVTF_Z_P_Z_X2D 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_SCVTF_Z_P_Z_X2D 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_SCVTF_Z_P_Z_X2D 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_SCVTF_Z_P_Z_X2D 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_SCVTF_Z_P_Z_W2S (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 32
  let d_esize := 32
  let is_unsigned : Bool := false
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_SCVTF_Z_P_Z_W2S 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_SCVTF_Z_P_Z_W2S 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_SCVTF_Z_P_Z_W2S 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_SCVTF_Z_P_Z_W2S 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_SCVTF_Z_P_Z_W2S 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_SCVTF_Z_P_Z_W2D (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 32
  let d_esize := 64
  let is_unsigned : Bool := false
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  match VL with
  | 128 => (execute_SCVTF_Z_P_Z_W2D 128 d d_esize esize g n rounding s_esize is_unsigned)
  | 256 => (execute_SCVTF_Z_P_Z_W2D 256 d d_esize esize g n rounding s_esize is_unsigned)
  | 512 => (execute_SCVTF_Z_P_Z_W2D 512 d d_esize esize g n rounding s_esize is_unsigned)
  | 1024 => (execute_SCVTF_Z_P_Z_W2D 1024 d d_esize esize g n rounding s_esize is_unsigned)
  | 2048 => (execute_SCVTF_Z_P_Z_W2D 2048 d d_esize esize g n rounding s_esize is_unsigned)
  | _ => (pure ())

def decode_FABD_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_FABD_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FABD_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FABD_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FABD_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FABD_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FADD_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_FADD_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FADD_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FADD_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FADD_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FADD_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FDIV_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_FDIV_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FDIV_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FDIV_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FDIV_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FDIV_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FDIVR_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_FDIVR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FDIVR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FDIVR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FDIVR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FDIVR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FMAXNM_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_FMAXNM_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FMAXNM_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FMAXNM_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FMAXNM_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FMAXNM_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FMINNM_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_FMINNM_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FMINNM_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FMINNM_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FMINNM_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FMINNM_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FMAX_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_FMAX_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FMAX_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FMAX_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FMAX_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FMAX_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FMIN_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_FMIN_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FMIN_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FMIN_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FMIN_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FMIN_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FMUL_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_FMUL_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FMUL_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FMUL_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FMUL_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FMUL_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FMULX_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_FMULX_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FMULX_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FMULX_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FMULX_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FMULX_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FSCALE_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_FSCALE_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FSCALE_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FSCALE_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FSCALE_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FSCALE_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FSUB_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_FSUB_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FSUB_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FSUB_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FSUB_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FSUB_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FSUBR_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_FSUBR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FSUBR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FSUBR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FSUBR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FSUBR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FADDV_V_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_FADDV_V_P_Z__ 128 d esize g n)
  | 256 => (execute_FADDV_V_P_Z__ 256 d esize g n)
  | 512 => (execute_FADDV_V_P_Z__ 512 d esize g n)
  | 1024 => (execute_FADDV_V_P_Z__ 1024 d esize g n)
  | 2048 => (execute_FADDV_V_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_FMAXNMV_V_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_FMAXNMV_V_P_Z__ 128 d esize g n)
  | 256 => (execute_FMAXNMV_V_P_Z__ 256 d esize g n)
  | 512 => (execute_FMAXNMV_V_P_Z__ 512 d esize g n)
  | 1024 => (execute_FMAXNMV_V_P_Z__ 1024 d esize g n)
  | 2048 => (execute_FMAXNMV_V_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_FMINNMV_V_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_FMINNMV_V_P_Z__ 128 d esize g n)
  | 256 => (execute_FMINNMV_V_P_Z__ 256 d esize g n)
  | 512 => (execute_FMINNMV_V_P_Z__ 512 d esize g n)
  | 1024 => (execute_FMINNMV_V_P_Z__ 1024 d esize g n)
  | 2048 => (execute_FMINNMV_V_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_FMAXV_V_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_FMAXV_V_P_Z__ 128 d esize g n)
  | 256 => (execute_FMAXV_V_P_Z__ 256 d esize g n)
  | 512 => (execute_FMAXV_V_P_Z__ 512 d esize g n)
  | 1024 => (execute_FMAXV_V_P_Z__ 1024 d esize g n)
  | 2048 => (execute_FMAXV_V_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_FMINV_V_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_FMINV_V_P_Z__ 128 d esize g n)
  | 256 => (execute_FMINV_V_P_Z__ 256 d esize g n)
  | 512 => (execute_FMINV_V_P_Z__ 512 d esize g n)
  | 1024 => (execute_FMINV_V_P_Z__ 1024 d esize g n)
  | 2048 => (execute_FMINV_V_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_FACGE_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GE
  match VL with
  | 128 => (execute_FACGE_P_P_ZZ__ 128 d esize g m n op)
  | 256 => (execute_FACGE_P_P_ZZ__ 256 d esize g m n op)
  | 512 => (execute_FACGE_P_P_ZZ__ 512 d esize g m n op)
  | 1024 => (execute_FACGE_P_P_ZZ__ 1024 d esize g m n op)
  | 2048 => (execute_FACGE_P_P_ZZ__ 2048 d esize g m n op)
  | _ => (pure ())

def decode_FACGT_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GT
  match VL with
  | 128 => (execute_FACGT_P_P_ZZ__ 128 d esize g m n op)
  | 256 => (execute_FACGT_P_P_ZZ__ 256 d esize g m n op)
  | 512 => (execute_FACGT_P_P_ZZ__ 512 d esize g m n op)
  | 1024 => (execute_FACGT_P_P_ZZ__ 1024 d esize g m n op)
  | 2048 => (execute_FACGT_P_P_ZZ__ 2048 d esize g m n op)
  | _ => (pure ())

def decode_FCMUO_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_UN
  match VL with
  | 128 => (execute_FCMUO_P_P_ZZ__ 128 d esize g m n op)
  | 256 => (execute_FCMUO_P_P_ZZ__ 256 d esize g m n op)
  | 512 => (execute_FCMUO_P_P_ZZ__ 512 d esize g m n op)
  | 1024 => (execute_FCMUO_P_P_ZZ__ 1024 d esize g m n op)
  | 2048 => (execute_FCMUO_P_P_ZZ__ 2048 d esize g m n op)
  | _ => (pure ())

def decode_FCMGE_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (cmph : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (cmpl : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GE
  match VL with
  | 128 => (execute_FCMGE_P_P_ZZ__ 128 d esize g m n op)
  | 256 => (execute_FCMGE_P_P_ZZ__ 256 d esize g m n op)
  | 512 => (execute_FCMGE_P_P_ZZ__ 512 d esize g m n op)
  | 1024 => (execute_FCMGE_P_P_ZZ__ 1024 d esize g m n op)
  | 2048 => (execute_FCMGE_P_P_ZZ__ 2048 d esize g m n op)
  | _ => (pure ())

def decode_FCMGT_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (cmph : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (cmpl : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GT
  match VL with
  | 128 => (execute_FCMGT_P_P_ZZ__ 128 d esize g m n op)
  | 256 => (execute_FCMGT_P_P_ZZ__ 256 d esize g m n op)
  | 512 => (execute_FCMGT_P_P_ZZ__ 512 d esize g m n op)
  | 1024 => (execute_FCMGT_P_P_ZZ__ 1024 d esize g m n op)
  | 2048 => (execute_FCMGT_P_P_ZZ__ 2048 d esize g m n op)
  | _ => (pure ())

def decode_FCMEQ_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (cmph : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (cmpl : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_EQ
  match VL with
  | 128 => (execute_FCMEQ_P_P_ZZ__ 128 d esize g m n op)
  | 256 => (execute_FCMEQ_P_P_ZZ__ 256 d esize g m n op)
  | 512 => (execute_FCMEQ_P_P_ZZ__ 512 d esize g m n op)
  | 1024 => (execute_FCMEQ_P_P_ZZ__ 1024 d esize g m n op)
  | 2048 => (execute_FCMEQ_P_P_ZZ__ 2048 d esize g m n op)
  | _ => (pure ())

def decode_FCMNE_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (cmph : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (cmpl : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_NE
  match VL with
  | 128 => (execute_FCMNE_P_P_ZZ__ 128 d esize g m n op)
  | 256 => (execute_FCMNE_P_P_ZZ__ 256 d esize g m n op)
  | 512 => (execute_FCMNE_P_P_ZZ__ 512 d esize g m n op)
  | 1024 => (execute_FCMNE_P_P_ZZ__ 1024 d esize g m n op)
  | 2048 => (execute_FCMNE_P_P_ZZ__ 2048 d esize g m n op)
  | _ => (pure ())

def decode_FMLA_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (N : (BitVec 1)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := false
  let op3_neg : Bool := false
  match VL with
  | 128 => (execute_FMLA_Z_P_ZZZ__ 128 da esize g m n op1_neg op3_neg)
  | 256 => (execute_FMLA_Z_P_ZZZ__ 256 da esize g m n op1_neg op3_neg)
  | 512 => (execute_FMLA_Z_P_ZZZ__ 512 da esize g m n op1_neg op3_neg)
  | 1024 => (execute_FMLA_Z_P_ZZZ__ 1024 da esize g m n op1_neg op3_neg)
  | 2048 => (execute_FMLA_Z_P_ZZZ__ 2048 da esize g m n op1_neg op3_neg)
  | _ => (pure ())

def decode_FMLS_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (N : (BitVec 1)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  let op3_neg : Bool := false
  match VL with
  | 128 => (execute_FMLS_Z_P_ZZZ__ 128 da esize g m n op1_neg op3_neg)
  | 256 => (execute_FMLS_Z_P_ZZZ__ 256 da esize g m n op1_neg op3_neg)
  | 512 => (execute_FMLS_Z_P_ZZZ__ 512 da esize g m n op1_neg op3_neg)
  | 1024 => (execute_FMLS_Z_P_ZZZ__ 1024 da esize g m n op1_neg op3_neg)
  | 2048 => (execute_FMLS_Z_P_ZZZ__ 2048 da esize g m n op1_neg op3_neg)
  | _ => (pure ())

def decode_FNMLA_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (N : (BitVec 1)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  let op3_neg : Bool := true
  match VL with
  | 128 => (execute_FNMLA_Z_P_ZZZ__ 128 da esize g m n op1_neg op3_neg)
  | 256 => (execute_FNMLA_Z_P_ZZZ__ 256 da esize g m n op1_neg op3_neg)
  | 512 => (execute_FNMLA_Z_P_ZZZ__ 512 da esize g m n op1_neg op3_neg)
  | 1024 => (execute_FNMLA_Z_P_ZZZ__ 1024 da esize g m n op1_neg op3_neg)
  | 2048 => (execute_FNMLA_Z_P_ZZZ__ 2048 da esize g m n op1_neg op3_neg)
  | _ => (pure ())

def decode_FNMLS_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (N : (BitVec 1)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := false
  let op3_neg : Bool := true
  match VL with
  | 128 => (execute_FNMLS_Z_P_ZZZ__ 128 da esize g m n op1_neg op3_neg)
  | 256 => (execute_FNMLS_Z_P_ZZZ__ 256 da esize g m n op1_neg op3_neg)
  | 512 => (execute_FNMLS_Z_P_ZZZ__ 512 da esize g m n op1_neg op3_neg)
  | 1024 => (execute_FNMLS_Z_P_ZZZ__ 1024 da esize g m n op1_neg op3_neg)
  | 2048 => (execute_FNMLS_Z_P_ZZZ__ 2048 da esize g m n op1_neg op3_neg)
  | _ => (pure ())

def decode_FMAD_Z_P_ZZZ__ (size : (BitVec 2)) (Za : (BitVec 5)) (N : (BitVec 1)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let a := (BitVec.toNat Za)
  let op1_neg : Bool := false
  let op3_neg : Bool := false
  match VL with
  | 128 => (execute_FMAD_Z_P_ZZZ__ 128 a dn esize g m op1_neg op3_neg)
  | 256 => (execute_FMAD_Z_P_ZZZ__ 256 a dn esize g m op1_neg op3_neg)
  | 512 => (execute_FMAD_Z_P_ZZZ__ 512 a dn esize g m op1_neg op3_neg)
  | 1024 => (execute_FMAD_Z_P_ZZZ__ 1024 a dn esize g m op1_neg op3_neg)
  | 2048 => (execute_FMAD_Z_P_ZZZ__ 2048 a dn esize g m op1_neg op3_neg)
  | _ => (pure ())

def decode_FMSB_Z_P_ZZZ__ (size : (BitVec 2)) (Za : (BitVec 5)) (N : (BitVec 1)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let a := (BitVec.toNat Za)
  let op1_neg : Bool := true
  let op3_neg : Bool := false
  match VL with
  | 128 => (execute_FMSB_Z_P_ZZZ__ 128 a dn esize g m op1_neg op3_neg)
  | 256 => (execute_FMSB_Z_P_ZZZ__ 256 a dn esize g m op1_neg op3_neg)
  | 512 => (execute_FMSB_Z_P_ZZZ__ 512 a dn esize g m op1_neg op3_neg)
  | 1024 => (execute_FMSB_Z_P_ZZZ__ 1024 a dn esize g m op1_neg op3_neg)
  | 2048 => (execute_FMSB_Z_P_ZZZ__ 2048 a dn esize g m op1_neg op3_neg)
  | _ => (pure ())

def decode_FNMAD_Z_P_ZZZ__ (size : (BitVec 2)) (Za : (BitVec 5)) (N : (BitVec 1)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let a := (BitVec.toNat Za)
  let op1_neg : Bool := true
  let op3_neg : Bool := true
  match VL with
  | 128 => (execute_FNMAD_Z_P_ZZZ__ 128 a dn esize g m op1_neg op3_neg)
  | 256 => (execute_FNMAD_Z_P_ZZZ__ 256 a dn esize g m op1_neg op3_neg)
  | 512 => (execute_FNMAD_Z_P_ZZZ__ 512 a dn esize g m op1_neg op3_neg)
  | 1024 => (execute_FNMAD_Z_P_ZZZ__ 1024 a dn esize g m op1_neg op3_neg)
  | 2048 => (execute_FNMAD_Z_P_ZZZ__ 2048 a dn esize g m op1_neg op3_neg)
  | _ => (pure ())

def decode_FNMSB_Z_P_ZZZ__ (size : (BitVec 2)) (Za : (BitVec 5)) (N : (BitVec 1)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let a := (BitVec.toNat Za)
  let op1_neg : Bool := false
  let op3_neg : Bool := true
  match VL with
  | 128 => (execute_FNMSB_Z_P_ZZZ__ 128 a dn esize g m op1_neg op3_neg)
  | 256 => (execute_FNMSB_Z_P_ZZZ__ 256 a dn esize g m op1_neg op3_neg)
  | 512 => (execute_FNMSB_Z_P_ZZZ__ 512 a dn esize g m op1_neg op3_neg)
  | 1024 => (execute_FNMSB_Z_P_ZZZ__ 1024 a dn esize g m op1_neg op3_neg)
  | 2048 => (execute_FNMSB_Z_P_ZZZ__ 2048 a dn esize g m op1_neg op3_neg)
  | _ => (pure ())

def decode_FADD_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FADD_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_FADD_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_FADD_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_FADD_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_FADD_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_FMUL_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FMUL_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_FMUL_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_FMUL_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_FMUL_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_FMUL_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_FSUB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FSUB_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_FSUB_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_FSUB_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_FSUB_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_FSUB_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_FTSMUL_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FTSMUL_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_FTSMUL_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_FTSMUL_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_FTSMUL_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_FTSMUL_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_FRECPS_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FRECPS_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_FRECPS_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_FRECPS_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_FRECPS_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_FRECPS_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_FRSQRTS_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FRSQRTS_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_FRSQRTS_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_FRSQRTS_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_FRSQRTS_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_FRSQRTS_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_FTSSEL_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FTSSEL_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_FTSSEL_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_FTSSEL_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_FTSSEL_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_FTSSEL_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_FEXPA_Z_Z__ (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FEXPA_Z_Z__ 128 d esize n)
  | 256 => (execute_FEXPA_Z_Z__ 256 d esize n)
  | 512 => (execute_FEXPA_Z_Z__ 512 d esize n)
  | 1024 => (execute_FEXPA_Z_Z__ 1024 d esize n)
  | 2048 => (execute_FEXPA_Z_Z__ 2048 d esize n)
  | _ => (pure ())

def decode_FTMAD_Z_ZZI__ (size : (BitVec 2)) (imm3 : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let imm := (BitVec.toNat imm3)
  match VL with
  | 128 => (execute_FTMAD_Z_ZZI__ 128 dn esize imm m)
  | 256 => (execute_FTMAD_Z_ZZI__ 256 dn esize imm m)
  | 512 => (execute_FTMAD_Z_ZZI__ 512 dn esize imm m)
  | 1024 => (execute_FTMAD_Z_ZZI__ 1024 dn esize imm m)
  | 2048 => (execute_FTMAD_Z_ZZI__ 2048 dn esize imm m)
  | _ => (pure ())

def decode_FCADD_Z_P_ZZ__ (size : (BitVec 2)) (rot : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let sub_i : Bool := (rot == 0#1)
  let sub_r : Bool := (rot == 1#1)
  match VL with
  | 128 => (execute_FCADD_Z_P_ZZ__ 128 dn esize g m sub_i sub_r)
  | 256 => (execute_FCADD_Z_P_ZZ__ 256 dn esize g m sub_i sub_r)
  | 512 => (execute_FCADD_Z_P_ZZ__ 512 dn esize g m sub_i sub_r)
  | 1024 => (execute_FCADD_Z_P_ZZ__ 1024 dn esize g m sub_i sub_r)
  | 2048 => (execute_FCADD_Z_P_ZZ__ 2048 dn esize g m sub_i sub_r)
  | _ => (pure ())

def decode_FCMLA_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (rot : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel_a := (BitVec.toNat (BitVec.join1 [(BitVec.access rot 0)]))
  let sel_b := (BitVec.toNat (Complement.complement (BitVec.join1 [(BitVec.access rot 0)])))
  let neg_i : Bool := ((BitVec.join1 [(BitVec.access rot 1)]) == 1#1)
  let neg_r : Bool := ((BitVec.join1 [(BitVec.access rot 0)]) != (BitVec.join1 [(BitVec.access rot 1)]))
  match VL with
  | 128 => (execute_FCMLA_Z_P_ZZZ__ 128 da esize g m n neg_i neg_r sel_a sel_b)
  | 256 => (execute_FCMLA_Z_P_ZZZ__ 256 da esize g m n neg_i neg_r sel_a sel_b)
  | 512 => (execute_FCMLA_Z_P_ZZZ__ 512 da esize g m n neg_i neg_r sel_a sel_b)
  | 1024 => (execute_FCMLA_Z_P_ZZZ__ 1024 da esize g m n neg_i neg_r sel_a sel_b)
  | 2048 => (execute_FCMLA_Z_P_ZZZ__ 2048 da esize g m n neg_i neg_r sel_a sel_b)
  | _ => (pure ())

def decode_FCMLA_Z_ZZZi_H (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel_a := (BitVec.toNat (BitVec.join1 [(BitVec.access rot 0)]))
  let sel_b := (BitVec.toNat (Complement.complement (BitVec.join1 [(BitVec.access rot 0)])))
  let neg_i : Bool := ((BitVec.join1 [(BitVec.access rot 1)]) == 1#1)
  let neg_r : Bool := ((BitVec.join1 [(BitVec.access rot 0)]) != (BitVec.join1 [(BitVec.access rot 1)]))
  match VL with
  | 128 => (execute_FCMLA_Z_ZZZi_H 128 da esize index m n neg_i neg_r sel_a sel_b)
  | 256 => (execute_FCMLA_Z_ZZZi_H 256 da esize index m n neg_i neg_r sel_a sel_b)
  | 512 => (execute_FCMLA_Z_ZZZi_H 512 da esize index m n neg_i neg_r sel_a sel_b)
  | 1024 => (execute_FCMLA_Z_ZZZi_H 1024 da esize index m n neg_i neg_r sel_a sel_b)
  | 2048 => (execute_FCMLA_Z_ZZZi_H 2048 da esize index m n neg_i neg_r sel_a sel_b)
  | _ => (pure ())

def decode_FCMLA_Z_ZZZi_S (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i1)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel_a := (BitVec.toNat (BitVec.join1 [(BitVec.access rot 0)]))
  let sel_b := (BitVec.toNat (Complement.complement (BitVec.join1 [(BitVec.access rot 0)])))
  let neg_i : Bool := ((BitVec.join1 [(BitVec.access rot 1)]) == 1#1)
  let neg_r : Bool := ((BitVec.join1 [(BitVec.access rot 0)]) != (BitVec.join1 [(BitVec.access rot 1)]))
  match VL with
  | 128 => (execute_FCMLA_Z_ZZZi_S 128 da esize index m n neg_i neg_r sel_a sel_b)
  | 256 => (execute_FCMLA_Z_ZZZi_S 256 da esize index m n neg_i neg_r sel_a sel_b)
  | 512 => (execute_FCMLA_Z_ZZZi_S 512 da esize index m n neg_i neg_r sel_a sel_b)
  | 1024 => (execute_FCMLA_Z_ZZZi_S 1024 da esize index m n neg_i neg_r sel_a sel_b)
  | 2048 => (execute_FCMLA_Z_ZZZi_S 2048 da esize index m n neg_i neg_r sel_a sel_b)
  | _ => (pure ())

def decode_FMUL_Z_ZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FMUL_Z_ZZi_H 128 d esize index m n)
  | 256 => (execute_FMUL_Z_ZZi_H 256 d esize index m n)
  | 512 => (execute_FMUL_Z_ZZi_H 512 d esize index m n)
  | 1024 => (execute_FMUL_Z_ZZi_H 1024 d esize index m n)
  | 2048 => (execute_FMUL_Z_ZZi_H 2048 d esize index m n)
  | _ => (pure ())

def decode_FMLA_Z_ZZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := false
  let op3_neg : Bool := false
  match VL with
  | 128 => (execute_FMLA_Z_ZZZi_H 128 da esize index m n op1_neg op3_neg)
  | 256 => (execute_FMLA_Z_ZZZi_H 256 da esize index m n op1_neg op3_neg)
  | 512 => (execute_FMLA_Z_ZZZi_H 512 da esize index m n op1_neg op3_neg)
  | 1024 => (execute_FMLA_Z_ZZZi_H 1024 da esize index m n op1_neg op3_neg)
  | 2048 => (execute_FMLA_Z_ZZZi_H 2048 da esize index m n op1_neg op3_neg)
  | _ => (pure ())

def decode_FMLS_Z_ZZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  let op3_neg : Bool := false
  match VL with
  | 128 => (execute_FMLS_Z_ZZZi_H 128 da esize index m n op1_neg op3_neg)
  | 256 => (execute_FMLS_Z_ZZZi_H 256 da esize index m n op1_neg op3_neg)
  | 512 => (execute_FMLS_Z_ZZZi_H 512 da esize index m n op1_neg op3_neg)
  | 1024 => (execute_FMLS_Z_ZZZi_H 1024 da esize index m n op1_neg op3_neg)
  | 2048 => (execute_FMLS_Z_ZZZi_H 2048 da esize index m n op1_neg op3_neg)
  | _ => (pure ())

def decode_FMUL_Z_ZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FMUL_Z_ZZi_S 128 d esize index m n)
  | 256 => (execute_FMUL_Z_ZZi_S 256 d esize index m n)
  | 512 => (execute_FMUL_Z_ZZi_S 512 d esize index m n)
  | 1024 => (execute_FMUL_Z_ZZi_S 1024 d esize index m n)
  | 2048 => (execute_FMUL_Z_ZZi_S 2048 d esize index m n)
  | _ => (pure ())

def decode_FMLA_Z_ZZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := false
  let op3_neg : Bool := false
  match VL with
  | 128 => (execute_FMLA_Z_ZZZi_S 128 da esize index m n op1_neg op3_neg)
  | 256 => (execute_FMLA_Z_ZZZi_S 256 da esize index m n op1_neg op3_neg)
  | 512 => (execute_FMLA_Z_ZZZi_S 512 da esize index m n op1_neg op3_neg)
  | 1024 => (execute_FMLA_Z_ZZZi_S 1024 da esize index m n op1_neg op3_neg)
  | 2048 => (execute_FMLA_Z_ZZZi_S 2048 da esize index m n op1_neg op3_neg)
  | _ => (pure ())

def decode_FMLS_Z_ZZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  let op3_neg : Bool := false
  match VL with
  | 128 => (execute_FMLS_Z_ZZZi_S 128 da esize index m n op1_neg op3_neg)
  | 256 => (execute_FMLS_Z_ZZZi_S 256 da esize index m n op1_neg op3_neg)
  | 512 => (execute_FMLS_Z_ZZZi_S 512 da esize index m n op1_neg op3_neg)
  | 1024 => (execute_FMLS_Z_ZZZi_S 1024 da esize index m n op1_neg op3_neg)
  | 2048 => (execute_FMLS_Z_ZZZi_S 2048 da esize index m n op1_neg op3_neg)
  | _ => (pure ())

def decode_FMUL_Z_ZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let index := (BitVec.toNat i1)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FMUL_Z_ZZi_D 128 d esize index m n)
  | 256 => (execute_FMUL_Z_ZZi_D 256 d esize index m n)
  | 512 => (execute_FMUL_Z_ZZi_D 512 d esize index m n)
  | 1024 => (execute_FMUL_Z_ZZi_D 1024 d esize index m n)
  | 2048 => (execute_FMUL_Z_ZZi_D 2048 d esize index m n)
  | _ => (pure ())

def decode_FMLA_Z_ZZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (op : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let index := (BitVec.toNat i1)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := false
  let op3_neg : Bool := false
  match VL with
  | 128 => (execute_FMLA_Z_ZZZi_D 128 da esize index m n op1_neg op3_neg)
  | 256 => (execute_FMLA_Z_ZZZi_D 256 da esize index m n op1_neg op3_neg)
  | 512 => (execute_FMLA_Z_ZZZi_D 512 da esize index m n op1_neg op3_neg)
  | 1024 => (execute_FMLA_Z_ZZZi_D 1024 da esize index m n op1_neg op3_neg)
  | 2048 => (execute_FMLA_Z_ZZZi_D 2048 da esize index m n op1_neg op3_neg)
  | _ => (pure ())

def decode_FMLS_Z_ZZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (op : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let index := (BitVec.toNat i1)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  let op3_neg : Bool := false
  match VL with
  | 128 => (execute_FMLS_Z_ZZZi_D 128 da esize index m n op1_neg op3_neg)
  | 256 => (execute_FMLS_Z_ZZZi_D 256 da esize index m n op1_neg op3_neg)
  | 512 => (execute_FMLS_Z_ZZZi_D 512 da esize index m n op1_neg op3_neg)
  | 1024 => (execute_FMLS_Z_ZZZi_D 1024 da esize index m n op1_neg op3_neg)
  | 2048 => (execute_FMLS_Z_ZZZi_D 2048 da esize index m n op1_neg op3_neg)
  | _ => (pure ())

def decode_FADDP_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let m := (BitVec.toNat Zm)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_FADDP_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FADDP_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FADDP_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FADDP_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FADDP_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FMAXNMP_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let m := (BitVec.toNat Zm)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_FMAXNMP_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FMAXNMP_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FMAXNMP_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FMAXNMP_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FMAXNMP_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FMAXP_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let m := (BitVec.toNat Zm)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_FMAXP_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FMAXP_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FMAXP_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FMAXP_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FMAXP_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FMINNMP_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let m := (BitVec.toNat Zm)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_FMINNMP_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FMINNMP_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FMINNMP_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FMINNMP_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FMINNMP_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FMINP_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let m := (BitVec.toNat Zm)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_FMINP_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_FMINP_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_FMINP_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_FMINP_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_FMINP_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_FMLALB_Z_ZZZ__ (o2 : (BitVec 1)) (Zm : (BitVec 5)) (op : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := false
  match VL with
  | 128 => (execute_FMLALB_Z_ZZZ__ 128 da esize m n op1_neg)
  | 256 => (execute_FMLALB_Z_ZZZ__ 256 da esize m n op1_neg)
  | 512 => (execute_FMLALB_Z_ZZZ__ 512 da esize m n op1_neg)
  | 1024 => (execute_FMLALB_Z_ZZZ__ 1024 da esize m n op1_neg)
  | 2048 => (execute_FMLALB_Z_ZZZ__ 2048 da esize m n op1_neg)
  | _ => (pure ())

def decode_FMLALT_Z_ZZZ__ (o2 : (BitVec 1)) (Zm : (BitVec 5)) (op : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := false
  match VL with
  | 128 => (execute_FMLALT_Z_ZZZ__ 128 da esize m n op1_neg)
  | 256 => (execute_FMLALT_Z_ZZZ__ 256 da esize m n op1_neg)
  | 512 => (execute_FMLALT_Z_ZZZ__ 512 da esize m n op1_neg)
  | 1024 => (execute_FMLALT_Z_ZZZ__ 1024 da esize m n op1_neg)
  | 2048 => (execute_FMLALT_Z_ZZZ__ 2048 da esize m n op1_neg)
  | _ => (pure ())

def decode_FMLSLB_Z_ZZZ__ (o2 : (BitVec 1)) (Zm : (BitVec 5)) (op : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  match VL with
  | 128 => (execute_FMLSLB_Z_ZZZ__ 128 da esize m n op1_neg)
  | 256 => (execute_FMLSLB_Z_ZZZ__ 256 da esize m n op1_neg)
  | 512 => (execute_FMLSLB_Z_ZZZ__ 512 da esize m n op1_neg)
  | 1024 => (execute_FMLSLB_Z_ZZZ__ 1024 da esize m n op1_neg)
  | 2048 => (execute_FMLSLB_Z_ZZZ__ 2048 da esize m n op1_neg)
  | _ => (pure ())

def decode_FMLSLT_Z_ZZZ__ (o2 : (BitVec 1)) (Zm : (BitVec 5)) (op : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  match VL with
  | 128 => (execute_FMLSLT_Z_ZZZ__ 128 da esize m n op1_neg)
  | 256 => (execute_FMLSLT_Z_ZZZ__ 256 da esize m n op1_neg)
  | 512 => (execute_FMLSLT_Z_ZZZ__ 512 da esize m n op1_neg)
  | 1024 => (execute_FMLSLT_Z_ZZZ__ 1024 da esize m n op1_neg)
  | 2048 => (execute_FMLSLT_Z_ZZZ__ 2048 da esize m n op1_neg)
  | _ => (pure ())

def decode_FMLALB_Z_ZZZi_S (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let index := (BitVec.toNat (i3h +++ i3l))
  let op1_neg : Bool := false
  match VL with
  | 128 => (execute_FMLALB_Z_ZZZi_S 128 da esize index m n op1_neg)
  | 256 => (execute_FMLALB_Z_ZZZi_S 256 da esize index m n op1_neg)
  | 512 => (execute_FMLALB_Z_ZZZi_S 512 da esize index m n op1_neg)
  | 1024 => (execute_FMLALB_Z_ZZZi_S 1024 da esize index m n op1_neg)
  | 2048 => (execute_FMLALB_Z_ZZZi_S 2048 da esize index m n op1_neg)
  | _ => (pure ())

def decode_FMLALT_Z_ZZZi_S (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let index := (BitVec.toNat (i3h +++ i3l))
  let op1_neg : Bool := false
  match VL with
  | 128 => (execute_FMLALT_Z_ZZZi_S 128 da esize index m n op1_neg)
  | 256 => (execute_FMLALT_Z_ZZZi_S 256 da esize index m n op1_neg)
  | 512 => (execute_FMLALT_Z_ZZZi_S 512 da esize index m n op1_neg)
  | 1024 => (execute_FMLALT_Z_ZZZi_S 1024 da esize index m n op1_neg)
  | 2048 => (execute_FMLALT_Z_ZZZi_S 2048 da esize index m n op1_neg)
  | _ => (pure ())

def decode_FMLSLB_Z_ZZZi_S (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let index := (BitVec.toNat (i3h +++ i3l))
  let op1_neg : Bool := true
  match VL with
  | 128 => (execute_FMLSLB_Z_ZZZi_S 128 da esize index m n op1_neg)
  | 256 => (execute_FMLSLB_Z_ZZZi_S 256 da esize index m n op1_neg)
  | 512 => (execute_FMLSLB_Z_ZZZi_S 512 da esize index m n op1_neg)
  | 1024 => (execute_FMLSLB_Z_ZZZi_S 1024 da esize index m n op1_neg)
  | 2048 => (execute_FMLSLB_Z_ZZZi_S 2048 da esize index m n op1_neg)
  | _ => (pure ())

def decode_FMLSLT_Z_ZZZi_S (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let index := (BitVec.toNat (i3h +++ i3l))
  let op1_neg : Bool := true
  match VL with
  | 128 => (execute_FMLSLT_Z_ZZZi_S 128 da esize index m n op1_neg)
  | 256 => (execute_FMLSLT_Z_ZZZi_S 256 da esize index m n op1_neg)
  | 512 => (execute_FMLSLT_Z_ZZZi_S 512 da esize index m n op1_neg)
  | 1024 => (execute_FMLSLT_Z_ZZZi_S 1024 da esize index m n op1_neg)
  | 2048 => (execute_FMLSLT_Z_ZZZi_S 2048 da esize index m n op1_neg)
  | _ => (pure ())

def decode_BFMLALB_Z_ZZZ__ (o2 : (BitVec 1)) (Zm : (BitVec 5)) (op : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))) <||> (do
       (pure (! (← (HaveBF16Ext ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_BFMLALB_Z_ZZZ__ 128 da m n)
  | 256 => (execute_BFMLALB_Z_ZZZ__ 256 da m n)
  | 512 => (execute_BFMLALB_Z_ZZZ__ 512 da m n)
  | 1024 => (execute_BFMLALB_Z_ZZZ__ 1024 da m n)
  | 2048 => (execute_BFMLALB_Z_ZZZ__ 2048 da m n)
  | _ => (pure ())

def decode_BFMLALT_Z_ZZZ__ (o2 : (BitVec 1)) (Zm : (BitVec 5)) (op : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))) <||> (do
       (pure (! (← (HaveBF16Ext ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_BFMLALT_Z_ZZZ__ 128 da m n)
  | 256 => (execute_BFMLALT_Z_ZZZ__ 256 da m n)
  | 512 => (execute_BFMLALT_Z_ZZZ__ 512 da m n)
  | 1024 => (execute_BFMLALT_Z_ZZZ__ 1024 da m n)
  | 2048 => (execute_BFMLALT_Z_ZZZ__ 2048 da m n)
  | _ => (pure ())

def decode_BFMLSLB_Z_ZZZ__ (o2 : (BitVec 1)) (Zm : (BitVec 5)) (op : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  match VL with
  | 128 => (execute_BFMLSLB_Z_ZZZ__ 128 da m n op1_neg)
  | 256 => (execute_BFMLSLB_Z_ZZZ__ 256 da m n op1_neg)
  | 512 => (execute_BFMLSLB_Z_ZZZ__ 512 da m n op1_neg)
  | 1024 => (execute_BFMLSLB_Z_ZZZ__ 1024 da m n op1_neg)
  | 2048 => (execute_BFMLSLB_Z_ZZZ__ 2048 da m n op1_neg)
  | _ => (pure ())

def decode_BFMLSLT_Z_ZZZ__ (o2 : (BitVec 1)) (Zm : (BitVec 5)) (op : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  match VL with
  | 128 => (execute_BFMLSLT_Z_ZZZ__ 128 da m n op1_neg)
  | 256 => (execute_BFMLSLT_Z_ZZZ__ 256 da m n op1_neg)
  | 512 => (execute_BFMLSLT_Z_ZZZ__ 512 da m n op1_neg)
  | 1024 => (execute_BFMLSLT_Z_ZZZ__ 1024 da m n op1_neg)
  | 2048 => (execute_BFMLSLT_Z_ZZZ__ 2048 da m n op1_neg)
  | _ => (pure ())

def decode_BFMLALB_Z_ZZZi__ (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))) <||> (do
       (pure (! (← (HaveBF16Ext ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let index := (BitVec.toNat (i3h +++ i3l))
  match VL with
  | 128 => (execute_BFMLALB_Z_ZZZi__ 128 da index m n)
  | 256 => (execute_BFMLALB_Z_ZZZi__ 256 da index m n)
  | 512 => (execute_BFMLALB_Z_ZZZi__ 512 da index m n)
  | 1024 => (execute_BFMLALB_Z_ZZZi__ 1024 da index m n)
  | 2048 => (execute_BFMLALB_Z_ZZZi__ 2048 da index m n)
  | _ => (pure ())

def decode_BFMLALT_Z_ZZZi__ (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))) <||> (do
       (pure (! (← (HaveBF16Ext ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let index := (BitVec.toNat (i3h +++ i3l))
  match VL with
  | 128 => (execute_BFMLALT_Z_ZZZi__ 128 da index m n)
  | 256 => (execute_BFMLALT_Z_ZZZi__ 256 da index m n)
  | 512 => (execute_BFMLALT_Z_ZZZi__ 512 da index m n)
  | 1024 => (execute_BFMLALT_Z_ZZZi__ 1024 da index m n)
  | 2048 => (execute_BFMLALT_Z_ZZZi__ 2048 da index m n)
  | _ => (pure ())

def decode_BFMLSLB_Z_ZZZi__ (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let index := (BitVec.toNat (i3h +++ i3l))
  let op1_neg : Bool := true
  match VL with
  | 128 => (execute_BFMLSLB_Z_ZZZi__ 128 da index m n op1_neg)
  | 256 => (execute_BFMLSLB_Z_ZZZi__ 256 da index m n op1_neg)
  | 512 => (execute_BFMLSLB_Z_ZZZi__ 512 da index m n op1_neg)
  | 1024 => (execute_BFMLSLB_Z_ZZZi__ 1024 da index m n op1_neg)
  | 2048 => (execute_BFMLSLB_Z_ZZZi__ 2048 da index m n op1_neg)
  | _ => (pure ())

def decode_BFMLSLT_Z_ZZZi__ (o2 : (BitVec 1)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let index := (BitVec.toNat (i3h +++ i3l))
  let op1_neg : Bool := true
  match VL with
  | 128 => (execute_BFMLSLT_Z_ZZZi__ 128 da index m n op1_neg)
  | 256 => (execute_BFMLSLT_Z_ZZZi__ 256 da index m n op1_neg)
  | 512 => (execute_BFMLSLT_Z_ZZZi__ 512 da index m n op1_neg)
  | 1024 => (execute_BFMLSLT_Z_ZZZi__ 1024 da index m n op1_neg)
  | 2048 => (execute_BFMLSLT_Z_ZZZi__ 2048 da index m n op1_neg)
  | _ => (pure ())

def decode_BFDOT_Z_ZZZ__ (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))) <||> (do
       (pure (! (← (HaveBF16Ext ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_BFDOT_Z_ZZZ__ 128 da m n)
  | 256 => (execute_BFDOT_Z_ZZZ__ 256 da m n)
  | 512 => (execute_BFDOT_Z_ZZZ__ 512 da m n)
  | 1024 => (execute_BFDOT_Z_ZZZ__ 1024 da m n)
  | 2048 => (execute_BFDOT_Z_ZZZ__ 2048 da m n)
  | _ => (pure ())

def decode_BFDOT_Z_ZZZi__ (i2 : (BitVec 2)) (Zm : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))) <||> (do
       (pure (! (← (HaveBF16Ext ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let index := (BitVec.toNat i2)
  match VL with
  | 128 => (execute_BFDOT_Z_ZZZi__ 128 da index m n)
  | 256 => (execute_BFDOT_Z_ZZZi__ 256 da index m n)
  | 512 => (execute_BFDOT_Z_ZZZi__ 512 da index m n)
  | 1024 => (execute_BFDOT_Z_ZZZi__ 1024 da index m n)
  | 2048 => (execute_BFDOT_Z_ZZZi__ 2048 da index m n)
  | _ => (pure ())

def decode_FDOT_Z_ZZZ__ (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_FDOT_Z_ZZZ__ 128 da m n)
  | 256 => (execute_FDOT_Z_ZZZ__ 256 da m n)
  | 512 => (execute_FDOT_Z_ZZZ__ 512 da m n)
  | 1024 => (execute_FDOT_Z_ZZZ__ 1024 da m n)
  | 2048 => (execute_FDOT_Z_ZZZ__ 2048 da m n)
  | _ => (pure ())

def decode_FDOT_Z_ZZZi__ (i2 : (BitVec 2)) (Zm : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let index := (BitVec.toNat i2)
  match VL with
  | 128 => (execute_FDOT_Z_ZZZi__ 128 da index m n)
  | 256 => (execute_FDOT_Z_ZZZi__ 256 da index m n)
  | 512 => (execute_FDOT_Z_ZZZi__ 512 da index m n)
  | 1024 => (execute_FDOT_Z_ZZZi__ 1024 da index m n)
  | 2048 => (execute_FDOT_Z_ZZZi__ 2048 da index m n)
  | _ => (pure ())

def decode_BFCVT_Z_P_Z_S2BF (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))) <||> (do
       (pure (! (← (HaveBF16Ext ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_BFCVT_Z_P_Z_S2BF 128 d g n)
  | 256 => (execute_BFCVT_Z_P_Z_S2BF 256 d g n)
  | 512 => (execute_BFCVT_Z_P_Z_S2BF 512 d g n)
  | 1024 => (execute_BFCVT_Z_P_Z_S2BF 1024 d g n)
  | 2048 => (execute_BFCVT_Z_P_Z_S2BF 2048 d g n)
  | _ => (pure ())

def decode_BFCVTNT_Z_P_Z_S2BF (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))) <||> (do
       (pure (! (← (HaveBF16Ext ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_BFCVTNT_Z_P_Z_S2BF 128 d g n)
  | 256 => (execute_BFCVTNT_Z_P_Z_S2BF 256 d g n)
  | 512 => (execute_BFCVTNT_Z_P_Z_S2BF 512 d g n)
  | 1024 => (execute_BFCVTNT_Z_P_Z_S2BF 1024 d g n)
  | 2048 => (execute_BFCVTNT_Z_P_Z_S2BF 2048 d g n)
  | _ => (pure ())

def decode_FMMLA_Z_ZZZ_S (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVEFP32MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_FMMLA_Z_ZZZ_S 128 da esize m n)
  | 256 => (execute_FMMLA_Z_ZZZ_S 256 da esize m n)
  | 512 => (execute_FMMLA_Z_ZZZ_S 512 da esize m n)
  | 1024 => (execute_FMMLA_Z_ZZZ_S 1024 da esize m n)
  | 2048 => (execute_FMMLA_Z_ZZZ_S 2048 da esize m n)
  | _ => (pure ())

def decode_FMMLA_Z_ZZZ_D (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVEFP64MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_FMMLA_Z_ZZZ_D 128 da esize m n)
  | 256 => (execute_FMMLA_Z_ZZZ_D 256 da esize m n)
  | 512 => (execute_FMMLA_Z_ZZZ_D 512 da esize m n)
  | 1024 => (execute_FMMLA_Z_ZZZ_D 1024 da esize m n)
  | 2048 => (execute_FMMLA_Z_ZZZ_D 2048 da esize m n)
  | _ => (pure ())

def decode_BFMMLA_Z_ZZZ__ (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveBF16Ext ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_BFMMLA_Z_ZZZ__ 128 da m n)
  | 256 => (execute_BFMMLA_Z_ZZZ__ 256 da m n)
  | 512 => (execute_BFMMLA_Z_ZZZ__ 512 da m n)
  | 1024 => (execute_BFMMLA_Z_ZZZ__ 1024 da m n)
  | 2048 => (execute_BFMMLA_Z_ZZZ__ 2048 da m n)
  | _ => (pure ())

def decode_FLOGB_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FLOGB_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_FLOGB_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_FLOGB_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_FLOGB_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_FLOGB_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_FCVTNT_Z_P_Z_D2S (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FCVTNT_Z_P_Z_D2S 128 d esize g n)
  | 256 => (execute_FCVTNT_Z_P_Z_D2S 256 d esize g n)
  | 512 => (execute_FCVTNT_Z_P_Z_D2S 512 d esize g n)
  | 1024 => (execute_FCVTNT_Z_P_Z_D2S 1024 d esize g n)
  | 2048 => (execute_FCVTNT_Z_P_Z_D2S 2048 d esize g n)
  | _ => (pure ())

def decode_FCVTNT_Z_P_Z_S2H (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FCVTNT_Z_P_Z_S2H 128 d esize g n)
  | 256 => (execute_FCVTNT_Z_P_Z_S2H 256 d esize g n)
  | 512 => (execute_FCVTNT_Z_P_Z_S2H 512 d esize g n)
  | 1024 => (execute_FCVTNT_Z_P_Z_S2H 1024 d esize g n)
  | 2048 => (execute_FCVTNT_Z_P_Z_S2H 2048 d esize g n)
  | _ => (pure ())

def decode_FCVTLT_Z_P_Z_S2D (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FCVTLT_Z_P_Z_S2D 128 d esize g n)
  | 256 => (execute_FCVTLT_Z_P_Z_S2D 256 d esize g n)
  | 512 => (execute_FCVTLT_Z_P_Z_S2D 512 d esize g n)
  | 1024 => (execute_FCVTLT_Z_P_Z_S2D 1024 d esize g n)
  | 2048 => (execute_FCVTLT_Z_P_Z_S2D 2048 d esize g n)
  | _ => (pure ())

def decode_FCVTLT_Z_P_Z_H2S (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FCVTLT_Z_P_Z_H2S 128 d esize g n)
  | 256 => (execute_FCVTLT_Z_P_Z_H2S 256 d esize g n)
  | 512 => (execute_FCVTLT_Z_P_Z_H2S 512 d esize g n)
  | 1024 => (execute_FCVTLT_Z_P_Z_H2S 1024 d esize g n)
  | 2048 => (execute_FCVTLT_Z_P_Z_H2S 2048 d esize g n)
  | _ => (pure ())

def decode_FCVTX_Z_P_Z_D2S (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let s_esize := 64
  let d_esize := 32
  match VL with
  | 128 => (execute_FCVTX_Z_P_Z_D2S 128 d d_esize esize g n s_esize)
  | 256 => (execute_FCVTX_Z_P_Z_D2S 256 d d_esize esize g n s_esize)
  | 512 => (execute_FCVTX_Z_P_Z_D2S 512 d d_esize esize g n s_esize)
  | 1024 => (execute_FCVTX_Z_P_Z_D2S 1024 d d_esize esize g n s_esize)
  | 2048 => (execute_FCVTX_Z_P_Z_D2S 2048 d d_esize esize g n s_esize)
  | _ => (pure ())

def decode_FCVTXNT_Z_P_Z_D2S (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FCVTXNT_Z_P_Z_D2S 128 d esize g n)
  | 256 => (execute_FCVTXNT_Z_P_Z_D2S 256 d esize g n)
  | 512 => (execute_FCVTXNT_Z_P_Z_D2S 512 d esize g n)
  | 1024 => (execute_FCVTXNT_Z_P_Z_D2S 1024 d esize g n)
  | 2048 => (execute_FCVTXNT_Z_P_Z_D2S 2048 d esize g n)
  | _ => (pure ())

def decode_FCLAMP_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FCLAMP_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_FCLAMP_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_FCLAMP_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_FCLAMP_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_FCLAMP_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_FADDQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_FADDQV_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_FADDQV_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_FADDQV_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_FADDQV_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_FADDQV_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_FMAXNMQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_FMAXNMQV_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_FMAXNMQV_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_FMAXNMQV_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_FMAXNMQV_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_FMAXNMQV_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_FMINNMQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_FMINNMQV_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_FMINNMQV_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_FMINNMQV_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_FMINNMQV_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_FMINNMQV_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_FMAXQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_FMAXQV_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_FMAXQV_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_FMAXQV_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_FMAXQV_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_FMAXQV_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_FMINQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_FMINQV_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_FMINQV_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_FMINQV_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_FMINQV_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_FMINQV_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_BFADD_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_BFADD_Z_ZZ__ 128 d m n)
  | 256 => (execute_BFADD_Z_ZZ__ 256 d m n)
  | 512 => (execute_BFADD_Z_ZZ__ 512 d m n)
  | 1024 => (execute_BFADD_Z_ZZ__ 1024 d m n)
  | 2048 => (execute_BFADD_Z_ZZ__ 2048 d m n)
  | _ => (pure ())

def decode_BFMUL_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_BFMUL_Z_ZZ__ 128 d m n)
  | 256 => (execute_BFMUL_Z_ZZ__ 256 d m n)
  | 512 => (execute_BFMUL_Z_ZZ__ 512 d m n)
  | 1024 => (execute_BFMUL_Z_ZZ__ 1024 d m n)
  | 2048 => (execute_BFMUL_Z_ZZ__ 2048 d m n)
  | _ => (pure ())

def decode_BFSUB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_BFSUB_Z_ZZ__ 128 d m n)
  | 256 => (execute_BFSUB_Z_ZZ__ 256 d m n)
  | 512 => (execute_BFSUB_Z_ZZ__ 512 d m n)
  | 1024 => (execute_BFSUB_Z_ZZ__ 1024 d m n)
  | 2048 => (execute_BFSUB_Z_ZZ__ 2048 d m n)
  | _ => (pure ())

def decode_BFADD_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_BFADD_Z_P_ZZ__ 128 dn g m)
  | 256 => (execute_BFADD_Z_P_ZZ__ 256 dn g m)
  | 512 => (execute_BFADD_Z_P_ZZ__ 512 dn g m)
  | 1024 => (execute_BFADD_Z_P_ZZ__ 1024 dn g m)
  | 2048 => (execute_BFADD_Z_P_ZZ__ 2048 dn g m)
  | _ => (pure ())

def decode_BFMUL_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_BFMUL_Z_P_ZZ__ 128 dn g m)
  | 256 => (execute_BFMUL_Z_P_ZZ__ 256 dn g m)
  | 512 => (execute_BFMUL_Z_P_ZZ__ 512 dn g m)
  | 1024 => (execute_BFMUL_Z_P_ZZ__ 1024 dn g m)
  | 2048 => (execute_BFMUL_Z_P_ZZ__ 2048 dn g m)
  | _ => (pure ())

def decode_BFSUB_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_BFSUB_Z_P_ZZ__ 128 dn g m)
  | 256 => (execute_BFSUB_Z_P_ZZ__ 256 dn g m)
  | 512 => (execute_BFSUB_Z_P_ZZ__ 512 dn g m)
  | 1024 => (execute_BFSUB_Z_P_ZZ__ 1024 dn g m)
  | 2048 => (execute_BFSUB_Z_P_ZZ__ 2048 dn g m)
  | _ => (pure ())

def decode_BFMLA_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := false
  let op3_neg : Bool := false
  match VL with
  | 128 => (execute_BFMLA_Z_P_ZZZ__ 128 da g m n op1_neg op3_neg)
  | 256 => (execute_BFMLA_Z_P_ZZZ__ 256 da g m n op1_neg op3_neg)
  | 512 => (execute_BFMLA_Z_P_ZZZ__ 512 da g m n op1_neg op3_neg)
  | 1024 => (execute_BFMLA_Z_P_ZZZ__ 1024 da g m n op1_neg op3_neg)
  | 2048 => (execute_BFMLA_Z_P_ZZZ__ 2048 da g m n op1_neg op3_neg)
  | _ => (pure ())

def decode_BFMLS_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  let op3_neg : Bool := false
  match VL with
  | 128 => (execute_BFMLS_Z_P_ZZZ__ 128 da g m n op1_neg op3_neg)
  | 256 => (execute_BFMLS_Z_P_ZZZ__ 256 da g m n op1_neg op3_neg)
  | 512 => (execute_BFMLS_Z_P_ZZZ__ 512 da g m n op1_neg op3_neg)
  | 1024 => (execute_BFMLS_Z_P_ZZZ__ 1024 da g m n op1_neg op3_neg)
  | 2048 => (execute_BFMLS_Z_P_ZZZ__ 2048 da g m n op1_neg op3_neg)
  | _ => (pure ())

def decode_BFMLA_Z_ZZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := false
  let op3_neg : Bool := false
  match VL with
  | 128 => (execute_BFMLA_Z_ZZZi_H 128 da index m n op1_neg op3_neg)
  | 256 => (execute_BFMLA_Z_ZZZi_H 256 da index m n op1_neg op3_neg)
  | 512 => (execute_BFMLA_Z_ZZZi_H 512 da index m n op1_neg op3_neg)
  | 1024 => (execute_BFMLA_Z_ZZZi_H 1024 da index m n op1_neg op3_neg)
  | 2048 => (execute_BFMLA_Z_ZZZi_H 2048 da index m n op1_neg op3_neg)
  | _ => (pure ())

def decode_BFMLS_Z_ZZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  let op3_neg : Bool := false
  match VL with
  | 128 => (execute_BFMLS_Z_ZZZi_H 128 da index m n op1_neg op3_neg)
  | 256 => (execute_BFMLS_Z_ZZZi_H 256 da index m n op1_neg op3_neg)
  | 512 => (execute_BFMLS_Z_ZZZi_H 512 da index m n op1_neg op3_neg)
  | 1024 => (execute_BFMLS_Z_ZZZi_H 1024 da index m n op1_neg op3_neg)
  | 2048 => (execute_BFMLS_Z_ZZZi_H 2048 da index m n op1_neg op3_neg)
  | _ => (pure ())

def decode_BFMUL_Z_ZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_BFMUL_Z_ZZi_H 128 d index m n)
  | 256 => (execute_BFMUL_Z_ZZi_H 256 d index m n)
  | 512 => (execute_BFMUL_Z_ZZi_H 512 d index m n)
  | 1024 => (execute_BFMUL_Z_ZZi_H 1024 d index m n)
  | 2048 => (execute_BFMUL_Z_ZZi_H 2048 d index m n)
  | _ => (pure ())

def decode_BFMAXNM_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_BFMAXNM_Z_P_ZZ__ 128 dn g m)
  | 256 => (execute_BFMAXNM_Z_P_ZZ__ 256 dn g m)
  | 512 => (execute_BFMAXNM_Z_P_ZZ__ 512 dn g m)
  | 1024 => (execute_BFMAXNM_Z_P_ZZ__ 1024 dn g m)
  | 2048 => (execute_BFMAXNM_Z_P_ZZ__ 2048 dn g m)
  | _ => (pure ())

def decode_BFMINNM_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_BFMINNM_Z_P_ZZ__ 128 dn g m)
  | 256 => (execute_BFMINNM_Z_P_ZZ__ 256 dn g m)
  | 512 => (execute_BFMINNM_Z_P_ZZ__ 512 dn g m)
  | 1024 => (execute_BFMINNM_Z_P_ZZ__ 1024 dn g m)
  | 2048 => (execute_BFMINNM_Z_P_ZZ__ 2048 dn g m)
  | _ => (pure ())

def decode_BFMAX_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_BFMAX_Z_P_ZZ__ 128 dn g m)
  | 256 => (execute_BFMAX_Z_P_ZZ__ 256 dn g m)
  | 512 => (execute_BFMAX_Z_P_ZZ__ 512 dn g m)
  | 1024 => (execute_BFMAX_Z_P_ZZ__ 1024 dn g m)
  | 2048 => (execute_BFMAX_Z_P_ZZ__ 2048 dn g m)
  | _ => (pure ())

def decode_BFMIN_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_BFMIN_Z_P_ZZ__ 128 dn g m)
  | 256 => (execute_BFMIN_Z_P_ZZ__ 256 dn g m)
  | 512 => (execute_BFMIN_Z_P_ZZ__ 512 dn g m)
  | 1024 => (execute_BFMIN_Z_P_ZZ__ 1024 dn g m)
  | 2048 => (execute_BFMIN_Z_P_ZZ__ 2048 dn g m)
  | _ => (pure ())

def decode_BFCLAMP_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVEB16B16 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_BFCLAMP_Z_ZZ__ 128 d m n)
  | 256 => (execute_BFCLAMP_Z_ZZ__ 256 d m n)
  | 512 => (execute_BFCLAMP_Z_ZZ__ 512 d m n)
  | 1024 => (execute_BFCLAMP_Z_ZZ__ 1024 d m n)
  | 2048 => (execute_BFCLAMP_Z_ZZ__ 2048 d m n)
  | _ => (pure ())

def decode_ADR_Z_AZ_D_u32_scaled (Zm : (BitVec 5)) (msz : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let osize := 32
  let is_unsigned : Bool := true
  let mbytes := (Int.shiftl 1 (BitVec.toNat msz))
  match VL with
  | 128 => (execute_ADR_Z_AZ_D_u32_scaled 128 d esize m mbytes n osize is_unsigned)
  | 256 => (execute_ADR_Z_AZ_D_u32_scaled 256 d esize m mbytes n osize is_unsigned)
  | 512 => (execute_ADR_Z_AZ_D_u32_scaled 512 d esize m mbytes n osize is_unsigned)
  | 1024 => (execute_ADR_Z_AZ_D_u32_scaled 1024 d esize m mbytes n osize is_unsigned)
  | 2048 => (execute_ADR_Z_AZ_D_u32_scaled 2048 d esize m mbytes n osize is_unsigned)
  | _ => (pure ())

def decode_ADR_Z_AZ_D_s32_scaled (Zm : (BitVec 5)) (msz : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let osize := 32
  let is_unsigned : Bool := false
  let mbytes := (Int.shiftl 1 (BitVec.toNat msz))
  match VL with
  | 128 => (execute_ADR_Z_AZ_D_s32_scaled 128 d esize m mbytes n osize is_unsigned)
  | 256 => (execute_ADR_Z_AZ_D_s32_scaled 256 d esize m mbytes n osize is_unsigned)
  | 512 => (execute_ADR_Z_AZ_D_s32_scaled 512 d esize m mbytes n osize is_unsigned)
  | 1024 => (execute_ADR_Z_AZ_D_s32_scaled 1024 d esize m mbytes n osize is_unsigned)
  | 2048 => (execute_ADR_Z_AZ_D_s32_scaled 2048 d esize m mbytes n osize is_unsigned)
  | _ => (pure ())

def decode_ADR_Z_AZ_SD_same_scaled (sz : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let osize := esize
  let is_unsigned : Bool := true
  let mbytes := (Int.shiftl 1 (BitVec.toNat msz))
  match VL with
  | 128 => (execute_ADR_Z_AZ_SD_same_scaled 128 d esize m mbytes n osize is_unsigned)
  | 256 => (execute_ADR_Z_AZ_SD_same_scaled 256 d esize m mbytes n osize is_unsigned)
  | 512 => (execute_ADR_Z_AZ_SD_same_scaled 512 d esize m mbytes n osize is_unsigned)
  | 1024 => (execute_ADR_Z_AZ_SD_same_scaled 1024 d esize m mbytes n osize is_unsigned)
  | 2048 => (execute_ADR_Z_AZ_SD_same_scaled 2048 d esize m mbytes n osize is_unsigned)
  | _ => (pure ())

def decode_ADD_Z_ZI__ (size : (BitVec 2)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size +++ sh) == 0b001#3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat Zdn)
  let imm : Int := (BitVec.toNat imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm := imm
  match VL with
  | 128 => (execute_ADD_Z_ZI__ 128 dn esize imm)
  | 256 => (execute_ADD_Z_ZI__ 256 dn esize imm)
  | 512 => (execute_ADD_Z_ZI__ 512 dn esize imm)
  | 1024 => (execute_ADD_Z_ZI__ 1024 dn esize imm)
  | 2048 => (execute_ADD_Z_ZI__ 2048 dn esize imm)
  | _ => (pure ())

def decode_SUB_Z_ZI__ (size : (BitVec 2)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size +++ sh) == 0b001#3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat Zdn)
  let imm : Int := (BitVec.toNat imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm := imm
  match VL with
  | 128 => (execute_SUB_Z_ZI__ 128 dn esize imm)
  | 256 => (execute_SUB_Z_ZI__ 256 dn esize imm)
  | 512 => (execute_SUB_Z_ZI__ 512 dn esize imm)
  | 1024 => (execute_SUB_Z_ZI__ 1024 dn esize imm)
  | 2048 => (execute_SUB_Z_ZI__ 2048 dn esize imm)
  | _ => (pure ())

def decode_SUBR_Z_ZI__ (size : (BitVec 2)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size +++ sh) == 0b001#3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat Zdn)
  let imm : Int := (BitVec.toNat imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm := imm
  match VL with
  | 128 => (execute_SUBR_Z_ZI__ 128 dn esize imm)
  | 256 => (execute_SUBR_Z_ZI__ 256 dn esize imm)
  | 512 => (execute_SUBR_Z_ZI__ 512 dn esize imm)
  | 1024 => (execute_SUBR_Z_ZI__ 1024 dn esize imm)
  | 2048 => (execute_SUBR_Z_ZI__ 2048 dn esize imm)
  | _ => (pure ())

def decode_MUL_Z_ZI__ (size : (BitVec 2)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat Zdn)
  let imm := (BitVec.toInt imm8)
  match VL with
  | 128 => (execute_MUL_Z_ZI__ 128 dn esize imm)
  | 256 => (execute_MUL_Z_ZI__ 256 dn esize imm)
  | 512 => (execute_MUL_Z_ZI__ 512 dn esize imm)
  | 1024 => (execute_MUL_Z_ZI__ 1024 dn esize imm)
  | 2048 => (execute_MUL_Z_ZI__ 2048 dn esize imm)
  | _ => (pure ())

def decode_UMAX_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat Zdn)
  let is_unsigned : Bool := true
  let imm ← do (asl_Int imm8 is_unsigned)
  match VL with
  | 128 => (execute_UMAX_Z_ZI__ 128 dn esize imm is_unsigned)
  | 256 => (execute_UMAX_Z_ZI__ 256 dn esize imm is_unsigned)
  | 512 => (execute_UMAX_Z_ZI__ 512 dn esize imm is_unsigned)
  | 1024 => (execute_UMAX_Z_ZI__ 1024 dn esize imm is_unsigned)
  | 2048 => (execute_UMAX_Z_ZI__ 2048 dn esize imm is_unsigned)
  | _ => (pure ())

def decode_SMAX_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat Zdn)
  let is_unsigned : Bool := false
  let imm ← do (asl_Int imm8 is_unsigned)
  match VL with
  | 128 => (execute_SMAX_Z_ZI__ 128 dn esize imm is_unsigned)
  | 256 => (execute_SMAX_Z_ZI__ 256 dn esize imm is_unsigned)
  | 512 => (execute_SMAX_Z_ZI__ 512 dn esize imm is_unsigned)
  | 1024 => (execute_SMAX_Z_ZI__ 1024 dn esize imm is_unsigned)
  | 2048 => (execute_SMAX_Z_ZI__ 2048 dn esize imm is_unsigned)
  | _ => (pure ())

def decode_UMIN_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat Zdn)
  let is_unsigned : Bool := true
  let imm ← do (asl_Int imm8 is_unsigned)
  match VL with
  | 128 => (execute_UMIN_Z_ZI__ 128 dn esize imm is_unsigned)
  | 256 => (execute_UMIN_Z_ZI__ 256 dn esize imm is_unsigned)
  | 512 => (execute_UMIN_Z_ZI__ 512 dn esize imm is_unsigned)
  | 1024 => (execute_UMIN_Z_ZI__ 1024 dn esize imm is_unsigned)
  | 2048 => (execute_UMIN_Z_ZI__ 2048 dn esize imm is_unsigned)
  | _ => (pure ())

def decode_SMIN_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat Zdn)
  let is_unsigned : Bool := false
  let imm ← do (asl_Int imm8 is_unsigned)
  match VL with
  | 128 => (execute_SMIN_Z_ZI__ 128 dn esize imm is_unsigned)
  | 256 => (execute_SMIN_Z_ZI__ 256 dn esize imm is_unsigned)
  | 512 => (execute_SMIN_Z_ZI__ 512 dn esize imm is_unsigned)
  | 1024 => (execute_SMIN_Z_ZI__ 1024 dn esize imm is_unsigned)
  | 2048 => (execute_SMIN_Z_ZI__ 2048 dn esize imm is_unsigned)
  | _ => (pure ())

def decode_ADDPL_R_RI__ (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let d := (BitVec.toNat Rd)
  let imm := (BitVec.toInt imm6)
  match VL with
  | 128 => (execute_ADDPL_R_RI__ 128 d imm n)
  | 256 => (execute_ADDPL_R_RI__ 256 d imm n)
  | 512 => (execute_ADDPL_R_RI__ 512 d imm n)
  | 1024 => (execute_ADDPL_R_RI__ 1024 d imm n)
  | 2048 => (execute_ADDPL_R_RI__ 2048 d imm n)
  | _ => (pure ())

def decode_ADDVL_R_RI__ (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let d := (BitVec.toNat Rd)
  let imm := (BitVec.toInt imm6)
  match VL with
  | 128 => (execute_ADDVL_R_RI__ 128 d imm n)
  | 256 => (execute_ADDVL_R_RI__ 256 d imm n)
  | 512 => (execute_ADDVL_R_RI__ 512 d imm n)
  | 1024 => (execute_ADDVL_R_RI__ 1024 d imm n)
  | 2048 => (execute_ADDVL_R_RI__ 2048 d imm n)
  | _ => (pure ())

def decode_ADD_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_ADD_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_ADD_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_ADD_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_ADD_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_ADD_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_AND_Z_ZZ__ (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_AND_Z_ZZ__ 128 d m n)
  | 256 => (execute_AND_Z_ZZ__ 256 d m n)
  | 512 => (execute_AND_Z_ZZ__ 512 d m n)
  | 1024 => (execute_AND_Z_ZZ__ 1024 d m n)
  | 2048 => (execute_AND_Z_ZZ__ 2048 d m n)
  | _ => (pure ())

def decode_BIC_Z_ZZ__ (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_BIC_Z_ZZ__ 128 d m n)
  | 256 => (execute_BIC_Z_ZZ__ 256 d m n)
  | 512 => (execute_BIC_Z_ZZ__ 512 d m n)
  | 1024 => (execute_BIC_Z_ZZ__ 1024 d m n)
  | 2048 => (execute_BIC_Z_ZZ__ 2048 d m n)
  | _ => (pure ())

def decode_EOR_Z_ZZ__ (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_EOR_Z_ZZ__ 128 d m n)
  | 256 => (execute_EOR_Z_ZZ__ 256 d m n)
  | 512 => (execute_EOR_Z_ZZ__ 512 d m n)
  | 1024 => (execute_EOR_Z_ZZ__ 1024 d m n)
  | 2048 => (execute_EOR_Z_ZZ__ 2048 d m n)
  | _ => (pure ())

def decode_ORR_Z_ZZ__ (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_ORR_Z_ZZ__ 128 d m n)
  | 256 => (execute_ORR_Z_ZZ__ 256 d m n)
  | 512 => (execute_ORR_Z_ZZ__ 512 d m n)
  | 1024 => (execute_ORR_Z_ZZ__ 1024 d m n)
  | 2048 => (execute_ORR_Z_ZZ__ 2048 d m n)
  | _ => (pure ())

def decode_SUB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SUB_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_SUB_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_SUB_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_SUB_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_SUB_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_ADD_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_ADD_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_ADD_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_ADD_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_ADD_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_ADD_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_AND_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_AND_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_AND_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_AND_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_AND_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_AND_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_BIC_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_BIC_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_BIC_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_BIC_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_BIC_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_BIC_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_EOR_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_EOR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_EOR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_EOR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_EOR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_EOR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_LSL_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_LSL_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_LSL_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_LSL_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_LSL_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_LSL_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_LSLR_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_LSLR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_LSLR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_LSLR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_LSLR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_LSLR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_MUL_Z_P_ZZ__ (size : (BitVec 2)) (H : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_MUL_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_MUL_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_MUL_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_MUL_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_MUL_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_ORR_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_ORR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_ORR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_ORR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_ORR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_ORR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_SUB_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_SUB_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_SUB_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_SUB_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_SUB_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_SUB_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_SUBR_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_SUBR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_SUBR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_SUBR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_SUBR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_SUBR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_LSR_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_LSR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_LSR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_LSR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_LSR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_LSR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_ASR_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_ASR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_ASR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_ASR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_ASR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_ASR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_LSRR_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_LSRR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_LSRR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_LSRR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_LSRR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_LSRR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_ASRR_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_ASRR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_ASRR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_ASRR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_ASRR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_ASRR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_UABD_Z_P_ZZ__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UABD_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_UABD_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_UABD_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_UABD_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_UABD_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_SABD_Z_P_ZZ__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SABD_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_SABD_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_SABD_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_SABD_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_SABD_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_UDIV_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((let b__0 := size
     if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
     then true
     else false : Bool) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UDIV_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_UDIV_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_UDIV_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_UDIV_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_UDIV_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_SDIV_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((let b__0 := size
     if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
     then true
     else false : Bool) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SDIV_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_SDIV_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_SDIV_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_SDIV_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_SDIV_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_UDIVR_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((let b__0 := size
     if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
     then true
     else false : Bool) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UDIVR_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_UDIVR_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_UDIVR_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_UDIVR_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_UDIVR_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_SDIVR_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((let b__0 := size
     if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
     then true
     else false : Bool) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SDIVR_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_SDIVR_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_SDIVR_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_SDIVR_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_SDIVR_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_UMAX_Z_P_ZZ__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMAX_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_UMAX_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_UMAX_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_UMAX_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_UMAX_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_SMAX_Z_P_ZZ__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMAX_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_SMAX_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_SMAX_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_SMAX_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_SMAX_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_UMIN_Z_P_ZZ__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMIN_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_UMIN_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_UMIN_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_UMIN_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_UMIN_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_SMIN_Z_P_ZZ__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMIN_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_SMIN_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_SMIN_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_SMIN_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_SMIN_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_UMULH_Z_P_ZZ__ (size : (BitVec 2)) (H : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMULH_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_UMULH_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_UMULH_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_UMULH_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_UMULH_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_SMULH_Z_P_ZZ__ (size : (BitVec 2)) (H : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMULH_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_SMULH_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_SMULH_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_SMULH_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_SMULH_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_WHILELO_P_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Pd)
  let is_unsigned : Bool := true
  let op : SVECmp := Cmp_LT
  match VL with
  | 128 => (execute_WHILELO_P_P_RR__ 128 d esize m n op rsize is_unsigned)
  | 256 => (execute_WHILELO_P_P_RR__ 256 d esize m n op rsize is_unsigned)
  | 512 => (execute_WHILELO_P_P_RR__ 512 d esize m n op rsize is_unsigned)
  | 1024 => (execute_WHILELO_P_P_RR__ 1024 d esize m n op rsize is_unsigned)
  | 2048 => (execute_WHILELO_P_P_RR__ 2048 d esize m n op rsize is_unsigned)
  | _ => (pure ())

def decode_WHILELS_P_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Pd)
  let is_unsigned : Bool := true
  let op : SVECmp := Cmp_LE
  match VL with
  | 128 => (execute_WHILELS_P_P_RR__ 128 d esize m n op rsize is_unsigned)
  | 256 => (execute_WHILELS_P_P_RR__ 256 d esize m n op rsize is_unsigned)
  | 512 => (execute_WHILELS_P_P_RR__ 512 d esize m n op rsize is_unsigned)
  | 1024 => (execute_WHILELS_P_P_RR__ 1024 d esize m n op rsize is_unsigned)
  | 2048 => (execute_WHILELS_P_P_RR__ 2048 d esize m n op rsize is_unsigned)
  | _ => (pure ())

def decode_WHILELT_P_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Pd)
  let is_unsigned : Bool := false
  let op : SVECmp := Cmp_LT
  match VL with
  | 128 => (execute_WHILELT_P_P_RR__ 128 d esize m n op rsize is_unsigned)
  | 256 => (execute_WHILELT_P_P_RR__ 256 d esize m n op rsize is_unsigned)
  | 512 => (execute_WHILELT_P_P_RR__ 512 d esize m n op rsize is_unsigned)
  | 1024 => (execute_WHILELT_P_P_RR__ 1024 d esize m n op rsize is_unsigned)
  | 2048 => (execute_WHILELT_P_P_RR__ 2048 d esize m n op rsize is_unsigned)
  | _ => (pure ())

def decode_WHILELE_P_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Pd)
  let is_unsigned : Bool := false
  let op : SVECmp := Cmp_LE
  match VL with
  | 128 => (execute_WHILELE_P_P_RR__ 128 d esize m n op rsize is_unsigned)
  | 256 => (execute_WHILELE_P_P_RR__ 256 d esize m n op rsize is_unsigned)
  | 512 => (execute_WHILELE_P_P_RR__ 512 d esize m n op rsize is_unsigned)
  | 1024 => (execute_WHILELE_P_P_RR__ 1024 d esize m n op rsize is_unsigned)
  | 2048 => (execute_WHILELE_P_P_RR__ 2048 d esize m n op rsize is_unsigned)
  | _ => (pure ())

def decode_WHILEHI_P_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Pd)
  let is_unsigned : Bool := true
  let op : SVECmp := Cmp_GT
  match VL with
  | 128 => (execute_WHILEHI_P_P_RR__ 128 d esize m n op rsize is_unsigned)
  | 256 => (execute_WHILEHI_P_P_RR__ 256 d esize m n op rsize is_unsigned)
  | 512 => (execute_WHILEHI_P_P_RR__ 512 d esize m n op rsize is_unsigned)
  | 1024 => (execute_WHILEHI_P_P_RR__ 1024 d esize m n op rsize is_unsigned)
  | 2048 => (execute_WHILEHI_P_P_RR__ 2048 d esize m n op rsize is_unsigned)
  | _ => (pure ())

def decode_WHILEHS_P_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Pd)
  let is_unsigned : Bool := true
  let op : SVECmp := Cmp_GE
  match VL with
  | 128 => (execute_WHILEHS_P_P_RR__ 128 d esize m n op rsize is_unsigned)
  | 256 => (execute_WHILEHS_P_P_RR__ 256 d esize m n op rsize is_unsigned)
  | 512 => (execute_WHILEHS_P_P_RR__ 512 d esize m n op rsize is_unsigned)
  | 1024 => (execute_WHILEHS_P_P_RR__ 1024 d esize m n op rsize is_unsigned)
  | 2048 => (execute_WHILEHS_P_P_RR__ 2048 d esize m n op rsize is_unsigned)
  | _ => (pure ())

def decode_WHILEGT_P_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Pd)
  let is_unsigned : Bool := false
  let op : SVECmp := Cmp_GT
  match VL with
  | 128 => (execute_WHILEGT_P_P_RR__ 128 d esize m n op rsize is_unsigned)
  | 256 => (execute_WHILEGT_P_P_RR__ 256 d esize m n op rsize is_unsigned)
  | 512 => (execute_WHILEGT_P_P_RR__ 512 d esize m n op rsize is_unsigned)
  | 1024 => (execute_WHILEGT_P_P_RR__ 1024 d esize m n op rsize is_unsigned)
  | 2048 => (execute_WHILEGT_P_P_RR__ 2048 d esize m n op rsize is_unsigned)
  | _ => (pure ())

def decode_WHILEGE_P_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Pd)
  let is_unsigned : Bool := false
  let op : SVECmp := Cmp_GE
  match VL with
  | 128 => (execute_WHILEGE_P_P_RR__ 128 d esize m n op rsize is_unsigned)
  | 256 => (execute_WHILEGE_P_P_RR__ 256 d esize m n op rsize is_unsigned)
  | 512 => (execute_WHILEGE_P_P_RR__ 512 d esize m n op rsize is_unsigned)
  | 1024 => (execute_WHILEGE_P_P_RR__ 1024 d esize m n op rsize is_unsigned)
  | 2048 => (execute_WHILEGE_P_P_RR__ 2048 d esize m n op rsize is_unsigned)
  | _ => (pure ())

def decode_CMPEQ_P_P_ZI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_EQ
  let imm := (BitVec.toInt imm5)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_CMPEQ_P_P_ZI__ 128 d esize g imm n op is_unsigned)
  | 256 => (execute_CMPEQ_P_P_ZI__ 256 d esize g imm n op is_unsigned)
  | 512 => (execute_CMPEQ_P_P_ZI__ 512 d esize g imm n op is_unsigned)
  | 1024 => (execute_CMPEQ_P_P_ZI__ 1024 d esize g imm n op is_unsigned)
  | 2048 => (execute_CMPEQ_P_P_ZI__ 2048 d esize g imm n op is_unsigned)
  | _ => (pure ())

def decode_CMPNE_P_P_ZI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_NE
  let imm := (BitVec.toInt imm5)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_CMPNE_P_P_ZI__ 128 d esize g imm n op is_unsigned)
  | 256 => (execute_CMPNE_P_P_ZI__ 256 d esize g imm n op is_unsigned)
  | 512 => (execute_CMPNE_P_P_ZI__ 512 d esize g imm n op is_unsigned)
  | 1024 => (execute_CMPNE_P_P_ZI__ 1024 d esize g imm n op is_unsigned)
  | 2048 => (execute_CMPNE_P_P_ZI__ 2048 d esize g imm n op is_unsigned)
  | _ => (pure ())

def decode_CMPHS_P_P_ZI__ (size : (BitVec 2)) (imm7 : (BitVec 7)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GE
  let imm := (BitVec.toNat imm7)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_CMPHS_P_P_ZI__ 128 d esize g imm n op is_unsigned)
  | 256 => (execute_CMPHS_P_P_ZI__ 256 d esize g imm n op is_unsigned)
  | 512 => (execute_CMPHS_P_P_ZI__ 512 d esize g imm n op is_unsigned)
  | 1024 => (execute_CMPHS_P_P_ZI__ 1024 d esize g imm n op is_unsigned)
  | 2048 => (execute_CMPHS_P_P_ZI__ 2048 d esize g imm n op is_unsigned)
  | _ => (pure ())

def decode_CMPHI_P_P_ZI__ (size : (BitVec 2)) (imm7 : (BitVec 7)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GT
  let imm := (BitVec.toNat imm7)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_CMPHI_P_P_ZI__ 128 d esize g imm n op is_unsigned)
  | 256 => (execute_CMPHI_P_P_ZI__ 256 d esize g imm n op is_unsigned)
  | 512 => (execute_CMPHI_P_P_ZI__ 512 d esize g imm n op is_unsigned)
  | 1024 => (execute_CMPHI_P_P_ZI__ 1024 d esize g imm n op is_unsigned)
  | 2048 => (execute_CMPHI_P_P_ZI__ 2048 d esize g imm n op is_unsigned)
  | _ => (pure ())

def decode_CMPLO_P_P_ZI__ (size : (BitVec 2)) (imm7 : (BitVec 7)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_LT
  let imm := (BitVec.toNat imm7)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_CMPLO_P_P_ZI__ 128 d esize g imm n op is_unsigned)
  | 256 => (execute_CMPLO_P_P_ZI__ 256 d esize g imm n op is_unsigned)
  | 512 => (execute_CMPLO_P_P_ZI__ 512 d esize g imm n op is_unsigned)
  | 1024 => (execute_CMPLO_P_P_ZI__ 1024 d esize g imm n op is_unsigned)
  | 2048 => (execute_CMPLO_P_P_ZI__ 2048 d esize g imm n op is_unsigned)
  | _ => (pure ())

def decode_CMPLS_P_P_ZI__ (size : (BitVec 2)) (imm7 : (BitVec 7)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_LE
  let imm := (BitVec.toNat imm7)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_CMPLS_P_P_ZI__ 128 d esize g imm n op is_unsigned)
  | 256 => (execute_CMPLS_P_P_ZI__ 256 d esize g imm n op is_unsigned)
  | 512 => (execute_CMPLS_P_P_ZI__ 512 d esize g imm n op is_unsigned)
  | 1024 => (execute_CMPLS_P_P_ZI__ 1024 d esize g imm n op is_unsigned)
  | 2048 => (execute_CMPLS_P_P_ZI__ 2048 d esize g imm n op is_unsigned)
  | _ => (pure ())

def decode_CMPGE_P_P_ZI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GE
  let imm := (BitVec.toInt imm5)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_CMPGE_P_P_ZI__ 128 d esize g imm n op is_unsigned)
  | 256 => (execute_CMPGE_P_P_ZI__ 256 d esize g imm n op is_unsigned)
  | 512 => (execute_CMPGE_P_P_ZI__ 512 d esize g imm n op is_unsigned)
  | 1024 => (execute_CMPGE_P_P_ZI__ 1024 d esize g imm n op is_unsigned)
  | 2048 => (execute_CMPGE_P_P_ZI__ 2048 d esize g imm n op is_unsigned)
  | _ => (pure ())

def decode_CMPGT_P_P_ZI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GT
  let imm := (BitVec.toInt imm5)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_CMPGT_P_P_ZI__ 128 d esize g imm n op is_unsigned)
  | 256 => (execute_CMPGT_P_P_ZI__ 256 d esize g imm n op is_unsigned)
  | 512 => (execute_CMPGT_P_P_ZI__ 512 d esize g imm n op is_unsigned)
  | 1024 => (execute_CMPGT_P_P_ZI__ 1024 d esize g imm n op is_unsigned)
  | 2048 => (execute_CMPGT_P_P_ZI__ 2048 d esize g imm n op is_unsigned)
  | _ => (pure ())

def decode_CMPLT_P_P_ZI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_LT
  let imm := (BitVec.toInt imm5)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_CMPLT_P_P_ZI__ 128 d esize g imm n op is_unsigned)
  | 256 => (execute_CMPLT_P_P_ZI__ 256 d esize g imm n op is_unsigned)
  | 512 => (execute_CMPLT_P_P_ZI__ 512 d esize g imm n op is_unsigned)
  | 1024 => (execute_CMPLT_P_P_ZI__ 1024 d esize g imm n op is_unsigned)
  | 2048 => (execute_CMPLT_P_P_ZI__ 2048 d esize g imm n op is_unsigned)
  | _ => (pure ())

def decode_CMPLE_P_P_ZI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_LE
  let imm := (BitVec.toInt imm5)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_CMPLE_P_P_ZI__ 128 d esize g imm n op is_unsigned)
  | 256 => (execute_CMPLE_P_P_ZI__ 256 d esize g imm n op is_unsigned)
  | 512 => (execute_CMPLE_P_P_ZI__ 512 d esize g imm n op is_unsigned)
  | 1024 => (execute_CMPLE_P_P_ZI__ 1024 d esize g imm n op is_unsigned)
  | 2048 => (execute_CMPLE_P_P_ZI__ 2048 d esize g imm n op is_unsigned)
  | _ => (pure ())

def decode_CMPEQ_P_P_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_EQ
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_CMPEQ_P_P_ZW__ 128 d esize g m n op is_unsigned)
  | 256 => (execute_CMPEQ_P_P_ZW__ 256 d esize g m n op is_unsigned)
  | 512 => (execute_CMPEQ_P_P_ZW__ 512 d esize g m n op is_unsigned)
  | 1024 => (execute_CMPEQ_P_P_ZW__ 1024 d esize g m n op is_unsigned)
  | 2048 => (execute_CMPEQ_P_P_ZW__ 2048 d esize g m n op is_unsigned)
  | _ => (pure ())

def decode_CMPNE_P_P_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_NE
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_CMPNE_P_P_ZW__ 128 d esize g m n op is_unsigned)
  | 256 => (execute_CMPNE_P_P_ZW__ 256 d esize g m n op is_unsigned)
  | 512 => (execute_CMPNE_P_P_ZW__ 512 d esize g m n op is_unsigned)
  | 1024 => (execute_CMPNE_P_P_ZW__ 1024 d esize g m n op is_unsigned)
  | 2048 => (execute_CMPNE_P_P_ZW__ 2048 d esize g m n op is_unsigned)
  | _ => (pure ())

def decode_CMPHS_P_P_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GE
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_CMPHS_P_P_ZW__ 128 d esize g m n op is_unsigned)
  | 256 => (execute_CMPHS_P_P_ZW__ 256 d esize g m n op is_unsigned)
  | 512 => (execute_CMPHS_P_P_ZW__ 512 d esize g m n op is_unsigned)
  | 1024 => (execute_CMPHS_P_P_ZW__ 1024 d esize g m n op is_unsigned)
  | 2048 => (execute_CMPHS_P_P_ZW__ 2048 d esize g m n op is_unsigned)
  | _ => (pure ())

def decode_CMPHI_P_P_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GT
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_CMPHI_P_P_ZW__ 128 d esize g m n op is_unsigned)
  | 256 => (execute_CMPHI_P_P_ZW__ 256 d esize g m n op is_unsigned)
  | 512 => (execute_CMPHI_P_P_ZW__ 512 d esize g m n op is_unsigned)
  | 1024 => (execute_CMPHI_P_P_ZW__ 1024 d esize g m n op is_unsigned)
  | 2048 => (execute_CMPHI_P_P_ZW__ 2048 d esize g m n op is_unsigned)
  | _ => (pure ())

def decode_CMPLO_P_P_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_LT
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_CMPLO_P_P_ZW__ 128 d esize g m n op is_unsigned)
  | 256 => (execute_CMPLO_P_P_ZW__ 256 d esize g m n op is_unsigned)
  | 512 => (execute_CMPLO_P_P_ZW__ 512 d esize g m n op is_unsigned)
  | 1024 => (execute_CMPLO_P_P_ZW__ 1024 d esize g m n op is_unsigned)
  | 2048 => (execute_CMPLO_P_P_ZW__ 2048 d esize g m n op is_unsigned)
  | _ => (pure ())

def decode_CMPLS_P_P_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_LE
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_CMPLS_P_P_ZW__ 128 d esize g m n op is_unsigned)
  | 256 => (execute_CMPLS_P_P_ZW__ 256 d esize g m n op is_unsigned)
  | 512 => (execute_CMPLS_P_P_ZW__ 512 d esize g m n op is_unsigned)
  | 1024 => (execute_CMPLS_P_P_ZW__ 1024 d esize g m n op is_unsigned)
  | 2048 => (execute_CMPLS_P_P_ZW__ 2048 d esize g m n op is_unsigned)
  | _ => (pure ())

def decode_CMPGE_P_P_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GE
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_CMPGE_P_P_ZW__ 128 d esize g m n op is_unsigned)
  | 256 => (execute_CMPGE_P_P_ZW__ 256 d esize g m n op is_unsigned)
  | 512 => (execute_CMPGE_P_P_ZW__ 512 d esize g m n op is_unsigned)
  | 1024 => (execute_CMPGE_P_P_ZW__ 1024 d esize g m n op is_unsigned)
  | 2048 => (execute_CMPGE_P_P_ZW__ 2048 d esize g m n op is_unsigned)
  | _ => (pure ())

def decode_CMPGT_P_P_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GT
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_CMPGT_P_P_ZW__ 128 d esize g m n op is_unsigned)
  | 256 => (execute_CMPGT_P_P_ZW__ 256 d esize g m n op is_unsigned)
  | 512 => (execute_CMPGT_P_P_ZW__ 512 d esize g m n op is_unsigned)
  | 1024 => (execute_CMPGT_P_P_ZW__ 1024 d esize g m n op is_unsigned)
  | 2048 => (execute_CMPGT_P_P_ZW__ 2048 d esize g m n op is_unsigned)
  | _ => (pure ())

def decode_CMPLT_P_P_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_LT
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_CMPLT_P_P_ZW__ 128 d esize g m n op is_unsigned)
  | 256 => (execute_CMPLT_P_P_ZW__ 256 d esize g m n op is_unsigned)
  | 512 => (execute_CMPLT_P_P_ZW__ 512 d esize g m n op is_unsigned)
  | 1024 => (execute_CMPLT_P_P_ZW__ 1024 d esize g m n op is_unsigned)
  | 2048 => (execute_CMPLT_P_P_ZW__ 2048 d esize g m n op is_unsigned)
  | _ => (pure ())

def decode_CMPLE_P_P_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_LE
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_CMPLE_P_P_ZW__ 128 d esize g m n op is_unsigned)
  | 256 => (execute_CMPLE_P_P_ZW__ 256 d esize g m n op is_unsigned)
  | 512 => (execute_CMPLE_P_P_ZW__ 512 d esize g m n op is_unsigned)
  | 1024 => (execute_CMPLE_P_P_ZW__ 1024 d esize g m n op is_unsigned)
  | 2048 => (execute_CMPLE_P_P_ZW__ 2048 d esize g m n op is_unsigned)
  | _ => (pure ())

def decode_CMPEQ_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_EQ
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_CMPEQ_P_P_ZZ__ 128 d esize g m n op is_unsigned)
  | 256 => (execute_CMPEQ_P_P_ZZ__ 256 d esize g m n op is_unsigned)
  | 512 => (execute_CMPEQ_P_P_ZZ__ 512 d esize g m n op is_unsigned)
  | 1024 => (execute_CMPEQ_P_P_ZZ__ 1024 d esize g m n op is_unsigned)
  | 2048 => (execute_CMPEQ_P_P_ZZ__ 2048 d esize g m n op is_unsigned)
  | _ => (pure ())

def decode_CMPNE_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_NE
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_CMPNE_P_P_ZZ__ 128 d esize g m n op is_unsigned)
  | 256 => (execute_CMPNE_P_P_ZZ__ 256 d esize g m n op is_unsigned)
  | 512 => (execute_CMPNE_P_P_ZZ__ 512 d esize g m n op is_unsigned)
  | 1024 => (execute_CMPNE_P_P_ZZ__ 1024 d esize g m n op is_unsigned)
  | 2048 => (execute_CMPNE_P_P_ZZ__ 2048 d esize g m n op is_unsigned)
  | _ => (pure ())

def decode_CMPGE_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GE
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_CMPGE_P_P_ZZ__ 128 d esize g m n op is_unsigned)
  | 256 => (execute_CMPGE_P_P_ZZ__ 256 d esize g m n op is_unsigned)
  | 512 => (execute_CMPGE_P_P_ZZ__ 512 d esize g m n op is_unsigned)
  | 1024 => (execute_CMPGE_P_P_ZZ__ 1024 d esize g m n op is_unsigned)
  | 2048 => (execute_CMPGE_P_P_ZZ__ 2048 d esize g m n op is_unsigned)
  | _ => (pure ())

def decode_CMPGT_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GT
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_CMPGT_P_P_ZZ__ 128 d esize g m n op is_unsigned)
  | 256 => (execute_CMPGT_P_P_ZZ__ 256 d esize g m n op is_unsigned)
  | 512 => (execute_CMPGT_P_P_ZZ__ 512 d esize g m n op is_unsigned)
  | 1024 => (execute_CMPGT_P_P_ZZ__ 1024 d esize g m n op is_unsigned)
  | 2048 => (execute_CMPGT_P_P_ZZ__ 2048 d esize g m n op is_unsigned)
  | _ => (pure ())

def decode_CMPHS_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GE
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_CMPHS_P_P_ZZ__ 128 d esize g m n op is_unsigned)
  | 256 => (execute_CMPHS_P_P_ZZ__ 256 d esize g m n op is_unsigned)
  | 512 => (execute_CMPHS_P_P_ZZ__ 512 d esize g m n op is_unsigned)
  | 1024 => (execute_CMPHS_P_P_ZZ__ 1024 d esize g m n op is_unsigned)
  | 2048 => (execute_CMPHS_P_P_ZZ__ 2048 d esize g m n op is_unsigned)
  | _ => (pure ())

def decode_CMPHI_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Pd)
  let op : SVECmp := Cmp_GT
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_CMPHI_P_P_ZZ__ 128 d esize g m n op is_unsigned)
  | 256 => (execute_CMPHI_P_P_ZZ__ 256 d esize g m n op is_unsigned)
  | 512 => (execute_CMPHI_P_P_ZZ__ 512 d esize g m n op is_unsigned)
  | 1024 => (execute_CMPHI_P_P_ZZ__ 1024 d esize g m n op is_unsigned)
  | 2048 => (execute_CMPHI_P_P_ZZ__ 2048 d esize g m n op is_unsigned)
  | _ => (pure ())

def decode_DECP_R_P_R__ (size : (BitVec 2)) (D : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Pm)
  let dn := (BitVec.toNat Rdn)
  match VL with
  | 128 => (execute_DECP_R_P_R__ 128 dn esize m)
  | 256 => (execute_DECP_R_P_R__ 256 dn esize m)
  | 512 => (execute_DECP_R_P_R__ 512 dn esize m)
  | 1024 => (execute_DECP_R_P_R__ 1024 dn esize m)
  | 2048 => (execute_DECP_R_P_R__ 2048 dn esize m)
  | _ => (pure ())

def decode_INCP_R_P_R__ (size : (BitVec 2)) (D : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Pm)
  let dn := (BitVec.toNat Rdn)
  match VL with
  | 128 => (execute_INCP_R_P_R__ 128 dn esize m)
  | 256 => (execute_INCP_R_P_R__ 256 dn esize m)
  | 512 => (execute_INCP_R_P_R__ 512 dn esize m)
  | 1024 => (execute_INCP_R_P_R__ 1024 dn esize m)
  | 2048 => (execute_INCP_R_P_R__ 2048 dn esize m)
  | _ => (pure ())

def decode_UQINCP_R_P_R_UW (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (sf : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Pm)
  let dn := (BitVec.toNat Rdn)
  let is_unsigned : Bool := true
  let ssize := 32
  match VL with
  | 128 => (execute_UQINCP_R_P_R_UW 128 dn esize m ssize is_unsigned)
  | 256 => (execute_UQINCP_R_P_R_UW 256 dn esize m ssize is_unsigned)
  | 512 => (execute_UQINCP_R_P_R_UW 512 dn esize m ssize is_unsigned)
  | 1024 => (execute_UQINCP_R_P_R_UW 1024 dn esize m ssize is_unsigned)
  | 2048 => (execute_UQINCP_R_P_R_UW 2048 dn esize m ssize is_unsigned)
  | _ => (pure ())

def decode_SQINCP_R_P_R_SX (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (sf : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Pm)
  let dn := (BitVec.toNat Rdn)
  let is_unsigned : Bool := false
  let ssize := 32
  match VL with
  | 128 => (execute_SQINCP_R_P_R_SX 128 dn esize m ssize is_unsigned)
  | 256 => (execute_SQINCP_R_P_R_SX 256 dn esize m ssize is_unsigned)
  | 512 => (execute_SQINCP_R_P_R_SX 512 dn esize m ssize is_unsigned)
  | 1024 => (execute_SQINCP_R_P_R_SX 1024 dn esize m ssize is_unsigned)
  | 2048 => (execute_SQINCP_R_P_R_SX 2048 dn esize m ssize is_unsigned)
  | _ => (pure ())

def decode_UQINCP_R_P_R_X (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (sf : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Pm)
  let dn := (BitVec.toNat Rdn)
  let is_unsigned : Bool := true
  let ssize := 64
  match VL with
  | 128 => (execute_UQINCP_R_P_R_X 128 dn esize m ssize is_unsigned)
  | 256 => (execute_UQINCP_R_P_R_X 256 dn esize m ssize is_unsigned)
  | 512 => (execute_UQINCP_R_P_R_X 512 dn esize m ssize is_unsigned)
  | 1024 => (execute_UQINCP_R_P_R_X 1024 dn esize m ssize is_unsigned)
  | 2048 => (execute_UQINCP_R_P_R_X 2048 dn esize m ssize is_unsigned)
  | _ => (pure ())

def decode_SQINCP_R_P_R_X (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (sf : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Pm)
  let dn := (BitVec.toNat Rdn)
  let is_unsigned : Bool := false
  let ssize := 64
  match VL with
  | 128 => (execute_SQINCP_R_P_R_X 128 dn esize m ssize is_unsigned)
  | 256 => (execute_SQINCP_R_P_R_X 256 dn esize m ssize is_unsigned)
  | 512 => (execute_SQINCP_R_P_R_X 512 dn esize m ssize is_unsigned)
  | 1024 => (execute_SQINCP_R_P_R_X 1024 dn esize m ssize is_unsigned)
  | 2048 => (execute_SQINCP_R_P_R_X 2048 dn esize m ssize is_unsigned)
  | _ => (pure ())

def decode_UQDECP_R_P_R_UW (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (sf : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Pm)
  let dn := (BitVec.toNat Rdn)
  let is_unsigned : Bool := true
  let ssize := 32
  match VL with
  | 128 => (execute_UQDECP_R_P_R_UW 128 dn esize m ssize is_unsigned)
  | 256 => (execute_UQDECP_R_P_R_UW 256 dn esize m ssize is_unsigned)
  | 512 => (execute_UQDECP_R_P_R_UW 512 dn esize m ssize is_unsigned)
  | 1024 => (execute_UQDECP_R_P_R_UW 1024 dn esize m ssize is_unsigned)
  | 2048 => (execute_UQDECP_R_P_R_UW 2048 dn esize m ssize is_unsigned)
  | _ => (pure ())

def decode_SQDECP_R_P_R_SX (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (sf : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Pm)
  let dn := (BitVec.toNat Rdn)
  let is_unsigned : Bool := false
  let ssize := 32
  match VL with
  | 128 => (execute_SQDECP_R_P_R_SX 128 dn esize m ssize is_unsigned)
  | 256 => (execute_SQDECP_R_P_R_SX 256 dn esize m ssize is_unsigned)
  | 512 => (execute_SQDECP_R_P_R_SX 512 dn esize m ssize is_unsigned)
  | 1024 => (execute_SQDECP_R_P_R_SX 1024 dn esize m ssize is_unsigned)
  | 2048 => (execute_SQDECP_R_P_R_SX 2048 dn esize m ssize is_unsigned)
  | _ => (pure ())

def decode_UQDECP_R_P_R_X (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (sf : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Pm)
  let dn := (BitVec.toNat Rdn)
  let is_unsigned : Bool := true
  let ssize := 64
  match VL with
  | 128 => (execute_UQDECP_R_P_R_X 128 dn esize m ssize is_unsigned)
  | 256 => (execute_UQDECP_R_P_R_X 256 dn esize m ssize is_unsigned)
  | 512 => (execute_UQDECP_R_P_R_X 512 dn esize m ssize is_unsigned)
  | 1024 => (execute_UQDECP_R_P_R_X 1024 dn esize m ssize is_unsigned)
  | 2048 => (execute_UQDECP_R_P_R_X 2048 dn esize m ssize is_unsigned)
  | _ => (pure ())

def decode_SQDECP_R_P_R_X (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (sf : (BitVec 1)) (Pm : (BitVec 4)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Pm)
  let dn := (BitVec.toNat Rdn)
  let is_unsigned : Bool := false
  let ssize := 64
  match VL with
  | 128 => (execute_SQDECP_R_P_R_X 128 dn esize m ssize is_unsigned)
  | 256 => (execute_SQDECP_R_P_R_X 256 dn esize m ssize is_unsigned)
  | 512 => (execute_SQDECP_R_P_R_X 512 dn esize m ssize is_unsigned)
  | 1024 => (execute_SQDECP_R_P_R_X 1024 dn esize m ssize is_unsigned)
  | 2048 => (execute_SQDECP_R_P_R_X 2048 dn esize m ssize is_unsigned)
  | _ => (pure ())

def decode_DECP_Z_P_Z__ (size : (BitVec 2)) (D : (BitVec 1)) (Pm : (BitVec 4)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Pm)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_DECP_Z_P_Z__ 128 dn esize m)
  | 256 => (execute_DECP_Z_P_Z__ 256 dn esize m)
  | 512 => (execute_DECP_Z_P_Z__ 512 dn esize m)
  | 1024 => (execute_DECP_Z_P_Z__ 1024 dn esize m)
  | 2048 => (execute_DECP_Z_P_Z__ 2048 dn esize m)
  | _ => (pure ())

def decode_INCP_Z_P_Z__ (size : (BitVec 2)) (D : (BitVec 1)) (Pm : (BitVec 4)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Pm)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_INCP_Z_P_Z__ 128 dn esize m)
  | 256 => (execute_INCP_Z_P_Z__ 256 dn esize m)
  | 512 => (execute_INCP_Z_P_Z__ 512 dn esize m)
  | 1024 => (execute_INCP_Z_P_Z__ 1024 dn esize m)
  | 2048 => (execute_INCP_Z_P_Z__ 2048 dn esize m)
  | _ => (pure ())

def decode_UQINCP_Z_P_Z__ (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (Pm : (BitVec 4)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Pm)
  let dn := (BitVec.toNat Zdn)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UQINCP_Z_P_Z__ 128 dn esize m is_unsigned)
  | 256 => (execute_UQINCP_Z_P_Z__ 256 dn esize m is_unsigned)
  | 512 => (execute_UQINCP_Z_P_Z__ 512 dn esize m is_unsigned)
  | 1024 => (execute_UQINCP_Z_P_Z__ 1024 dn esize m is_unsigned)
  | 2048 => (execute_UQINCP_Z_P_Z__ 2048 dn esize m is_unsigned)
  | _ => (pure ())

def decode_SQINCP_Z_P_Z__ (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (Pm : (BitVec 4)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Pm)
  let dn := (BitVec.toNat Zdn)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SQINCP_Z_P_Z__ 128 dn esize m is_unsigned)
  | 256 => (execute_SQINCP_Z_P_Z__ 256 dn esize m is_unsigned)
  | 512 => (execute_SQINCP_Z_P_Z__ 512 dn esize m is_unsigned)
  | 1024 => (execute_SQINCP_Z_P_Z__ 1024 dn esize m is_unsigned)
  | 2048 => (execute_SQINCP_Z_P_Z__ 2048 dn esize m is_unsigned)
  | _ => (pure ())

def decode_UQDECP_Z_P_Z__ (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (Pm : (BitVec 4)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Pm)
  let dn := (BitVec.toNat Zdn)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UQDECP_Z_P_Z__ 128 dn esize m is_unsigned)
  | 256 => (execute_UQDECP_Z_P_Z__ 256 dn esize m is_unsigned)
  | 512 => (execute_UQDECP_Z_P_Z__ 512 dn esize m is_unsigned)
  | 1024 => (execute_UQDECP_Z_P_Z__ 1024 dn esize m is_unsigned)
  | 2048 => (execute_UQDECP_Z_P_Z__ 2048 dn esize m is_unsigned)
  | _ => (pure ())

def decode_SQDECP_Z_P_Z__ (size : (BitVec 2)) (D : (BitVec 1)) (U : (BitVec 1)) (Pm : (BitVec 4)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Pm)
  let dn := (BitVec.toNat Zdn)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SQDECP_Z_P_Z__ 128 dn esize m is_unsigned)
  | 256 => (execute_SQDECP_Z_P_Z__ 256 dn esize m is_unsigned)
  | 512 => (execute_SQDECP_Z_P_Z__ 512 dn esize m is_unsigned)
  | 1024 => (execute_SQDECP_Z_P_Z__ 1024 dn esize m is_unsigned)
  | 2048 => (execute_SQDECP_Z_P_Z__ 2048 dn esize m is_unsigned)
  | _ => (pure ())

def decode_DECB_R_RS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 => (execute_DECB_R_RS__ 128 dn esize imm pat)
  | 256 => (execute_DECB_R_RS__ 256 dn esize imm pat)
  | 512 => (execute_DECB_R_RS__ 512 dn esize imm pat)
  | 1024 => (execute_DECB_R_RS__ 1024 dn esize imm pat)
  | 2048 => (execute_DECB_R_RS__ 2048 dn esize imm pat)
  | _ => (pure ())

def decode_DECH_R_RS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 => (execute_DECH_R_RS__ 128 dn esize imm pat)
  | 256 => (execute_DECH_R_RS__ 256 dn esize imm pat)
  | 512 => (execute_DECH_R_RS__ 512 dn esize imm pat)
  | 1024 => (execute_DECH_R_RS__ 1024 dn esize imm pat)
  | 2048 => (execute_DECH_R_RS__ 2048 dn esize imm pat)
  | _ => (pure ())

def decode_DECW_R_RS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 => (execute_DECW_R_RS__ 128 dn esize imm pat)
  | 256 => (execute_DECW_R_RS__ 256 dn esize imm pat)
  | 512 => (execute_DECW_R_RS__ 512 dn esize imm pat)
  | 1024 => (execute_DECW_R_RS__ 1024 dn esize imm pat)
  | 2048 => (execute_DECW_R_RS__ 2048 dn esize imm pat)
  | _ => (pure ())

def decode_DECD_R_RS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 => (execute_DECD_R_RS__ 128 dn esize imm pat)
  | 256 => (execute_DECD_R_RS__ 256 dn esize imm pat)
  | 512 => (execute_DECD_R_RS__ 512 dn esize imm pat)
  | 1024 => (execute_DECD_R_RS__ 1024 dn esize imm pat)
  | 2048 => (execute_DECD_R_RS__ 2048 dn esize imm pat)
  | _ => (pure ())

def decode_INCB_R_RS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 => (execute_INCB_R_RS__ 128 dn esize imm pat)
  | 256 => (execute_INCB_R_RS__ 256 dn esize imm pat)
  | 512 => (execute_INCB_R_RS__ 512 dn esize imm pat)
  | 1024 => (execute_INCB_R_RS__ 1024 dn esize imm pat)
  | 2048 => (execute_INCB_R_RS__ 2048 dn esize imm pat)
  | _ => (pure ())

def decode_INCH_R_RS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 => (execute_INCH_R_RS__ 128 dn esize imm pat)
  | 256 => (execute_INCH_R_RS__ 256 dn esize imm pat)
  | 512 => (execute_INCH_R_RS__ 512 dn esize imm pat)
  | 1024 => (execute_INCH_R_RS__ 1024 dn esize imm pat)
  | 2048 => (execute_INCH_R_RS__ 2048 dn esize imm pat)
  | _ => (pure ())

def decode_INCW_R_RS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 => (execute_INCW_R_RS__ 128 dn esize imm pat)
  | 256 => (execute_INCW_R_RS__ 256 dn esize imm pat)
  | 512 => (execute_INCW_R_RS__ 512 dn esize imm pat)
  | 1024 => (execute_INCW_R_RS__ 1024 dn esize imm pat)
  | 2048 => (execute_INCW_R_RS__ 2048 dn esize imm pat)
  | _ => (pure ())

def decode_INCD_R_RS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 => (execute_INCD_R_RS__ 128 dn esize imm pat)
  | 256 => (execute_INCD_R_RS__ 256 dn esize imm pat)
  | 512 => (execute_INCD_R_RS__ 512 dn esize imm pat)
  | 1024 => (execute_INCD_R_RS__ 1024 dn esize imm pat)
  | 2048 => (execute_INCD_R_RS__ 2048 dn esize imm pat)
  | _ => (pure ())

def decode_UQINCB_R_RS_UW (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize := 32
  (execute_UQINCB_R_RS_UW dn esize imm pat ssize is_unsigned)

def decode_UQINCH_R_RS_UW (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize := 32
  (execute_UQINCH_R_RS_UW dn esize imm pat ssize is_unsigned)

def decode_UQINCW_R_RS_UW (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize := 32
  (execute_UQINCW_R_RS_UW dn esize imm pat ssize is_unsigned)

def decode_UQINCD_R_RS_UW (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize := 32
  (execute_UQINCD_R_RS_UW dn esize imm pat ssize is_unsigned)

def decode_SQINCB_R_RS_SX (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize := 32
  (execute_SQINCB_R_RS_SX dn esize imm pat ssize is_unsigned)

def decode_SQINCH_R_RS_SX (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize := 32
  (execute_SQINCH_R_RS_SX dn esize imm pat ssize is_unsigned)

def decode_SQINCW_R_RS_SX (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize := 32
  (execute_SQINCW_R_RS_SX dn esize imm pat ssize is_unsigned)

def decode_SQINCD_R_RS_SX (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize := 32
  (execute_SQINCD_R_RS_SX dn esize imm pat ssize is_unsigned)

def decode_UQINCB_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize := 64
  (execute_UQINCB_R_RS_X dn esize imm pat ssize is_unsigned)

def decode_UQINCH_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize := 64
  (execute_UQINCH_R_RS_X dn esize imm pat ssize is_unsigned)

def decode_UQINCW_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize := 64
  (execute_UQINCW_R_RS_X dn esize imm pat ssize is_unsigned)

def decode_UQINCD_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize := 64
  (execute_UQINCD_R_RS_X dn esize imm pat ssize is_unsigned)

def decode_SQINCB_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize := 64
  (execute_SQINCB_R_RS_X dn esize imm pat ssize is_unsigned)

def decode_SQINCH_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize := 64
  (execute_SQINCH_R_RS_X dn esize imm pat ssize is_unsigned)

def decode_SQINCW_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize := 64
  (execute_SQINCW_R_RS_X dn esize imm pat ssize is_unsigned)

def decode_SQINCD_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize := 64
  (execute_SQINCD_R_RS_X dn esize imm pat ssize is_unsigned)

def decode_UQDECB_R_RS_UW (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize := 32
  (execute_UQDECB_R_RS_UW dn esize imm pat ssize is_unsigned)

def decode_UQDECH_R_RS_UW (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize := 32
  (execute_UQDECH_R_RS_UW dn esize imm pat ssize is_unsigned)

def decode_UQDECW_R_RS_UW (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize := 32
  (execute_UQDECW_R_RS_UW dn esize imm pat ssize is_unsigned)

def decode_UQDECD_R_RS_UW (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize := 32
  (execute_UQDECD_R_RS_UW dn esize imm pat ssize is_unsigned)

def decode_SQDECB_R_RS_SX (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize := 32
  (execute_SQDECB_R_RS_SX dn esize imm pat ssize is_unsigned)

def decode_SQDECH_R_RS_SX (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize := 32
  (execute_SQDECH_R_RS_SX dn esize imm pat ssize is_unsigned)

def decode_SQDECW_R_RS_SX (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize := 32
  (execute_SQDECW_R_RS_SX dn esize imm pat ssize is_unsigned)

def decode_SQDECD_R_RS_SX (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize := 32
  (execute_SQDECD_R_RS_SX dn esize imm pat ssize is_unsigned)

def decode_UQDECB_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize := 64
  (execute_UQDECB_R_RS_X dn esize imm pat ssize is_unsigned)

def decode_UQDECH_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize := 64
  (execute_UQDECH_R_RS_X dn esize imm pat ssize is_unsigned)

def decode_UQDECW_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize := 64
  (execute_UQDECW_R_RS_X dn esize imm pat ssize is_unsigned)

def decode_UQDECD_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  let ssize := 64
  (execute_UQDECD_R_RS_X dn esize imm pat ssize is_unsigned)

def decode_SQDECB_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize := 64
  (execute_SQDECB_R_RS_X dn esize imm pat ssize is_unsigned)

def decode_SQDECH_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize := 64
  (execute_SQDECH_R_RS_X dn esize imm pat ssize is_unsigned)

def decode_SQDECW_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize := 64
  (execute_SQDECW_R_RS_X dn esize imm pat ssize is_unsigned)

def decode_SQDECD_R_RS_X (size : (BitVec 2)) (sf : (BitVec 1)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let dn := (BitVec.toNat Rdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  let ssize := 64
  (execute_SQDECD_R_RS_X dn esize imm pat ssize is_unsigned)

def decode_CNTB_R_S__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (pattern : (BitVec 5)) (Rd : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let d := (BitVec.toNat Rd)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  (execute_CNTB_R_S__ d esize imm pat)

def decode_CNTH_R_S__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (pattern : (BitVec 5)) (Rd : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let d := (BitVec.toNat Rd)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  (execute_CNTH_R_S__ d esize imm pat)

def decode_CNTW_R_S__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (pattern : (BitVec 5)) (Rd : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let d := (BitVec.toNat Rd)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  (execute_CNTW_R_S__ d esize imm pat)

def decode_CNTD_R_S__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (pattern : (BitVec 5)) (Rd : (BitVec 5)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let d := (BitVec.toNat Rd)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  (execute_CNTD_R_S__ d esize imm pat)

def decode_DECH_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 => (execute_DECH_Z_ZS__ 128 dn esize imm pat)
  | 256 => (execute_DECH_Z_ZS__ 256 dn esize imm pat)
  | 512 => (execute_DECH_Z_ZS__ 512 dn esize imm pat)
  | 1024 => (execute_DECH_Z_ZS__ 1024 dn esize imm pat)
  | 2048 => (execute_DECH_Z_ZS__ 2048 dn esize imm pat)
  | _ => (pure ())

def decode_DECW_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 => (execute_DECW_Z_ZS__ 128 dn esize imm pat)
  | 256 => (execute_DECW_Z_ZS__ 256 dn esize imm pat)
  | 512 => (execute_DECW_Z_ZS__ 512 dn esize imm pat)
  | 1024 => (execute_DECW_Z_ZS__ 1024 dn esize imm pat)
  | 2048 => (execute_DECW_Z_ZS__ 2048 dn esize imm pat)
  | _ => (pure ())

def decode_DECD_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 => (execute_DECD_Z_ZS__ 128 dn esize imm pat)
  | 256 => (execute_DECD_Z_ZS__ 256 dn esize imm pat)
  | 512 => (execute_DECD_Z_ZS__ 512 dn esize imm pat)
  | 1024 => (execute_DECD_Z_ZS__ 1024 dn esize imm pat)
  | 2048 => (execute_DECD_Z_ZS__ 2048 dn esize imm pat)
  | _ => (pure ())

def decode_INCH_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 => (execute_INCH_Z_ZS__ 128 dn esize imm pat)
  | 256 => (execute_INCH_Z_ZS__ 256 dn esize imm pat)
  | 512 => (execute_INCH_Z_ZS__ 512 dn esize imm pat)
  | 1024 => (execute_INCH_Z_ZS__ 1024 dn esize imm pat)
  | 2048 => (execute_INCH_Z_ZS__ 2048 dn esize imm pat)
  | _ => (pure ())

def decode_INCW_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 => (execute_INCW_Z_ZS__ 128 dn esize imm pat)
  | 256 => (execute_INCW_Z_ZS__ 256 dn esize imm pat)
  | 512 => (execute_INCW_Z_ZS__ 512 dn esize imm pat)
  | 1024 => (execute_INCW_Z_ZS__ 1024 dn esize imm pat)
  | 2048 => (execute_INCW_Z_ZS__ 2048 dn esize imm pat)
  | _ => (pure ())

def decode_INCD_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  match VL with
  | 128 => (execute_INCD_Z_ZS__ 128 dn esize imm pat)
  | 256 => (execute_INCD_Z_ZS__ 256 dn esize imm pat)
  | 512 => (execute_INCD_Z_ZS__ 512 dn esize imm pat)
  | 1024 => (execute_INCD_Z_ZS__ 1024 dn esize imm pat)
  | 2048 => (execute_INCD_Z_ZS__ 2048 dn esize imm pat)
  | _ => (pure ())

def decode_UQINCH_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UQINCH_Z_ZS__ 128 dn esize imm pat is_unsigned)
  | 256 => (execute_UQINCH_Z_ZS__ 256 dn esize imm pat is_unsigned)
  | 512 => (execute_UQINCH_Z_ZS__ 512 dn esize imm pat is_unsigned)
  | 1024 => (execute_UQINCH_Z_ZS__ 1024 dn esize imm pat is_unsigned)
  | 2048 => (execute_UQINCH_Z_ZS__ 2048 dn esize imm pat is_unsigned)
  | _ => (pure ())

def decode_UQINCW_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UQINCW_Z_ZS__ 128 dn esize imm pat is_unsigned)
  | 256 => (execute_UQINCW_Z_ZS__ 256 dn esize imm pat is_unsigned)
  | 512 => (execute_UQINCW_Z_ZS__ 512 dn esize imm pat is_unsigned)
  | 1024 => (execute_UQINCW_Z_ZS__ 1024 dn esize imm pat is_unsigned)
  | 2048 => (execute_UQINCW_Z_ZS__ 2048 dn esize imm pat is_unsigned)
  | _ => (pure ())

def decode_UQINCD_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UQINCD_Z_ZS__ 128 dn esize imm pat is_unsigned)
  | 256 => (execute_UQINCD_Z_ZS__ 256 dn esize imm pat is_unsigned)
  | 512 => (execute_UQINCD_Z_ZS__ 512 dn esize imm pat is_unsigned)
  | 1024 => (execute_UQINCD_Z_ZS__ 1024 dn esize imm pat is_unsigned)
  | 2048 => (execute_UQINCD_Z_ZS__ 2048 dn esize imm pat is_unsigned)
  | _ => (pure ())

def decode_SQINCH_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SQINCH_Z_ZS__ 128 dn esize imm pat is_unsigned)
  | 256 => (execute_SQINCH_Z_ZS__ 256 dn esize imm pat is_unsigned)
  | 512 => (execute_SQINCH_Z_ZS__ 512 dn esize imm pat is_unsigned)
  | 1024 => (execute_SQINCH_Z_ZS__ 1024 dn esize imm pat is_unsigned)
  | 2048 => (execute_SQINCH_Z_ZS__ 2048 dn esize imm pat is_unsigned)
  | _ => (pure ())

def decode_SQINCW_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SQINCW_Z_ZS__ 128 dn esize imm pat is_unsigned)
  | 256 => (execute_SQINCW_Z_ZS__ 256 dn esize imm pat is_unsigned)
  | 512 => (execute_SQINCW_Z_ZS__ 512 dn esize imm pat is_unsigned)
  | 1024 => (execute_SQINCW_Z_ZS__ 1024 dn esize imm pat is_unsigned)
  | 2048 => (execute_SQINCW_Z_ZS__ 2048 dn esize imm pat is_unsigned)
  | _ => (pure ())

def decode_SQINCD_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SQINCD_Z_ZS__ 128 dn esize imm pat is_unsigned)
  | 256 => (execute_SQINCD_Z_ZS__ 256 dn esize imm pat is_unsigned)
  | 512 => (execute_SQINCD_Z_ZS__ 512 dn esize imm pat is_unsigned)
  | 1024 => (execute_SQINCD_Z_ZS__ 1024 dn esize imm pat is_unsigned)
  | 2048 => (execute_SQINCD_Z_ZS__ 2048 dn esize imm pat is_unsigned)
  | _ => (pure ())

def decode_UQDECH_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UQDECH_Z_ZS__ 128 dn esize imm pat is_unsigned)
  | 256 => (execute_UQDECH_Z_ZS__ 256 dn esize imm pat is_unsigned)
  | 512 => (execute_UQDECH_Z_ZS__ 512 dn esize imm pat is_unsigned)
  | 1024 => (execute_UQDECH_Z_ZS__ 1024 dn esize imm pat is_unsigned)
  | 2048 => (execute_UQDECH_Z_ZS__ 2048 dn esize imm pat is_unsigned)
  | _ => (pure ())

def decode_UQDECW_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UQDECW_Z_ZS__ 128 dn esize imm pat is_unsigned)
  | 256 => (execute_UQDECW_Z_ZS__ 256 dn esize imm pat is_unsigned)
  | 512 => (execute_UQDECW_Z_ZS__ 512 dn esize imm pat is_unsigned)
  | 1024 => (execute_UQDECW_Z_ZS__ 1024 dn esize imm pat is_unsigned)
  | 2048 => (execute_UQDECW_Z_ZS__ 2048 dn esize imm pat is_unsigned)
  | _ => (pure ())

def decode_UQDECD_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UQDECD_Z_ZS__ 128 dn esize imm pat is_unsigned)
  | 256 => (execute_UQDECD_Z_ZS__ 256 dn esize imm pat is_unsigned)
  | 512 => (execute_UQDECD_Z_ZS__ 512 dn esize imm pat is_unsigned)
  | 1024 => (execute_UQDECD_Z_ZS__ 1024 dn esize imm pat is_unsigned)
  | 2048 => (execute_UQDECD_Z_ZS__ 2048 dn esize imm pat is_unsigned)
  | _ => (pure ())

def decode_SQDECH_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SQDECH_Z_ZS__ 128 dn esize imm pat is_unsigned)
  | 256 => (execute_SQDECH_Z_ZS__ 256 dn esize imm pat is_unsigned)
  | 512 => (execute_SQDECH_Z_ZS__ 512 dn esize imm pat is_unsigned)
  | 1024 => (execute_SQDECH_Z_ZS__ 1024 dn esize imm pat is_unsigned)
  | 2048 => (execute_SQDECH_Z_ZS__ 2048 dn esize imm pat is_unsigned)
  | _ => (pure ())

def decode_SQDECW_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SQDECW_Z_ZS__ 128 dn esize imm pat is_unsigned)
  | 256 => (execute_SQDECW_Z_ZS__ 256 dn esize imm pat is_unsigned)
  | 512 => (execute_SQDECW_Z_ZS__ 512 dn esize imm pat is_unsigned)
  | 1024 => (execute_SQDECW_Z_ZS__ 1024 dn esize imm pat is_unsigned)
  | 2048 => (execute_SQDECW_Z_ZS__ 2048 dn esize imm pat is_unsigned)
  | _ => (pure ())

def decode_SQDECD_Z_ZS__ (size : (BitVec 2)) (imm4 : (BitVec 4)) (D : (BitVec 1)) (U : (BitVec 1)) (pattern : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let dn := (BitVec.toNat Zdn)
  let pat : (BitVec 5) := pattern
  let imm := ((BitVec.toNat imm4) +i 1)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SQDECD_Z_ZS__ 128 dn esize imm pat is_unsigned)
  | 256 => (execute_SQDECD_Z_ZS__ 256 dn esize imm pat is_unsigned)
  | 512 => (execute_SQDECD_Z_ZS__ 512 dn esize imm pat is_unsigned)
  | 1024 => (execute_SQDECD_Z_ZS__ 1024 dn esize imm pat is_unsigned)
  | 2048 => (execute_SQDECD_Z_ZS__ 2048 dn esize imm pat is_unsigned)
  | _ => (pure ())

def decode_CTERMEQ_RR__ (sz : (BitVec 1)) (Rm : (BitVec 5)) (Rn : (BitVec 5)) (ne : (BitVec 1)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let op : SVECmp := Cmp_EQ
  (execute_CTERMEQ_RR__ esize m n op)

def decode_CTERMNE_RR__ (sz : (BitVec 1)) (Rm : (BitVec 5)) (Rn : (BitVec 5)) (ne : (BitVec 1)) : SailM Unit := do
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let op : SVECmp := Cmp_NE
  (execute_CTERMNE_RR__ esize m n op)

def decode_FDUP_Z_I__ (size : (BitVec 2)) (imm8 : (BitVec 8)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let d := (BitVec.toNat Zd)
  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:23403.45-23403.46"
  let imm ← (( do (VFPExpandImm imm8 esize) ) : SailM (BitVec esize) )
  match VL with
  | 128 => (execute_FDUP_Z_I__ 128 d esize imm)
  | 256 => (execute_FDUP_Z_I__ 256 d esize imm)
  | 512 => (execute_FDUP_Z_I__ 512 d esize imm)
  | 1024 => (execute_FDUP_Z_I__ 1024 d esize imm)
  | 2048 => (execute_FDUP_Z_I__ 2048 d esize imm)
  | _ => (pure ())

def decode_FCPY_Z_P_I__ (size : (BitVec 2)) (Pg : (BitVec 4)) (imm8 : (BitVec 8)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let d := (BitVec.toNat Zd)
  sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64_sve.sail:23466.45-23466.46"
  let imm ← (( do (VFPExpandImm imm8 esize) ) : SailM (BitVec esize) )
  match VL with
  | 128 => (execute_FCPY_Z_P_I__ 128 d esize g imm)
  | 256 => (execute_FCPY_Z_P_I__ 256 d esize g imm)
  | 512 => (execute_FCPY_Z_P_I__ 512 d esize g imm)
  | 1024 => (execute_FCPY_Z_P_I__ 1024 d esize g imm)
  | 2048 => (execute_FCPY_Z_P_I__ 2048 d esize g imm)
  | _ => (pure ())

def decode_DUP_Z_I__ (size : (BitVec 2)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size +++ sh) == 0b001#3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let d := (BitVec.toNat Zd)
  let imm : Int := (BitVec.toInt imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm := imm
  match VL with
  | 128 => (execute_DUP_Z_I__ 128 d esize imm)
  | 256 => (execute_DUP_Z_I__ 256 d esize imm)
  | 512 => (execute_DUP_Z_I__ 512 d esize imm)
  | 1024 => (execute_DUP_Z_I__ 1024 d esize imm)
  | 2048 => (execute_DUP_Z_I__ 2048 d esize imm)
  | _ => (pure ())

def decode_CPY_Z_P_I__ (size : (BitVec 2)) (Pg : (BitVec 4)) (M : (BitVec 1)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size +++ sh) == 0b001#3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let d := (BitVec.toNat Zd)
  let merging : Bool := true
  let imm : Int := (BitVec.toInt imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm := imm
  match VL with
  | 128 => (execute_CPY_Z_P_I__ 128 d esize g imm merging)
  | 256 => (execute_CPY_Z_P_I__ 256 d esize g imm merging)
  | 512 => (execute_CPY_Z_P_I__ 512 d esize g imm merging)
  | 1024 => (execute_CPY_Z_P_I__ 1024 d esize g imm merging)
  | 2048 => (execute_CPY_Z_P_I__ 2048 d esize g imm merging)
  | _ => (pure ())

def decode_CPY_Z_O_I__ (size : (BitVec 2)) (Pg : (BitVec 4)) (M : (BitVec 1)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size +++ sh) == 0b001#3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let d := (BitVec.toNat Zd)
  let merging : Bool := false
  let imm : Int := (BitVec.toInt imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm := imm
  match VL with
  | 128 => (execute_CPY_Z_O_I__ 128 d esize g imm merging)
  | 256 => (execute_CPY_Z_O_I__ 256 d esize g imm merging)
  | 512 => (execute_CPY_Z_O_I__ 512 d esize g imm merging)
  | 1024 => (execute_CPY_Z_O_I__ 1024 d esize g imm merging)
  | 2048 => (execute_CPY_Z_O_I__ 2048 d esize g imm merging)
  | _ => (pure ())

def decode_DUPM_Z_I__ (imm13 : (BitVec 13)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let d := (BitVec.toNat Zd)
  let imm ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let imm ← (( do
    let (__tup_0, _) ← do (DecodeBitMasks (BitVec.join1 [(BitVec.access imm13 12)]) (Sail.BitVec.extractLsb imm13 5 0) (Sail.BitVec.extractLsb imm13 11 6) true esize)
    (pure __tup_0) ) : SailM (BitVec esize) )
  match VL with
  | 128 => (execute_DUPM_Z_I__ 128 d esize imm)
  | 256 => (execute_DUPM_Z_I__ 256 d esize imm)
  | 512 => (execute_DUPM_Z_I__ 512 d esize imm)
  | 1024 => (execute_DUPM_Z_I__ 1024 d esize imm)
  | 2048 => (execute_DUPM_Z_I__ 2048 d esize imm)
  | _ => (pure ())

def decode_UXTB_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let s_esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UXTB_Z_P_Z__ 128 d esize g n s_esize is_unsigned)
  | 256 => (execute_UXTB_Z_P_Z__ 256 d esize g n s_esize is_unsigned)
  | 512 => (execute_UXTB_Z_P_Z__ 512 d esize g n s_esize is_unsigned)
  | 1024 => (execute_UXTB_Z_P_Z__ 1024 d esize g n s_esize is_unsigned)
  | 2048 => (execute_UXTB_Z_P_Z__ 2048 d esize g n s_esize is_unsigned)
  | _ => (pure ())

def decode_UXTH_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((let b__0 := size
     if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
     then true
     else false : Bool) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let s_esize := 16
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UXTH_Z_P_Z__ 128 d esize g n s_esize is_unsigned)
  | 256 => (execute_UXTH_Z_P_Z__ 256 d esize g n s_esize is_unsigned)
  | 512 => (execute_UXTH_Z_P_Z__ 512 d esize g n s_esize is_unsigned)
  | 1024 => (execute_UXTH_Z_P_Z__ 1024 d esize g n s_esize is_unsigned)
  | 2048 => (execute_UXTH_Z_P_Z__ 2048 d esize g n s_esize is_unsigned)
  | _ => (pure ())

def decode_UXTW_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let s_esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UXTW_Z_P_Z__ 128 d esize g n s_esize is_unsigned)
  | 256 => (execute_UXTW_Z_P_Z__ 256 d esize g n s_esize is_unsigned)
  | 512 => (execute_UXTW_Z_P_Z__ 512 d esize g n s_esize is_unsigned)
  | 1024 => (execute_UXTW_Z_P_Z__ 1024 d esize g n s_esize is_unsigned)
  | 2048 => (execute_UXTW_Z_P_Z__ 2048 d esize g n s_esize is_unsigned)
  | _ => (pure ())

def decode_SXTB_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let s_esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SXTB_Z_P_Z__ 128 d esize g n s_esize is_unsigned)
  | 256 => (execute_SXTB_Z_P_Z__ 256 d esize g n s_esize is_unsigned)
  | 512 => (execute_SXTB_Z_P_Z__ 512 d esize g n s_esize is_unsigned)
  | 1024 => (execute_SXTB_Z_P_Z__ 1024 d esize g n s_esize is_unsigned)
  | 2048 => (execute_SXTB_Z_P_Z__ 2048 d esize g n s_esize is_unsigned)
  | _ => (pure ())

def decode_SXTH_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((let b__0 := size
     if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
     then true
     else false : Bool) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let s_esize := 16
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SXTH_Z_P_Z__ 128 d esize g n s_esize is_unsigned)
  | 256 => (execute_SXTH_Z_P_Z__ 256 d esize g n s_esize is_unsigned)
  | 512 => (execute_SXTH_Z_P_Z__ 512 d esize g n s_esize is_unsigned)
  | 1024 => (execute_SXTH_Z_P_Z__ 1024 d esize g n s_esize is_unsigned)
  | 2048 => (execute_SXTH_Z_P_Z__ 2048 d esize g n s_esize is_unsigned)
  | _ => (pure ())

def decode_SXTW_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let s_esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SXTW_Z_P_Z__ 128 d esize g n s_esize is_unsigned)
  | 256 => (execute_SXTW_Z_P_Z__ 256 d esize g n s_esize is_unsigned)
  | 512 => (execute_SXTW_Z_P_Z__ 512 d esize g n s_esize is_unsigned)
  | 1024 => (execute_SXTW_Z_P_Z__ 1024 d esize g n s_esize is_unsigned)
  | 2048 => (execute_SXTW_Z_P_Z__ 2048 d esize g n s_esize is_unsigned)
  | _ => (pure ())

def decode_ANDV_R_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_ANDV_R_P_Z__ 128 d esize g n)
  | 256 => (execute_ANDV_R_P_Z__ 256 d esize g n)
  | 512 => (execute_ANDV_R_P_Z__ 512 d esize g n)
  | 1024 => (execute_ANDV_R_P_Z__ 1024 d esize g n)
  | 2048 => (execute_ANDV_R_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_EORV_R_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_EORV_R_P_Z__ 128 d esize g n)
  | 256 => (execute_EORV_R_P_Z__ 256 d esize g n)
  | 512 => (execute_EORV_R_P_Z__ 512 d esize g n)
  | 1024 => (execute_EORV_R_P_Z__ 1024 d esize g n)
  | 2048 => (execute_EORV_R_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_ORV_R_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_ORV_R_P_Z__ 128 d esize g n)
  | 256 => (execute_ORV_R_P_Z__ 256 d esize g n)
  | 512 => (execute_ORV_R_P_Z__ 512 d esize g n)
  | 1024 => (execute_ORV_R_P_Z__ 1024 d esize g n)
  | 2048 => (execute_ORV_R_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_SADDV_R_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_SADDV_R_P_Z__ 128 d esize g n)
  | 256 => (execute_SADDV_R_P_Z__ 256 d esize g n)
  | 512 => (execute_SADDV_R_P_Z__ 512 d esize g n)
  | 1024 => (execute_SADDV_R_P_Z__ 1024 d esize g n)
  | 2048 => (execute_SADDV_R_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_UADDV_R_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_UADDV_R_P_Z__ 128 d esize g n)
  | 256 => (execute_UADDV_R_P_Z__ 256 d esize g n)
  | 512 => (execute_UADDV_R_P_Z__ 512 d esize g n)
  | 1024 => (execute_UADDV_R_P_Z__ 1024 d esize g n)
  | 2048 => (execute_UADDV_R_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_UMAXV_R_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMAXV_R_P_Z__ 128 d esize g n is_unsigned)
  | 256 => (execute_UMAXV_R_P_Z__ 256 d esize g n is_unsigned)
  | 512 => (execute_UMAXV_R_P_Z__ 512 d esize g n is_unsigned)
  | 1024 => (execute_UMAXV_R_P_Z__ 1024 d esize g n is_unsigned)
  | 2048 => (execute_UMAXV_R_P_Z__ 2048 d esize g n is_unsigned)
  | _ => (pure ())

def decode_SMAXV_R_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMAXV_R_P_Z__ 128 d esize g n is_unsigned)
  | 256 => (execute_SMAXV_R_P_Z__ 256 d esize g n is_unsigned)
  | 512 => (execute_SMAXV_R_P_Z__ 512 d esize g n is_unsigned)
  | 1024 => (execute_SMAXV_R_P_Z__ 1024 d esize g n is_unsigned)
  | 2048 => (execute_SMAXV_R_P_Z__ 2048 d esize g n is_unsigned)
  | _ => (pure ())

def decode_UMINV_R_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMINV_R_P_Z__ 128 d esize g n is_unsigned)
  | 256 => (execute_UMINV_R_P_Z__ 256 d esize g n is_unsigned)
  | 512 => (execute_UMINV_R_P_Z__ 512 d esize g n is_unsigned)
  | 1024 => (execute_UMINV_R_P_Z__ 1024 d esize g n is_unsigned)
  | 2048 => (execute_UMINV_R_P_Z__ 2048 d esize g n is_unsigned)
  | _ => (pure ())

def decode_SMINV_R_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMINV_R_P_Z__ 128 d esize g n is_unsigned)
  | 256 => (execute_SMINV_R_P_Z__ 256 d esize g n is_unsigned)
  | 512 => (execute_SMINV_R_P_Z__ 512 d esize g n is_unsigned)
  | 1024 => (execute_SMINV_R_P_Z__ 1024 d esize g n is_unsigned)
  | 2048 => (execute_SMINV_R_P_Z__ 2048 d esize g n is_unsigned)
  | _ => (pure ())

def decode_INDEX_Z_II__ (size : (BitVec 2)) (imm5b : (BitVec 5)) (imm5 : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let d := (BitVec.toNat Zd)
  let imm1 := (BitVec.toInt imm5)
  let imm2 := (BitVec.toInt imm5b)
  match VL with
  | 128 => (execute_INDEX_Z_II__ 128 d esize imm1 imm2)
  | 256 => (execute_INDEX_Z_II__ 256 d esize imm1 imm2)
  | 512 => (execute_INDEX_Z_II__ 512 d esize imm1 imm2)
  | 1024 => (execute_INDEX_Z_II__ 1024 d esize imm1 imm2)
  | 2048 => (execute_INDEX_Z_II__ 2048 d esize imm1 imm2)
  | _ => (pure ())

def decode_INDEX_Z_IR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (imm5 : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Zd)
  let imm := (BitVec.toInt imm5)
  match VL with
  | 128 => (execute_INDEX_Z_IR__ 128 d esize imm m)
  | 256 => (execute_INDEX_Z_IR__ 256 d esize imm m)
  | 512 => (execute_INDEX_Z_IR__ 512 d esize imm m)
  | 1024 => (execute_INDEX_Z_IR__ 1024 d esize imm m)
  | 2048 => (execute_INDEX_Z_IR__ 2048 d esize imm m)
  | _ => (pure ())

def decode_INDEX_Z_RI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (Rn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Rn)
  let d := (BitVec.toNat Zd)
  let imm := (BitVec.toInt imm5)
  match VL with
  | 128 => (execute_INDEX_Z_RI__ 128 d esize imm n)
  | 256 => (execute_INDEX_Z_RI__ 256 d esize imm n)
  | 512 => (execute_INDEX_Z_RI__ 512 d esize imm n)
  | 1024 => (execute_INDEX_Z_RI__ 1024 d esize imm n)
  | 2048 => (execute_INDEX_Z_RI__ 2048 d esize imm n)
  | _ => (pure ())

def decode_INDEX_Z_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (Rn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_INDEX_Z_RR__ 128 d esize m n)
  | 256 => (execute_INDEX_Z_RR__ 256 d esize m n)
  | 512 => (execute_INDEX_Z_RR__ 512 d esize m n)
  | 1024 => (execute_INDEX_Z_RR__ 1024 d esize m n)
  | 2048 => (execute_INDEX_Z_RR__ 2048 d esize m n)
  | _ => (pure ())

def decode_AND_Z_ZI__ (imm13 : (BitVec 13)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat Zdn)
  let imm ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let imm ← (( do
    let (__tup_0, _) ← do (DecodeBitMasks (BitVec.join1 [(BitVec.access imm13 12)]) (Sail.BitVec.extractLsb imm13 5 0) (Sail.BitVec.extractLsb imm13 11 6) true 64)
    (pure __tup_0) ) : SailM (BitVec 64) )
  match VL with
  | 128 => (execute_AND_Z_ZI__ 128 dn imm)
  | 256 => (execute_AND_Z_ZI__ 256 dn imm)
  | 512 => (execute_AND_Z_ZI__ 512 dn imm)
  | 1024 => (execute_AND_Z_ZI__ 1024 dn imm)
  | 2048 => (execute_AND_Z_ZI__ 2048 dn imm)
  | _ => (pure ())

def decode_EOR_Z_ZI__ (imm13 : (BitVec 13)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat Zdn)
  let imm ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let imm ← (( do
    let (__tup_0, _) ← do (DecodeBitMasks (BitVec.join1 [(BitVec.access imm13 12)]) (Sail.BitVec.extractLsb imm13 5 0) (Sail.BitVec.extractLsb imm13 11 6) true 64)
    (pure __tup_0) ) : SailM (BitVec 64) )
  match VL with
  | 128 => (execute_EOR_Z_ZI__ 128 dn imm)
  | 256 => (execute_EOR_Z_ZI__ 256 dn imm)
  | 512 => (execute_EOR_Z_ZI__ 512 dn imm)
  | 1024 => (execute_EOR_Z_ZI__ 1024 dn imm)
  | 2048 => (execute_EOR_Z_ZI__ 2048 dn imm)
  | _ => (pure ())

def decode_ORR_Z_ZI__ (imm13 : (BitVec 13)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat Zdn)
  let imm ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let imm ← (( do
    let (__tup_0, _) ← do (DecodeBitMasks (BitVec.join1 [(BitVec.access imm13 12)]) (Sail.BitVec.extractLsb imm13 5 0) (Sail.BitVec.extractLsb imm13 11 6) true 64)
    (pure __tup_0) ) : SailM (BitVec 64) )
  match VL with
  | 128 => (execute_ORR_Z_ZI__ 128 dn imm)
  | 256 => (execute_ORR_Z_ZI__ 256 dn imm)
  | 512 => (execute_ORR_Z_ZI__ 512 dn imm)
  | 1024 => (execute_ORR_Z_ZI__ 1024 dn imm)
  | 2048 => (execute_ORR_Z_ZI__ 2048 dn imm)
  | _ => (pure ())

def decode_MAD_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Za : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let a := (BitVec.toNat Za)
  let sub_op : Bool := false
  match VL with
  | 128 => (execute_MAD_Z_P_ZZZ__ 128 a dn esize g m sub_op)
  | 256 => (execute_MAD_Z_P_ZZZ__ 256 a dn esize g m sub_op)
  | 512 => (execute_MAD_Z_P_ZZZ__ 512 a dn esize g m sub_op)
  | 1024 => (execute_MAD_Z_P_ZZZ__ 1024 a dn esize g m sub_op)
  | 2048 => (execute_MAD_Z_P_ZZZ__ 2048 a dn esize g m sub_op)
  | _ => (pure ())

def decode_MSB_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Za : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let a := (BitVec.toNat Za)
  let sub_op : Bool := true
  match VL with
  | 128 => (execute_MSB_Z_P_ZZZ__ 128 a dn esize g m sub_op)
  | 256 => (execute_MSB_Z_P_ZZZ__ 256 a dn esize g m sub_op)
  | 512 => (execute_MSB_Z_P_ZZZ__ 512 a dn esize g m sub_op)
  | 1024 => (execute_MSB_Z_P_ZZZ__ 1024 a dn esize g m sub_op)
  | 2048 => (execute_MSB_Z_P_ZZZ__ 2048 a dn esize g m sub_op)
  | _ => (pure ())

def decode_MLA_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sub_op : Bool := false
  match VL with
  | 128 => (execute_MLA_Z_P_ZZZ__ 128 da esize g m n sub_op)
  | 256 => (execute_MLA_Z_P_ZZZ__ 256 da esize g m n sub_op)
  | 512 => (execute_MLA_Z_P_ZZZ__ 512 da esize g m n sub_op)
  | 1024 => (execute_MLA_Z_P_ZZZ__ 1024 da esize g m n sub_op)
  | 2048 => (execute_MLA_Z_P_ZZZ__ 2048 da esize g m n sub_op)
  | _ => (pure ())

def decode_MLS_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sub_op : Bool := true
  match VL with
  | 128 => (execute_MLS_Z_P_ZZZ__ 128 da esize g m n sub_op)
  | 256 => (execute_MLS_Z_P_ZZZ__ 256 da esize g m n sub_op)
  | 512 => (execute_MLS_Z_P_ZZZ__ 512 da esize g m n sub_op)
  | 1024 => (execute_MLS_Z_P_ZZZ__ 1024 da esize g m n sub_op)
  | 2048 => (execute_MLS_Z_P_ZZZ__ 2048 da esize g m n sub_op)
  | _ => (pure ())

def decode_MOVPRFX_Z_Z__ (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_MOVPRFX_Z_Z__ 128 d n)
  | 256 => (execute_MOVPRFX_Z_Z__ 256 d n)
  | 512 => (execute_MOVPRFX_Z_Z__ 512 d n)
  | 1024 => (execute_MOVPRFX_Z_Z__ 1024 d n)
  | 2048 => (execute_MOVPRFX_Z_Z__ 2048 d n)
  | _ => (pure ())

def decode_MOVPRFX_Z_P_Z__ (size : (BitVec 2)) (M : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let merging : Bool := (M == 1#1)
  match VL with
  | 128 => (execute_MOVPRFX_Z_P_Z__ 128 d esize g merging n)
  | 256 => (execute_MOVPRFX_Z_P_Z__ 256 d esize g merging n)
  | 512 => (execute_MOVPRFX_Z_P_Z__ 512 d esize g merging n)
  | 1024 => (execute_MOVPRFX_Z_P_Z__ 1024 d esize g merging n)
  | 2048 => (execute_MOVPRFX_Z_P_Z__ 2048 d esize g merging n)
  | _ => (pure ())

def decode_CNTP_R_P_P__ (size : (BitVec 2)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Rd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let d := (BitVec.toNat Rd)
  match VL with
  | 128 => (execute_CNTP_R_P_P__ 128 d esize g n)
  | 256 => (execute_CNTP_R_P_P__ 256 d esize g n)
  | 512 => (execute_CNTP_R_P_P__ 512 d esize g n)
  | 1024 => (execute_CNTP_R_P_P__ 1024 d esize g n)
  | 2048 => (execute_CNTP_R_P_P__ 2048 d esize g n)
  | _ => (pure ())

def decode_REV_P_P__ (size : (BitVec 2)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Pn)
  let d := (BitVec.toNat Pd)
  match VL with
  | 128 => (execute_REV_P_P__ 128 d esize n)
  | 256 => (execute_REV_P_P__ 256 d esize n)
  | 512 => (execute_REV_P_P__ 512 d esize n)
  | 1024 => (execute_REV_P_P__ 1024 d esize n)
  | 2048 => (execute_REV_P_P__ 2048 d esize n)
  | _ => (pure ())

def decode_TRN1_P_PP__ (size : (BitVec 2)) (Pm : (BitVec 4)) (H : (BitVec 1)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let part := 0
  match VL with
  | 128 => (execute_TRN1_P_PP__ 128 d esize m n part)
  | 256 => (execute_TRN1_P_PP__ 256 d esize m n part)
  | 512 => (execute_TRN1_P_PP__ 512 d esize m n part)
  | 1024 => (execute_TRN1_P_PP__ 1024 d esize m n part)
  | 2048 => (execute_TRN1_P_PP__ 2048 d esize m n part)
  | _ => (pure ())

def decode_TRN2_P_PP__ (size : (BitVec 2)) (Pm : (BitVec 4)) (H : (BitVec 1)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let part := 1
  match VL with
  | 128 => (execute_TRN2_P_PP__ 128 d esize m n part)
  | 256 => (execute_TRN2_P_PP__ 256 d esize m n part)
  | 512 => (execute_TRN2_P_PP__ 512 d esize m n part)
  | 1024 => (execute_TRN2_P_PP__ 1024 d esize m n part)
  | 2048 => (execute_TRN2_P_PP__ 2048 d esize m n part)
  | _ => (pure ())

def decode_UZP1_P_PP__ (size : (BitVec 2)) (Pm : (BitVec 4)) (H : (BitVec 1)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let part := 0
  match VL with
  | 128 => (execute_UZP1_P_PP__ 128 d esize m n part)
  | 256 => (execute_UZP1_P_PP__ 256 d esize m n part)
  | 512 => (execute_UZP1_P_PP__ 512 d esize m n part)
  | 1024 => (execute_UZP1_P_PP__ 1024 d esize m n part)
  | 2048 => (execute_UZP1_P_PP__ 2048 d esize m n part)
  | _ => (pure ())

def decode_UZP2_P_PP__ (size : (BitVec 2)) (Pm : (BitVec 4)) (H : (BitVec 1)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let part := 1
  match VL with
  | 128 => (execute_UZP2_P_PP__ 128 d esize m n part)
  | 256 => (execute_UZP2_P_PP__ 256 d esize m n part)
  | 512 => (execute_UZP2_P_PP__ 512 d esize m n part)
  | 1024 => (execute_UZP2_P_PP__ 1024 d esize m n part)
  | 2048 => (execute_UZP2_P_PP__ 2048 d esize m n part)
  | _ => (pure ())

def decode_ZIP1_P_PP__ (size : (BitVec 2)) (Pm : (BitVec 4)) (H : (BitVec 1)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let part := 0
  match VL with
  | 128 => (execute_ZIP1_P_PP__ 128 d esize m n part)
  | 256 => (execute_ZIP1_P_PP__ 256 d esize m n part)
  | 512 => (execute_ZIP1_P_PP__ 512 d esize m n part)
  | 1024 => (execute_ZIP1_P_PP__ 1024 d esize m n part)
  | 2048 => (execute_ZIP1_P_PP__ 2048 d esize m n part)
  | _ => (pure ())

def decode_ZIP2_P_PP__ (size : (BitVec 2)) (Pm : (BitVec 4)) (H : (BitVec 1)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let part := 1
  match VL with
  | 128 => (execute_ZIP2_P_PP__ 128 d esize m n part)
  | 256 => (execute_ZIP2_P_PP__ 256 d esize m n part)
  | 512 => (execute_ZIP2_P_PP__ 512 d esize m n part)
  | 1024 => (execute_ZIP2_P_PP__ 1024 d esize m n part)
  | 2048 => (execute_ZIP2_P_PP__ 2048 d esize m n part)
  | _ => (pure ())

def decode_REV_Z_Z__ (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_REV_Z_Z__ 128 d esize n)
  | 256 => (execute_REV_Z_Z__ 256 d esize n)
  | 512 => (execute_REV_Z_Z__ 512 d esize n)
  | 1024 => (execute_REV_Z_Z__ 1024 d esize n)
  | 2048 => (execute_REV_Z_Z__ 2048 d esize n)
  | _ => (pure ())

def decode_TBL_Z_ZZ_1 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let double_table : Bool := false
  match VL with
  | 128 => (execute_TBL_Z_ZZ_1 128 d double_table esize m n)
  | 256 => (execute_TBL_Z_ZZ_1 256 d double_table esize m n)
  | 512 => (execute_TBL_Z_ZZ_1 512 d double_table esize m n)
  | 1024 => (execute_TBL_Z_ZZ_1 1024 d double_table esize m n)
  | 2048 => (execute_TBL_Z_ZZ_1 2048 d double_table esize m n)
  | _ => (pure ())

def decode_TBL_Z_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let double_table : Bool := true
  match VL with
  | 128 => (execute_TBL_Z_ZZ_2 128 d double_table esize m n)
  | 256 => (execute_TBL_Z_ZZ_2 256 d double_table esize m n)
  | 512 => (execute_TBL_Z_ZZ_2 512 d double_table esize m n)
  | 1024 => (execute_TBL_Z_ZZ_2 1024 d double_table esize m n)
  | 2048 => (execute_TBL_Z_ZZ_2 2048 d double_table esize m n)
  | _ => (pure ())

def decode_TRN1_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let part := 0
  match VL with
  | 128 => (execute_TRN1_Z_ZZ__ 128 d esize m n part)
  | 256 => (execute_TRN1_Z_ZZ__ 256 d esize m n part)
  | 512 => (execute_TRN1_Z_ZZ__ 512 d esize m n part)
  | 1024 => (execute_TRN1_Z_ZZ__ 1024 d esize m n part)
  | 2048 => (execute_TRN1_Z_ZZ__ 2048 d esize m n part)
  | _ => (pure ())

def decode_TRN2_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let part := 1
  match VL with
  | 128 => (execute_TRN2_Z_ZZ__ 128 d esize m n part)
  | 256 => (execute_TRN2_Z_ZZ__ 256 d esize m n part)
  | 512 => (execute_TRN2_Z_ZZ__ 512 d esize m n part)
  | 1024 => (execute_TRN2_Z_ZZ__ 1024 d esize m n part)
  | 2048 => (execute_TRN2_Z_ZZ__ 2048 d esize m n part)
  | _ => (pure ())

def decode_UZP1_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let part := 0
  match VL with
  | 128 => (execute_UZP1_Z_ZZ__ 128 d esize m n part)
  | 256 => (execute_UZP1_Z_ZZ__ 256 d esize m n part)
  | 512 => (execute_UZP1_Z_ZZ__ 512 d esize m n part)
  | 1024 => (execute_UZP1_Z_ZZ__ 1024 d esize m n part)
  | 2048 => (execute_UZP1_Z_ZZ__ 2048 d esize m n part)
  | _ => (pure ())

def decode_UZP2_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let part := 1
  match VL with
  | 128 => (execute_UZP2_Z_ZZ__ 128 d esize m n part)
  | 256 => (execute_UZP2_Z_ZZ__ 256 d esize m n part)
  | 512 => (execute_UZP2_Z_ZZ__ 512 d esize m n part)
  | 1024 => (execute_UZP2_Z_ZZ__ 1024 d esize m n part)
  | 2048 => (execute_UZP2_Z_ZZ__ 2048 d esize m n part)
  | _ => (pure ())

def decode_ZIP1_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let part := 0
  match VL with
  | 128 => (execute_ZIP1_Z_ZZ__ 128 d esize m n part)
  | 256 => (execute_ZIP1_Z_ZZ__ 256 d esize m n part)
  | 512 => (execute_ZIP1_Z_ZZ__ 512 d esize m n part)
  | 1024 => (execute_ZIP1_Z_ZZ__ 1024 d esize m n part)
  | 2048 => (execute_ZIP1_Z_ZZ__ 2048 d esize m n part)
  | _ => (pure ())

def decode_ZIP2_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let part := 1
  match VL with
  | 128 => (execute_ZIP2_Z_ZZ__ 128 d esize m n part)
  | 256 => (execute_ZIP2_Z_ZZ__ 256 d esize m n part)
  | 512 => (execute_ZIP2_Z_ZZ__ 512 d esize m n part)
  | 1024 => (execute_ZIP2_Z_ZZ__ 1024 d esize m n part)
  | 2048 => (execute_ZIP2_Z_ZZ__ 2048 d esize m n part)
  | _ => (pure ())

def decode_TRN1_Z_ZZ_Q (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVEFP64MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 128
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let part := 0
  match VL with
  | 128 => (execute_TRN1_Z_ZZ_Q 128 d esize m n part)
  | 256 => (execute_TRN1_Z_ZZ_Q 256 d esize m n part)
  | 512 => (execute_TRN1_Z_ZZ_Q 512 d esize m n part)
  | 1024 => (execute_TRN1_Z_ZZ_Q 1024 d esize m n part)
  | 2048 => (execute_TRN1_Z_ZZ_Q 2048 d esize m n part)
  | _ => (pure ())

def decode_TRN2_Z_ZZ_Q (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVEFP64MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 128
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let part := 1
  match VL with
  | 128 => (execute_TRN2_Z_ZZ_Q 128 d esize m n part)
  | 256 => (execute_TRN2_Z_ZZ_Q 256 d esize m n part)
  | 512 => (execute_TRN2_Z_ZZ_Q 512 d esize m n part)
  | 1024 => (execute_TRN2_Z_ZZ_Q 1024 d esize m n part)
  | 2048 => (execute_TRN2_Z_ZZ_Q 2048 d esize m n part)
  | _ => (pure ())

def decode_ZIP1_Z_ZZ_Q (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVEFP64MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 128
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let part := 0
  match VL with
  | 128 => (execute_ZIP1_Z_ZZ_Q 128 d esize m n part)
  | 256 => (execute_ZIP1_Z_ZZ_Q 256 d esize m n part)
  | 512 => (execute_ZIP1_Z_ZZ_Q 512 d esize m n part)
  | 1024 => (execute_ZIP1_Z_ZZ_Q 1024 d esize m n part)
  | 2048 => (execute_ZIP1_Z_ZZ_Q 2048 d esize m n part)
  | _ => (pure ())

def decode_ZIP2_Z_ZZ_Q (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVEFP64MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 128
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let part := 1
  match VL with
  | 128 => (execute_ZIP2_Z_ZZ_Q 128 d esize m n part)
  | 256 => (execute_ZIP2_Z_ZZ_Q 256 d esize m n part)
  | 512 => (execute_ZIP2_Z_ZZ_Q 512 d esize m n part)
  | 1024 => (execute_ZIP2_Z_ZZ_Q 1024 d esize m n part)
  | 2048 => (execute_ZIP2_Z_ZZ_Q 2048 d esize m n part)
  | _ => (pure ())

def decode_UZP1_Z_ZZ_Q (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVEFP64MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 128
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let part := 0
  match VL with
  | 128 => (execute_UZP1_Z_ZZ_Q 128 d esize m n part)
  | 256 => (execute_UZP1_Z_ZZ_Q 256 d esize m n part)
  | 512 => (execute_UZP1_Z_ZZ_Q 512 d esize m n part)
  | 1024 => (execute_UZP1_Z_ZZ_Q 1024 d esize m n part)
  | 2048 => (execute_UZP1_Z_ZZ_Q 2048 d esize m n part)
  | _ => (pure ())

def decode_UZP2_Z_ZZ_Q (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVEFP64MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 128
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let part := 1
  match VL with
  | 128 => (execute_UZP2_Z_ZZ_Q 128 d esize m n part)
  | 256 => (execute_UZP2_Z_ZZ_Q 256 d esize m n part)
  | 512 => (execute_UZP2_Z_ZZ_Q 512 d esize m n part)
  | 1024 => (execute_UZP2_Z_ZZ_Q 1024 d esize m n part)
  | 2048 => (execute_UZP2_Z_ZZ_Q 2048 d esize m n part)
  | _ => (pure ())

def decode_CLASTA_R_P_Z__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Rdn)
  let m := (BitVec.toNat Zm)
  let csize :=
    if ((esize <b 64) : Bool)
    then 32
    else 64
  let isBefore : Bool := false
  match VL with
  | 128 => (execute_CLASTA_R_P_Z__ 128 csize dn esize g isBefore m)
  | 256 => (execute_CLASTA_R_P_Z__ 256 csize dn esize g isBefore m)
  | 512 => (execute_CLASTA_R_P_Z__ 512 csize dn esize g isBefore m)
  | 1024 => (execute_CLASTA_R_P_Z__ 1024 csize dn esize g isBefore m)
  | 2048 => (execute_CLASTA_R_P_Z__ 2048 csize dn esize g isBefore m)
  | _ => (pure ())

def decode_CLASTB_R_P_Z__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Rdn)
  let m := (BitVec.toNat Zm)
  let csize :=
    if ((esize <b 64) : Bool)
    then 32
    else 64
  let isBefore : Bool := true
  match VL with
  | 128 => (execute_CLASTB_R_P_Z__ 128 csize dn esize g isBefore m)
  | 256 => (execute_CLASTB_R_P_Z__ 256 csize dn esize g isBefore m)
  | 512 => (execute_CLASTB_R_P_Z__ 512 csize dn esize g isBefore m)
  | 1024 => (execute_CLASTB_R_P_Z__ 1024 csize dn esize g isBefore m)
  | 2048 => (execute_CLASTB_R_P_Z__ 2048 csize dn esize g isBefore m)
  | _ => (pure ())

def decode_CLASTA_V_P_Z__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Vdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Vdn)
  let m := (BitVec.toNat Zm)
  let isBefore : Bool := false
  match VL with
  | 128 => (execute_CLASTA_V_P_Z__ 128 dn esize g isBefore m)
  | 256 => (execute_CLASTA_V_P_Z__ 256 dn esize g isBefore m)
  | 512 => (execute_CLASTA_V_P_Z__ 512 dn esize g isBefore m)
  | 1024 => (execute_CLASTA_V_P_Z__ 1024 dn esize g isBefore m)
  | 2048 => (execute_CLASTA_V_P_Z__ 2048 dn esize g isBefore m)
  | _ => (pure ())

def decode_CLASTB_V_P_Z__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Vdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Vdn)
  let m := (BitVec.toNat Zm)
  let isBefore : Bool := true
  match VL with
  | 128 => (execute_CLASTB_V_P_Z__ 128 dn esize g isBefore m)
  | 256 => (execute_CLASTB_V_P_Z__ 256 dn esize g isBefore m)
  | 512 => (execute_CLASTB_V_P_Z__ 512 dn esize g isBefore m)
  | 1024 => (execute_CLASTB_V_P_Z__ 1024 dn esize g isBefore m)
  | 2048 => (execute_CLASTB_V_P_Z__ 2048 dn esize g isBefore m)
  | _ => (pure ())

def decode_CLASTA_Z_P_ZZ__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let isBefore : Bool := false
  match VL with
  | 128 => (execute_CLASTA_Z_P_ZZ__ 128 dn esize g isBefore m)
  | 256 => (execute_CLASTA_Z_P_ZZ__ 256 dn esize g isBefore m)
  | 512 => (execute_CLASTA_Z_P_ZZ__ 512 dn esize g isBefore m)
  | 1024 => (execute_CLASTA_Z_P_ZZ__ 1024 dn esize g isBefore m)
  | 2048 => (execute_CLASTA_Z_P_ZZ__ 2048 dn esize g isBefore m)
  | _ => (pure ())

def decode_CLASTB_Z_P_ZZ__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let isBefore : Bool := true
  match VL with
  | 128 => (execute_CLASTB_Z_P_ZZ__ 128 dn esize g isBefore m)
  | 256 => (execute_CLASTB_Z_P_ZZ__ 256 dn esize g isBefore m)
  | 512 => (execute_CLASTB_Z_P_ZZ__ 512 dn esize g isBefore m)
  | 1024 => (execute_CLASTB_Z_P_ZZ__ 1024 dn esize g isBefore m)
  | 2048 => (execute_CLASTB_Z_P_ZZ__ 2048 dn esize g isBefore m)
  | _ => (pure ())

def decode_COMPACT_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((let b__0 := size
     if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
     then true
     else false : Bool) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_COMPACT_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_COMPACT_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_COMPACT_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_COMPACT_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_COMPACT_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_SPLICE_Z_P_ZZ_Des (size : (BitVec 2)) (Pv : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let v := (BitVec.toNat Pv)
  let dst := (BitVec.toNat Zdn)
  let s1 := dst
  let s2 := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_SPLICE_Z_P_ZZ_Des 128 dst esize s1 s2 v)
  | 256 => (execute_SPLICE_Z_P_ZZ_Des 256 dst esize s1 s2 v)
  | 512 => (execute_SPLICE_Z_P_ZZ_Des 512 dst esize s1 s2 v)
  | 1024 => (execute_SPLICE_Z_P_ZZ_Des 1024 dst esize s1 s2 v)
  | 2048 => (execute_SPLICE_Z_P_ZZ_Des 2048 dst esize s1 s2 v)
  | _ => (pure ())

def decode_SPLICE_Z_P_ZZ_Con (size : (BitVec 2)) (Pv : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let v := (BitVec.toNat Pv)
  let dst := (BitVec.toNat Zd)
  let s1 := (BitVec.toNat Zn)
  let s2 := (Nat.mod (s1 +i 1) 32)
  match VL with
  | 128 => (execute_SPLICE_Z_P_ZZ_Con 128 dst esize s1 s2 v)
  | 256 => (execute_SPLICE_Z_P_ZZ_Con 256 dst esize s1 s2 v)
  | 512 => (execute_SPLICE_Z_P_ZZ_Con 512 dst esize s1 s2 v)
  | 1024 => (execute_SPLICE_Z_P_ZZ_Con 1024 dst esize s1 s2 v)
  | 2048 => (execute_SPLICE_Z_P_ZZ_Con 2048 dst esize s1 s2 v)
  | _ => (pure ())

def decode_EXT_Z_ZI_Des (imm8h : (BitVec 5)) (imm8l : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let dst := (BitVec.toNat Zdn)
  let s1 := dst
  let s2 := (BitVec.toNat Zm)
  let position := (BitVec.toNat (imm8h +++ imm8l))
  match VL with
  | 128 => (execute_EXT_Z_ZI_Des 128 dst esize position s1 s2)
  | 256 => (execute_EXT_Z_ZI_Des 256 dst esize position s1 s2)
  | 512 => (execute_EXT_Z_ZI_Des 512 dst esize position s1 s2)
  | 1024 => (execute_EXT_Z_ZI_Des 1024 dst esize position s1 s2)
  | 2048 => (execute_EXT_Z_ZI_Des 2048 dst esize position s1 s2)
  | _ => (pure ())

def decode_EXT_Z_ZI_Con (imm8h : (BitVec 5)) (imm8l : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let dst := (BitVec.toNat Zd)
  let s1 := (BitVec.toNat Zn)
  let s2 := (Nat.mod (s1 +i 1) 32)
  let position := (BitVec.toNat (imm8h +++ imm8l))
  match VL with
  | 128 => (execute_EXT_Z_ZI_Con 128 dst esize position s1 s2)
  | 256 => (execute_EXT_Z_ZI_Con 256 dst esize position s1 s2)
  | 512 => (execute_EXT_Z_ZI_Con 512 dst esize position s1 s2)
  | 1024 => (execute_EXT_Z_ZI_Con 1024 dst esize position s1 s2)
  | 2048 => (execute_EXT_Z_ZI_Con 2048 dst esize position s1 s2)
  | _ => (pure ())

def decode_CPY_Z_P_R__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_CPY_Z_P_R__ 128 d esize g n)
  | 256 => (execute_CPY_Z_P_R__ 256 d esize g n)
  | 512 => (execute_CPY_Z_P_R__ 512 d esize g n)
  | 1024 => (execute_CPY_Z_P_R__ 1024 d esize g n)
  | 2048 => (execute_CPY_Z_P_R__ 2048 d esize g n)
  | _ => (pure ())

def decode_CPY_Z_P_V__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Vn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Vn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_CPY_Z_P_V__ 128 d esize g n)
  | 256 => (execute_CPY_Z_P_V__ 256 d esize g n)
  | 512 => (execute_CPY_Z_P_V__ 512 d esize g n)
  | 1024 => (execute_CPY_Z_P_V__ 1024 d esize g n)
  | 2048 => (execute_CPY_Z_P_V__ 2048 d esize g n)
  | _ => (pure ())

def decode_DUP_Z_Zi__ (imm2 : (BitVec 2)) (tsz : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let imm : (BitVec 7) := (imm2 +++ tsz)
  let esize : Nat := 8
  let index ← (( do (undefined_range 0 63) ) : SailM Nat )
  let (esize, index) ← (( do
    let b__0 := tsz
    let (esize, index) ← (( do
      if ((b__0 == (0b00000#5 : (BitVec 5))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (let (esize, index) : (Int × Nat) :=
          if ((b__0 == (0b10000#5 : (BitVec 5))) : Bool)
          then
            (let esize : Nat := 128
            let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 6 5))
            (esize, index))
          else
            (let (esize, index) : (Int × Nat) :=
              if (((Sail.BitVec.extractLsb b__0 3 0) == (0x8#4 : (BitVec 4))) : Bool)
              then
                (let esize : Nat := 64
                let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 6 4))
                (esize, index))
              else
                (let (esize, index) : (Int × Nat) :=
                  if (((Sail.BitVec.extractLsb b__0 2 0) == (0b100#3 : (BitVec 3))) : Bool)
                  then
                    (let esize : Nat := 32
                    let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 6 3))
                    (esize, index))
                  else
                    (let (esize, index) : (Int × Nat) :=
                      if (((Sail.BitVec.extractLsb b__0 1 0) == (0b10#2 : (BitVec 2))) : Bool)
                      then
                        (let esize : Nat := 16
                        let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 6 2))
                        (esize, index))
                      else
                        (let esize : Nat := 8
                        let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 6 1))
                        (esize, index))
                    (esize, index))
                (esize, index))
            (esize, index))
        (pure (esize, index))) ) : SailM (Int × Nat) )
    (pure (esize, index)) ) : SailM (Int × Nat) )
  let index := index
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_DUP_Z_Zi__ 128 d esize index n)
  | 256 => (execute_DUP_Z_Zi__ 256 d esize index n)
  | 512 => (execute_DUP_Z_Zi__ 512 d esize index n)
  | 1024 => (execute_DUP_Z_Zi__ 1024 d esize index n)
  | 2048 => (execute_DUP_Z_Zi__ 2048 d esize index n)
  | _ => (pure ())

def decode_DUP_Z_R__ (size : (BitVec 2)) (Rn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Rn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_DUP_Z_R__ 128 d esize n)
  | 256 => (execute_DUP_Z_R__ 256 d esize n)
  | 512 => (execute_DUP_Z_R__ 512 d esize n)
  | 1024 => (execute_DUP_Z_R__ 1024 d esize n)
  | 2048 => (execute_DUP_Z_R__ 2048 d esize n)
  | _ => (pure ())

def decode_LASTA_R_P_Z__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Rd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize :=
    if ((esize <b 64) : Bool)
    then 32
    else 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Rd)
  let isBefore : Bool := false
  match VL with
  | 128 => (execute_LASTA_R_P_Z__ 128 d esize g isBefore n rsize)
  | 256 => (execute_LASTA_R_P_Z__ 256 d esize g isBefore n rsize)
  | 512 => (execute_LASTA_R_P_Z__ 512 d esize g isBefore n rsize)
  | 1024 => (execute_LASTA_R_P_Z__ 1024 d esize g isBefore n rsize)
  | 2048 => (execute_LASTA_R_P_Z__ 2048 d esize g isBefore n rsize)
  | _ => (pure ())

def decode_LASTB_R_P_Z__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Rd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize :=
    if ((esize <b 64) : Bool)
    then 32
    else 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Rd)
  let isBefore : Bool := true
  match VL with
  | 128 => (execute_LASTB_R_P_Z__ 128 d esize g isBefore n rsize)
  | 256 => (execute_LASTB_R_P_Z__ 256 d esize g isBefore n rsize)
  | 512 => (execute_LASTB_R_P_Z__ 512 d esize g isBefore n rsize)
  | 1024 => (execute_LASTB_R_P_Z__ 1024 d esize g isBefore n rsize)
  | 2048 => (execute_LASTB_R_P_Z__ 2048 d esize g isBefore n rsize)
  | _ => (pure ())

def decode_LASTA_V_P_Z__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  let isBefore : Bool := false
  match VL with
  | 128 => (execute_LASTA_V_P_Z__ 128 d esize g isBefore n)
  | 256 => (execute_LASTA_V_P_Z__ 256 d esize g isBefore n)
  | 512 => (execute_LASTA_V_P_Z__ 512 d esize g isBefore n)
  | 1024 => (execute_LASTA_V_P_Z__ 1024 d esize g isBefore n)
  | 2048 => (execute_LASTA_V_P_Z__ 2048 d esize g isBefore n)
  | _ => (pure ())

def decode_LASTB_V_P_Z__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  let isBefore : Bool := true
  match VL with
  | 128 => (execute_LASTB_V_P_Z__ 128 d esize g isBefore n)
  | 256 => (execute_LASTB_V_P_Z__ 256 d esize g isBefore n)
  | 512 => (execute_LASTB_V_P_Z__ 512 d esize g isBefore n)
  | 1024 => (execute_LASTB_V_P_Z__ 1024 d esize g isBefore n)
  | 2048 => (execute_LASTB_V_P_Z__ 2048 d esize g isBefore n)
  | _ => (pure ())

def decode_PUNPKLO_P_P__ (H : (BitVec 1)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let n := (BitVec.toNat Pn)
  let d := (BitVec.toNat Pd)
  let hi : Bool := false
  match VL with
  | 128 => (execute_PUNPKLO_P_P__ 128 d esize hi n)
  | 256 => (execute_PUNPKLO_P_P__ 256 d esize hi n)
  | 512 => (execute_PUNPKLO_P_P__ 512 d esize hi n)
  | 1024 => (execute_PUNPKLO_P_P__ 1024 d esize hi n)
  | 2048 => (execute_PUNPKLO_P_P__ 2048 d esize hi n)
  | _ => (pure ())

def decode_PUNPKHI_P_P__ (H : (BitVec 1)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let n := (BitVec.toNat Pn)
  let d := (BitVec.toNat Pd)
  let hi : Bool := true
  match VL with
  | 128 => (execute_PUNPKHI_P_P__ 128 d esize hi n)
  | 256 => (execute_PUNPKHI_P_P__ 256 d esize hi n)
  | 512 => (execute_PUNPKHI_P_P__ 512 d esize hi n)
  | 1024 => (execute_PUNPKHI_P_P__ 1024 d esize hi n)
  | 2048 => (execute_PUNPKHI_P_P__ 2048 d esize hi n)
  | _ => (pure ())

def decode_REVW_Z_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let swsize := 32
  match VL with
  | 128 => (execute_REVW_Z_Z__ 128 d esize g n swsize)
  | 256 => (execute_REVW_Z_Z__ 256 d esize g n swsize)
  | 512 => (execute_REVW_Z_Z__ 512 d esize g n swsize)
  | 1024 => (execute_REVW_Z_Z__ 1024 d esize g n swsize)
  | 2048 => (execute_REVW_Z_Z__ 2048 d esize g n swsize)
  | _ => (pure ())

def decode_REVH_Z_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((let b__0 := size
     if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
     then true
     else false : Bool) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let swsize := 16
  match VL with
  | 128 => (execute_REVH_Z_Z__ 128 d esize g n swsize)
  | 256 => (execute_REVH_Z_Z__ 256 d esize g n swsize)
  | 512 => (execute_REVH_Z_Z__ 512 d esize g n swsize)
  | 1024 => (execute_REVH_Z_Z__ 1024 d esize g n swsize)
  | 2048 => (execute_REVH_Z_Z__ 2048 d esize g n swsize)
  | _ => (pure ())

def decode_REVB_Z_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let swsize := 8
  match VL with
  | 128 => (execute_REVB_Z_Z__ 128 d esize g n swsize)
  | 256 => (execute_REVB_Z_Z__ 256 d esize g n swsize)
  | 512 => (execute_REVB_Z_Z__ 512 d esize g n swsize)
  | 1024 => (execute_REVB_Z_Z__ 1024 d esize g n swsize)
  | 2048 => (execute_REVB_Z_Z__ 2048 d esize g n swsize)
  | _ => (pure ())

def decode_UUNPKLO_Z_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let is_unsigned : Bool := true
  let hi : Bool := false
  match VL with
  | 128 => (execute_UUNPKLO_Z_Z__ 128 d esize hi n is_unsigned)
  | 256 => (execute_UUNPKLO_Z_Z__ 256 d esize hi n is_unsigned)
  | 512 => (execute_UUNPKLO_Z_Z__ 512 d esize hi n is_unsigned)
  | 1024 => (execute_UUNPKLO_Z_Z__ 1024 d esize hi n is_unsigned)
  | 2048 => (execute_UUNPKLO_Z_Z__ 2048 d esize hi n is_unsigned)
  | _ => (pure ())

def decode_UUNPKHI_Z_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let is_unsigned : Bool := true
  let hi : Bool := true
  match VL with
  | 128 => (execute_UUNPKHI_Z_Z__ 128 d esize hi n is_unsigned)
  | 256 => (execute_UUNPKHI_Z_Z__ 256 d esize hi n is_unsigned)
  | 512 => (execute_UUNPKHI_Z_Z__ 512 d esize hi n is_unsigned)
  | 1024 => (execute_UUNPKHI_Z_Z__ 1024 d esize hi n is_unsigned)
  | 2048 => (execute_UUNPKHI_Z_Z__ 2048 d esize hi n is_unsigned)
  | _ => (pure ())

def decode_SUNPKLO_Z_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let is_unsigned : Bool := false
  let hi : Bool := false
  match VL with
  | 128 => (execute_SUNPKLO_Z_Z__ 128 d esize hi n is_unsigned)
  | 256 => (execute_SUNPKLO_Z_Z__ 256 d esize hi n is_unsigned)
  | 512 => (execute_SUNPKLO_Z_Z__ 512 d esize hi n is_unsigned)
  | 1024 => (execute_SUNPKLO_Z_Z__ 1024 d esize hi n is_unsigned)
  | 2048 => (execute_SUNPKLO_Z_Z__ 2048 d esize hi n is_unsigned)
  | _ => (pure ())

def decode_SUNPKHI_Z_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let is_unsigned : Bool := false
  let hi : Bool := true
  match VL with
  | 128 => (execute_SUNPKHI_Z_Z__ 128 d esize hi n is_unsigned)
  | 256 => (execute_SUNPKHI_Z_Z__ 256 d esize hi n is_unsigned)
  | 512 => (execute_SUNPKHI_Z_Z__ 512 d esize hi n is_unsigned)
  | 1024 => (execute_SUNPKHI_Z_Z__ 1024 d esize hi n is_unsigned)
  | 2048 => (execute_SUNPKHI_Z_Z__ 2048 d esize hi n is_unsigned)
  | _ => (pure ())

def decode_SETFFR_F__ (_ : Unit) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  match VL with
  | 128 => (execute_SETFFR_F__ 128)
  | 256 => (execute_SETFFR_F__ 256)
  | 512 => (execute_SETFFR_F__ 512)
  | 1024 => (execute_SETFFR_F__ 1024)
  | 2048 => (execute_SETFFR_F__ 2048)
  | _ => (pure ())

def decode_PTRUE_P_S__ (size : (BitVec 2)) (S : (BitVec 1)) (pattern : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let d := (BitVec.toNat Pd)
  let setflags : Bool := false
  let pat : (BitVec 5) := pattern
  match VL with
  | 128 => (execute_PTRUE_P_S__ 128 d esize pat setflags)
  | 256 => (execute_PTRUE_P_S__ 256 d esize pat setflags)
  | 512 => (execute_PTRUE_P_S__ 512 d esize pat setflags)
  | 1024 => (execute_PTRUE_P_S__ 1024 d esize pat setflags)
  | 2048 => (execute_PTRUE_P_S__ 2048 d esize pat setflags)
  | _ => (pure ())

def decode_PTRUES_P_S__ (size : (BitVec 2)) (S : (BitVec 1)) (pattern : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let d := (BitVec.toNat Pd)
  let setflags : Bool := true
  let pat : (BitVec 5) := pattern
  match VL with
  | 128 => (execute_PTRUES_P_S__ 128 d esize pat setflags)
  | 256 => (execute_PTRUES_P_S__ 256 d esize pat setflags)
  | 512 => (execute_PTRUES_P_S__ 512 d esize pat setflags)
  | 1024 => (execute_PTRUES_P_S__ 1024 d esize pat setflags)
  | 2048 => (execute_PTRUES_P_S__ 2048 d esize pat setflags)
  | _ => (pure ())

def decode_PFALSE_P__ (S : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Pd)
  match VL with
  | 128 => (execute_PFALSE_P__ 128 d)
  | 256 => (execute_PFALSE_P__ 256 d)
  | 512 => (execute_PFALSE_P__ 512 d)
  | 1024 => (execute_PFALSE_P__ 1024 d)
  | 2048 => (execute_PFALSE_P__ 2048 d)
  | _ => (pure ())

def decode_RDFFR_P_F__ (S : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Pd)
  match VL with
  | 128 => (execute_RDFFR_P_F__ 128 d)
  | 256 => (execute_RDFFR_P_F__ 256 d)
  | 512 => (execute_RDFFR_P_F__ 512 d)
  | 1024 => (execute_RDFFR_P_F__ 1024 d)
  | 2048 => (execute_RDFFR_P_F__ 2048 d)
  | _ => (pure ())

def decode_WRFFR_F_P__ (Pn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Pn)
  match VL with
  | 128 => (execute_WRFFR_F_P__ 128 n)
  | 256 => (execute_WRFFR_F_P__ 256 n)
  | 512 => (execute_WRFFR_F_P__ 512 n)
  | 1024 => (execute_WRFFR_F_P__ 1024 n)
  | 2048 => (execute_WRFFR_F_P__ 2048 n)
  | _ => (pure ())

def decode_RDFFR_P_P_F__ (S : (BitVec 1)) (Pg : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := false
  match VL with
  | 128 => (execute_RDFFR_P_P_F__ 128 d g setflags)
  | 256 => (execute_RDFFR_P_P_F__ 256 d g setflags)
  | 512 => (execute_RDFFR_P_P_F__ 512 d g setflags)
  | 1024 => (execute_RDFFR_P_P_F__ 1024 d g setflags)
  | 2048 => (execute_RDFFR_P_P_F__ 2048 d g setflags)
  | _ => (pure ())

def decode_RDFFRS_P_P_F__ (S : (BitVec 1)) (Pg : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := true
  match VL with
  | 128 => (execute_RDFFRS_P_P_F__ 128 d g setflags)
  | 256 => (execute_RDFFRS_P_P_F__ 256 d g setflags)
  | 512 => (execute_RDFFRS_P_P_F__ 512 d g setflags)
  | 1024 => (execute_RDFFRS_P_P_F__ 1024 d g setflags)
  | 2048 => (execute_RDFFRS_P_P_F__ 2048 d g setflags)
  | _ => (pure ())

def decode_PTEST__P_P__ (S : (BitVec 1)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  match VL with
  | 128 => (execute_PTEST__P_P__ 128 esize g n)
  | 256 => (execute_PTEST__P_P__ 256 esize g n)
  | 512 => (execute_PTEST__P_P__ 512 esize g n)
  | 1024 => (execute_PTEST__P_P__ 1024 esize g n)
  | 2048 => (execute_PTEST__P_P__ 2048 esize g n)
  | _ => (pure ())

def decode_BRKA_P_P_P__ (B : (BitVec 1)) (S : (BitVec 1)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (M : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let d := (BitVec.toNat Pd)
  let merging : Bool := (M == 1#1)
  let setflags : Bool := false
  match VL with
  | 128 => (execute_BRKA_P_P_P__ 128 d esize g merging n setflags)
  | 256 => (execute_BRKA_P_P_P__ 256 d esize g merging n setflags)
  | 512 => (execute_BRKA_P_P_P__ 512 d esize g merging n setflags)
  | 1024 => (execute_BRKA_P_P_P__ 1024 d esize g merging n setflags)
  | 2048 => (execute_BRKA_P_P_P__ 2048 d esize g merging n setflags)
  | _ => (pure ())

def decode_BRKAS_P_P_P_Z (B : (BitVec 1)) (S : (BitVec 1)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (M : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let d := (BitVec.toNat Pd)
  let merging : Bool := false
  let setflags : Bool := true
  match VL with
  | 128 => (execute_BRKAS_P_P_P_Z 128 d esize g merging n setflags)
  | 256 => (execute_BRKAS_P_P_P_Z 256 d esize g merging n setflags)
  | 512 => (execute_BRKAS_P_P_P_Z 512 d esize g merging n setflags)
  | 1024 => (execute_BRKAS_P_P_P_Z 1024 d esize g merging n setflags)
  | 2048 => (execute_BRKAS_P_P_P_Z 2048 d esize g merging n setflags)
  | _ => (pure ())

def decode_BRKB_P_P_P__ (B : (BitVec 1)) (S : (BitVec 1)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (M : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let d := (BitVec.toNat Pd)
  let merging : Bool := (M == 1#1)
  let setflags : Bool := false
  match VL with
  | 128 => (execute_BRKB_P_P_P__ 128 d esize g merging n setflags)
  | 256 => (execute_BRKB_P_P_P__ 256 d esize g merging n setflags)
  | 512 => (execute_BRKB_P_P_P__ 512 d esize g merging n setflags)
  | 1024 => (execute_BRKB_P_P_P__ 1024 d esize g merging n setflags)
  | 2048 => (execute_BRKB_P_P_P__ 2048 d esize g merging n setflags)
  | _ => (pure ())

def decode_BRKBS_P_P_P_Z (B : (BitVec 1)) (S : (BitVec 1)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (M : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let d := (BitVec.toNat Pd)
  let merging : Bool := false
  let setflags : Bool := true
  match VL with
  | 128 => (execute_BRKBS_P_P_P_Z 128 d esize g merging n setflags)
  | 256 => (execute_BRKBS_P_P_P_Z 256 d esize g merging n setflags)
  | 512 => (execute_BRKBS_P_P_P_Z 512 d esize g merging n setflags)
  | 1024 => (execute_BRKBS_P_P_P_Z 1024 d esize g merging n setflags)
  | 2048 => (execute_BRKBS_P_P_P_Z 2048 d esize g merging n setflags)
  | _ => (pure ())

def decode_AND_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := false
  match VL with
  | 128 => (execute_AND_P_P_PP_Z 128 d esize g m n setflags)
  | 256 => (execute_AND_P_P_PP_Z 256 d esize g m n setflags)
  | 512 => (execute_AND_P_P_PP_Z 512 d esize g m n setflags)
  | 1024 => (execute_AND_P_P_PP_Z 1024 d esize g m n setflags)
  | 2048 => (execute_AND_P_P_PP_Z 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_ANDS_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := true
  match VL with
  | 128 => (execute_ANDS_P_P_PP_Z 128 d esize g m n setflags)
  | 256 => (execute_ANDS_P_P_PP_Z 256 d esize g m n setflags)
  | 512 => (execute_ANDS_P_P_PP_Z 512 d esize g m n setflags)
  | 1024 => (execute_ANDS_P_P_PP_Z 1024 d esize g m n setflags)
  | 2048 => (execute_ANDS_P_P_PP_Z 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_BIC_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := false
  match VL with
  | 128 => (execute_BIC_P_P_PP_Z 128 d esize g m n setflags)
  | 256 => (execute_BIC_P_P_PP_Z 256 d esize g m n setflags)
  | 512 => (execute_BIC_P_P_PP_Z 512 d esize g m n setflags)
  | 1024 => (execute_BIC_P_P_PP_Z 1024 d esize g m n setflags)
  | 2048 => (execute_BIC_P_P_PP_Z 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_BICS_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := true
  match VL with
  | 128 => (execute_BICS_P_P_PP_Z 128 d esize g m n setflags)
  | 256 => (execute_BICS_P_P_PP_Z 256 d esize g m n setflags)
  | 512 => (execute_BICS_P_P_PP_Z 512 d esize g m n setflags)
  | 1024 => (execute_BICS_P_P_PP_Z 1024 d esize g m n setflags)
  | 2048 => (execute_BICS_P_P_PP_Z 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_EOR_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := false
  match VL with
  | 128 => (execute_EOR_P_P_PP_Z 128 d esize g m n setflags)
  | 256 => (execute_EOR_P_P_PP_Z 256 d esize g m n setflags)
  | 512 => (execute_EOR_P_P_PP_Z 512 d esize g m n setflags)
  | 1024 => (execute_EOR_P_P_PP_Z 1024 d esize g m n setflags)
  | 2048 => (execute_EOR_P_P_PP_Z 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_EORS_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := true
  match VL with
  | 128 => (execute_EORS_P_P_PP_Z 128 d esize g m n setflags)
  | 256 => (execute_EORS_P_P_PP_Z 256 d esize g m n setflags)
  | 512 => (execute_EORS_P_P_PP_Z 512 d esize g m n setflags)
  | 1024 => (execute_EORS_P_P_PP_Z 1024 d esize g m n setflags)
  | 2048 => (execute_EORS_P_P_PP_Z 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_NAND_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := false
  match VL with
  | 128 => (execute_NAND_P_P_PP_Z 128 d esize g m n setflags)
  | 256 => (execute_NAND_P_P_PP_Z 256 d esize g m n setflags)
  | 512 => (execute_NAND_P_P_PP_Z 512 d esize g m n setflags)
  | 1024 => (execute_NAND_P_P_PP_Z 1024 d esize g m n setflags)
  | 2048 => (execute_NAND_P_P_PP_Z 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_NANDS_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := true
  match VL with
  | 128 => (execute_NANDS_P_P_PP_Z 128 d esize g m n setflags)
  | 256 => (execute_NANDS_P_P_PP_Z 256 d esize g m n setflags)
  | 512 => (execute_NANDS_P_P_PP_Z 512 d esize g m n setflags)
  | 1024 => (execute_NANDS_P_P_PP_Z 1024 d esize g m n setflags)
  | 2048 => (execute_NANDS_P_P_PP_Z 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_NOR_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := false
  match VL with
  | 128 => (execute_NOR_P_P_PP_Z 128 d esize g m n setflags)
  | 256 => (execute_NOR_P_P_PP_Z 256 d esize g m n setflags)
  | 512 => (execute_NOR_P_P_PP_Z 512 d esize g m n setflags)
  | 1024 => (execute_NOR_P_P_PP_Z 1024 d esize g m n setflags)
  | 2048 => (execute_NOR_P_P_PP_Z 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_NORS_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := true
  match VL with
  | 128 => (execute_NORS_P_P_PP_Z 128 d esize g m n setflags)
  | 256 => (execute_NORS_P_P_PP_Z 256 d esize g m n setflags)
  | 512 => (execute_NORS_P_P_PP_Z 512 d esize g m n setflags)
  | 1024 => (execute_NORS_P_P_PP_Z 1024 d esize g m n setflags)
  | 2048 => (execute_NORS_P_P_PP_Z 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_ORN_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := false
  match VL with
  | 128 => (execute_ORN_P_P_PP_Z 128 d esize g m n setflags)
  | 256 => (execute_ORN_P_P_PP_Z 256 d esize g m n setflags)
  | 512 => (execute_ORN_P_P_PP_Z 512 d esize g m n setflags)
  | 1024 => (execute_ORN_P_P_PP_Z 1024 d esize g m n setflags)
  | 2048 => (execute_ORN_P_P_PP_Z 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_ORNS_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := true
  match VL with
  | 128 => (execute_ORNS_P_P_PP_Z 128 d esize g m n setflags)
  | 256 => (execute_ORNS_P_P_PP_Z 256 d esize g m n setflags)
  | 512 => (execute_ORNS_P_P_PP_Z 512 d esize g m n setflags)
  | 1024 => (execute_ORNS_P_P_PP_Z 1024 d esize g m n setflags)
  | 2048 => (execute_ORNS_P_P_PP_Z 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_ORR_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := false
  match VL with
  | 128 => (execute_ORR_P_P_PP_Z 128 d esize g m n setflags)
  | 256 => (execute_ORR_P_P_PP_Z 256 d esize g m n setflags)
  | 512 => (execute_ORR_P_P_PP_Z 512 d esize g m n setflags)
  | 1024 => (execute_ORR_P_P_PP_Z 1024 d esize g m n setflags)
  | 2048 => (execute_ORR_P_P_PP_Z 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_ORRS_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := true
  match VL with
  | 128 => (execute_ORRS_P_P_PP_Z 128 d esize g m n setflags)
  | 256 => (execute_ORRS_P_P_PP_Z 256 d esize g m n setflags)
  | 512 => (execute_ORRS_P_P_PP_Z 512 d esize g m n setflags)
  | 1024 => (execute_ORRS_P_P_PP_Z 1024 d esize g m n setflags)
  | 2048 => (execute_ORRS_P_P_PP_Z 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_SEL_P_P_PP__ (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  match VL with
  | 128 => (execute_SEL_P_P_PP__ 128 d esize g m n)
  | 256 => (execute_SEL_P_P_PP__ 256 d esize g m n)
  | 512 => (execute_SEL_P_P_PP__ 512 d esize g m n)
  | 1024 => (execute_SEL_P_P_PP__ 1024 d esize g m n)
  | 2048 => (execute_SEL_P_P_PP__ 2048 d esize g m n)
  | _ => (pure ())

def decode_PFIRST_P_P_P__ (S : (BitVec 1)) (Pg : (BitVec 4)) (Pdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Pdn)
  match VL with
  | 128 => (execute_PFIRST_P_P_P__ 128 dn esize g)
  | 256 => (execute_PFIRST_P_P_P__ 256 dn esize g)
  | 512 => (execute_PFIRST_P_P_P__ 512 dn esize g)
  | 1024 => (execute_PFIRST_P_P_P__ 1024 dn esize g)
  | 2048 => (execute_PFIRST_P_P_P__ 2048 dn esize g)
  | _ => (pure ())

def decode_PNEXT_P_P_P__ (size : (BitVec 2)) (Pv : (BitVec 4)) (Pdn : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let v := (BitVec.toNat Pv)
  let dn := (BitVec.toNat Pdn)
  match VL with
  | 128 => (execute_PNEXT_P_P_P__ 128 dn esize v)
  | 256 => (execute_PNEXT_P_P_P__ 256 dn esize v)
  | 512 => (execute_PNEXT_P_P_P__ 512 dn esize v)
  | 1024 => (execute_PNEXT_P_P_P__ 1024 dn esize v)
  | 2048 => (execute_PNEXT_P_P_P__ 2048 dn esize v)
  | _ => (pure ())

def decode_RDVL_R_I__ (imm6 : (BitVec 6)) (Rd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let imm := (BitVec.toInt imm6)
  match VL with
  | 128 => (execute_RDVL_R_I__ 128 d imm)
  | 256 => (execute_RDVL_R_I__ 256 d imm)
  | 512 => (execute_RDVL_R_I__ 512 d imm)
  | 1024 => (execute_RDVL_R_I__ 1024 d imm)
  | 2048 => (execute_RDVL_R_I__ 2048 d imm)
  | _ => (pure ())

def decode_SEL_Z_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pv : (BitVec 4)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let v := (BitVec.toNat Pv)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SEL_Z_P_ZZ__ 128 d esize m n v)
  | 256 => (execute_SEL_Z_P_ZZ__ 256 d esize m n v)
  | 512 => (execute_SEL_Z_P_ZZ__ 512 d esize m n v)
  | 1024 => (execute_SEL_Z_P_ZZ__ 1024 d esize m n v)
  | 2048 => (execute_SEL_Z_P_ZZ__ 2048 d esize m n v)
  | _ => (pure ())

def decode_LSL_Z_ZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0x0#4 : (BitVec 4))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0x1#4 : (BitVec 4))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 3 1) == (0b001#3 : (BitVec 3))) : Bool)
        then (pure 16)
        else
          (if (((Sail.BitVec.extractLsb b__0 3 2) == (0b01#2 : (BitVec 2))) : Bool)
          then (pure 32)
          else (pure 64)))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((BitVec.toNat (tsize +++ imm3)) -i esize)
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_LSL_Z_ZI__ 128 d 8 n shift)
      | 256 => (execute_LSL_Z_ZI__ 256 d 8 n shift)
      | 512 => (execute_LSL_Z_ZI__ 512 d 8 n shift)
      | 1024 => (execute_LSL_Z_ZI__ 1024 d 8 n shift)
      | 2048 => (execute_LSL_Z_ZI__ 2048 d 8 n shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_LSL_Z_ZI__ 128 d 16 n shift)
      | 256 => (execute_LSL_Z_ZI__ 256 d 16 n shift)
      | 512 => (execute_LSL_Z_ZI__ 512 d 16 n shift)
      | 1024 => (execute_LSL_Z_ZI__ 1024 d 16 n shift)
      | 2048 => (execute_LSL_Z_ZI__ 2048 d 16 n shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_LSL_Z_ZI__ 128 d 32 n shift)
      | 256 => (execute_LSL_Z_ZI__ 256 d 32 n shift)
      | 512 => (execute_LSL_Z_ZI__ 512 d 32 n shift)
      | 1024 => (execute_LSL_Z_ZI__ 1024 d 32 n shift)
      | 2048 => (execute_LSL_Z_ZI__ 2048 d 32 n shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_LSL_Z_ZI__ 128 d 64 n shift)
      | 256 => (execute_LSL_Z_ZI__ 256 d 64 n shift)
      | 512 => (execute_LSL_Z_ZI__ 512 d 64 n shift)
      | 1024 => (execute_LSL_Z_ZI__ 1024 d 64 n shift)
      | 2048 => (execute_LSL_Z_ZI__ 2048 d 64 n shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:31348.22-31348.23"

def decode_LSR_Z_ZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0x0#4 : (BitVec 4))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0x1#4 : (BitVec 4))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 3 1) == (0b001#3 : (BitVec 3))) : Bool)
        then (pure 16)
        else
          (if (((Sail.BitVec.extractLsb b__0 3 2) == (0b01#2 : (BitVec 2))) : Bool)
          then (pure 32)
          else (pure 64)))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_LSR_Z_ZI__ 128 d 8 n shift)
      | 256 => (execute_LSR_Z_ZI__ 256 d 8 n shift)
      | 512 => (execute_LSR_Z_ZI__ 512 d 8 n shift)
      | 1024 => (execute_LSR_Z_ZI__ 1024 d 8 n shift)
      | 2048 => (execute_LSR_Z_ZI__ 2048 d 8 n shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_LSR_Z_ZI__ 128 d 16 n shift)
      | 256 => (execute_LSR_Z_ZI__ 256 d 16 n shift)
      | 512 => (execute_LSR_Z_ZI__ 512 d 16 n shift)
      | 1024 => (execute_LSR_Z_ZI__ 1024 d 16 n shift)
      | 2048 => (execute_LSR_Z_ZI__ 2048 d 16 n shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_LSR_Z_ZI__ 128 d 32 n shift)
      | 256 => (execute_LSR_Z_ZI__ 256 d 32 n shift)
      | 512 => (execute_LSR_Z_ZI__ 512 d 32 n shift)
      | 1024 => (execute_LSR_Z_ZI__ 1024 d 32 n shift)
      | 2048 => (execute_LSR_Z_ZI__ 2048 d 32 n shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_LSR_Z_ZI__ 128 d 64 n shift)
      | 256 => (execute_LSR_Z_ZI__ 256 d 64 n shift)
      | 512 => (execute_LSR_Z_ZI__ 512 d 64 n shift)
      | 1024 => (execute_LSR_Z_ZI__ 1024 d 64 n shift)
      | 2048 => (execute_LSR_Z_ZI__ 2048 d 64 n shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:31492.22-31492.23"

def decode_ASR_Z_ZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0x0#4 : (BitVec 4))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0x1#4 : (BitVec 4))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 3 1) == (0b001#3 : (BitVec 3))) : Bool)
        then (pure 16)
        else
          (if (((Sail.BitVec.extractLsb b__0 3 2) == (0b01#2 : (BitVec 2))) : Bool)
          then (pure 32)
          else (pure 64)))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_ASR_Z_ZI__ 128 d 8 n shift)
      | 256 => (execute_ASR_Z_ZI__ 256 d 8 n shift)
      | 512 => (execute_ASR_Z_ZI__ 512 d 8 n shift)
      | 1024 => (execute_ASR_Z_ZI__ 1024 d 8 n shift)
      | 2048 => (execute_ASR_Z_ZI__ 2048 d 8 n shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_ASR_Z_ZI__ 128 d 16 n shift)
      | 256 => (execute_ASR_Z_ZI__ 256 d 16 n shift)
      | 512 => (execute_ASR_Z_ZI__ 512 d 16 n shift)
      | 1024 => (execute_ASR_Z_ZI__ 1024 d 16 n shift)
      | 2048 => (execute_ASR_Z_ZI__ 2048 d 16 n shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_ASR_Z_ZI__ 128 d 32 n shift)
      | 256 => (execute_ASR_Z_ZI__ 256 d 32 n shift)
      | 512 => (execute_ASR_Z_ZI__ 512 d 32 n shift)
      | 1024 => (execute_ASR_Z_ZI__ 1024 d 32 n shift)
      | 2048 => (execute_ASR_Z_ZI__ 2048 d 32 n shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_ASR_Z_ZI__ 128 d 64 n shift)
      | 256 => (execute_ASR_Z_ZI__ 256 d 64 n shift)
      | 512 => (execute_ASR_Z_ZI__ 512 d 64 n shift)
      | 1024 => (execute_ASR_Z_ZI__ 1024 d 64 n shift)
      | 2048 => (execute_ASR_Z_ZI__ 2048 d 64 n shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:31637.22-31637.23"

def decode_ASRD_Z_P_ZI__ (tszh : (BitVec 2)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0x0#4 : (BitVec 4))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0x1#4 : (BitVec 4))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 3 1) == (0b001#3 : (BitVec 3))) : Bool)
        then (pure 16)
        else
          (if (((Sail.BitVec.extractLsb b__0 3 2) == (0b01#2 : (BitVec 2))) : Bool)
          then (pure 32)
          else (pure 64)))) ) : SailM Int )
  let esize := esize
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_ASRD_Z_P_ZI__ 128 dn 8 g shift)
      | 256 => (execute_ASRD_Z_P_ZI__ 256 dn 8 g shift)
      | 512 => (execute_ASRD_Z_P_ZI__ 512 dn 8 g shift)
      | 1024 => (execute_ASRD_Z_P_ZI__ 1024 dn 8 g shift)
      | 2048 => (execute_ASRD_Z_P_ZI__ 2048 dn 8 g shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_ASRD_Z_P_ZI__ 128 dn 16 g shift)
      | 256 => (execute_ASRD_Z_P_ZI__ 256 dn 16 g shift)
      | 512 => (execute_ASRD_Z_P_ZI__ 512 dn 16 g shift)
      | 1024 => (execute_ASRD_Z_P_ZI__ 1024 dn 16 g shift)
      | 2048 => (execute_ASRD_Z_P_ZI__ 2048 dn 16 g shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_ASRD_Z_P_ZI__ 128 dn 32 g shift)
      | 256 => (execute_ASRD_Z_P_ZI__ 256 dn 32 g shift)
      | 512 => (execute_ASRD_Z_P_ZI__ 512 dn 32 g shift)
      | 1024 => (execute_ASRD_Z_P_ZI__ 1024 dn 32 g shift)
      | 2048 => (execute_ASRD_Z_P_ZI__ 2048 dn 32 g shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_ASRD_Z_P_ZI__ 128 dn 64 g shift)
      | 256 => (execute_ASRD_Z_P_ZI__ 256 dn 64 g shift)
      | 512 => (execute_ASRD_Z_P_ZI__ 512 dn 64 g shift)
      | 1024 => (execute_ASRD_Z_P_ZI__ 1024 dn 64 g shift)
      | 2048 => (execute_ASRD_Z_P_ZI__ 2048 dn 64 g shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:31792.22-31792.23"

def decode_LSL_Z_P_ZI__ (tszh : (BitVec 2)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0x0#4 : (BitVec 4))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0x1#4 : (BitVec 4))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 3 1) == (0b001#3 : (BitVec 3))) : Bool)
        then (pure 16)
        else
          (if (((Sail.BitVec.extractLsb b__0 3 2) == (0b01#2 : (BitVec 2))) : Bool)
          then (pure 32)
          else (pure 64)))) ) : SailM Int )
  let esize := esize
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let shift := ((BitVec.toNat (tsize +++ imm3)) -i esize)
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_LSL_Z_P_ZI__ 128 dn 8 g shift)
      | 256 => (execute_LSL_Z_P_ZI__ 256 dn 8 g shift)
      | 512 => (execute_LSL_Z_P_ZI__ 512 dn 8 g shift)
      | 1024 => (execute_LSL_Z_P_ZI__ 1024 dn 8 g shift)
      | 2048 => (execute_LSL_Z_P_ZI__ 2048 dn 8 g shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_LSL_Z_P_ZI__ 128 dn 16 g shift)
      | 256 => (execute_LSL_Z_P_ZI__ 256 dn 16 g shift)
      | 512 => (execute_LSL_Z_P_ZI__ 512 dn 16 g shift)
      | 1024 => (execute_LSL_Z_P_ZI__ 1024 dn 16 g shift)
      | 2048 => (execute_LSL_Z_P_ZI__ 2048 dn 16 g shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_LSL_Z_P_ZI__ 128 dn 32 g shift)
      | 256 => (execute_LSL_Z_P_ZI__ 256 dn 32 g shift)
      | 512 => (execute_LSL_Z_P_ZI__ 512 dn 32 g shift)
      | 1024 => (execute_LSL_Z_P_ZI__ 1024 dn 32 g shift)
      | 2048 => (execute_LSL_Z_P_ZI__ 2048 dn 32 g shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_LSL_Z_P_ZI__ 128 dn 64 g shift)
      | 256 => (execute_LSL_Z_P_ZI__ 256 dn 64 g shift)
      | 512 => (execute_LSL_Z_P_ZI__ 512 dn 64 g shift)
      | 1024 => (execute_LSL_Z_P_ZI__ 1024 dn 64 g shift)
      | 2048 => (execute_LSL_Z_P_ZI__ 2048 dn 64 g shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:31944.22-31944.23"

def decode_LSR_Z_P_ZI__ (tszh : (BitVec 2)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0x0#4 : (BitVec 4))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0x1#4 : (BitVec 4))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 3 1) == (0b001#3 : (BitVec 3))) : Bool)
        then (pure 16)
        else
          (if (((Sail.BitVec.extractLsb b__0 3 2) == (0b01#2 : (BitVec 2))) : Bool)
          then (pure 32)
          else (pure 64)))) ) : SailM Int )
  let esize := esize
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_LSR_Z_P_ZI__ 128 dn 8 g shift)
      | 256 => (execute_LSR_Z_P_ZI__ 256 dn 8 g shift)
      | 512 => (execute_LSR_Z_P_ZI__ 512 dn 8 g shift)
      | 1024 => (execute_LSR_Z_P_ZI__ 1024 dn 8 g shift)
      | 2048 => (execute_LSR_Z_P_ZI__ 2048 dn 8 g shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_LSR_Z_P_ZI__ 128 dn 16 g shift)
      | 256 => (execute_LSR_Z_P_ZI__ 256 dn 16 g shift)
      | 512 => (execute_LSR_Z_P_ZI__ 512 dn 16 g shift)
      | 1024 => (execute_LSR_Z_P_ZI__ 1024 dn 16 g shift)
      | 2048 => (execute_LSR_Z_P_ZI__ 2048 dn 16 g shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_LSR_Z_P_ZI__ 128 dn 32 g shift)
      | 256 => (execute_LSR_Z_P_ZI__ 256 dn 32 g shift)
      | 512 => (execute_LSR_Z_P_ZI__ 512 dn 32 g shift)
      | 1024 => (execute_LSR_Z_P_ZI__ 1024 dn 32 g shift)
      | 2048 => (execute_LSR_Z_P_ZI__ 2048 dn 32 g shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_LSR_Z_P_ZI__ 128 dn 64 g shift)
      | 256 => (execute_LSR_Z_P_ZI__ 256 dn 64 g shift)
      | 512 => (execute_LSR_Z_P_ZI__ 512 dn 64 g shift)
      | 1024 => (execute_LSR_Z_P_ZI__ 1024 dn 64 g shift)
      | 2048 => (execute_LSR_Z_P_ZI__ 2048 dn 64 g shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:32096.22-32096.23"

def decode_ASR_Z_P_ZI__ (tszh : (BitVec 2)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0x0#4 : (BitVec 4))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0x1#4 : (BitVec 4))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 3 1) == (0b001#3 : (BitVec 3))) : Bool)
        then (pure 16)
        else
          (if (((Sail.BitVec.extractLsb b__0 3 2) == (0b01#2 : (BitVec 2))) : Bool)
          then (pure 32)
          else (pure 64)))) ) : SailM Int )
  let esize := esize
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_ASR_Z_P_ZI__ 128 dn 8 g shift)
      | 256 => (execute_ASR_Z_P_ZI__ 256 dn 8 g shift)
      | 512 => (execute_ASR_Z_P_ZI__ 512 dn 8 g shift)
      | 1024 => (execute_ASR_Z_P_ZI__ 1024 dn 8 g shift)
      | 2048 => (execute_ASR_Z_P_ZI__ 2048 dn 8 g shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_ASR_Z_P_ZI__ 128 dn 16 g shift)
      | 256 => (execute_ASR_Z_P_ZI__ 256 dn 16 g shift)
      | 512 => (execute_ASR_Z_P_ZI__ 512 dn 16 g shift)
      | 1024 => (execute_ASR_Z_P_ZI__ 1024 dn 16 g shift)
      | 2048 => (execute_ASR_Z_P_ZI__ 2048 dn 16 g shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_ASR_Z_P_ZI__ 128 dn 32 g shift)
      | 256 => (execute_ASR_Z_P_ZI__ 256 dn 32 g shift)
      | 512 => (execute_ASR_Z_P_ZI__ 512 dn 32 g shift)
      | 1024 => (execute_ASR_Z_P_ZI__ 1024 dn 32 g shift)
      | 2048 => (execute_ASR_Z_P_ZI__ 2048 dn 32 g shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_ASR_Z_P_ZI__ 128 dn 64 g shift)
      | 256 => (execute_ASR_Z_P_ZI__ 256 dn 64 g shift)
      | 512 => (execute_ASR_Z_P_ZI__ 512 dn 64 g shift)
      | 1024 => (execute_ASR_Z_P_ZI__ 1024 dn 64 g shift)
      | 2048 => (execute_ASR_Z_P_ZI__ 2048 dn 64 g shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:32248.22-32248.23"

def decode_LSL_Z_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_LSL_Z_ZW__ 128 d esize m n)
  | 256 => (execute_LSL_Z_ZW__ 256 d esize m n)
  | 512 => (execute_LSL_Z_ZW__ 512 d esize m n)
  | 1024 => (execute_LSL_Z_ZW__ 1024 d esize m n)
  | 2048 => (execute_LSL_Z_ZW__ 2048 d esize m n)
  | _ => (pure ())

def decode_LSR_Z_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_LSR_Z_ZW__ 128 d esize m n)
  | 256 => (execute_LSR_Z_ZW__ 256 d esize m n)
  | 512 => (execute_LSR_Z_ZW__ 512 d esize m n)
  | 1024 => (execute_LSR_Z_ZW__ 1024 d esize m n)
  | 2048 => (execute_LSR_Z_ZW__ 2048 d esize m n)
  | _ => (pure ())

def decode_ASR_Z_ZW__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_ASR_Z_ZW__ 128 d esize m n)
  | 256 => (execute_ASR_Z_ZW__ 256 d esize m n)
  | 512 => (execute_ASR_Z_ZW__ 512 d esize m n)
  | 1024 => (execute_ASR_Z_ZW__ 1024 d esize m n)
  | 2048 => (execute_ASR_Z_ZW__ 2048 d esize m n)
  | _ => (pure ())

def decode_LSL_Z_P_ZW__ (size : (BitVec 2)) (R : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_LSL_Z_P_ZW__ 128 dn esize g m)
  | 256 => (execute_LSL_Z_P_ZW__ 256 dn esize g m)
  | 512 => (execute_LSL_Z_P_ZW__ 512 dn esize g m)
  | 1024 => (execute_LSL_Z_P_ZW__ 1024 dn esize g m)
  | 2048 => (execute_LSL_Z_P_ZW__ 2048 dn esize g m)
  | _ => (pure ())

def decode_LSR_Z_P_ZW__ (size : (BitVec 2)) (R : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_LSR_Z_P_ZW__ 128 dn esize g m)
  | 256 => (execute_LSR_Z_P_ZW__ 256 dn esize g m)
  | 512 => (execute_LSR_Z_P_ZW__ 512 dn esize g m)
  | 1024 => (execute_LSR_Z_P_ZW__ 1024 dn esize g m)
  | 2048 => (execute_LSR_Z_P_ZW__ 2048 dn esize g m)
  | _ => (pure ())

def decode_ASR_Z_P_ZW__ (size : (BitVec 2)) (R : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_ASR_Z_P_ZW__ 128 dn esize g m)
  | 256 => (execute_ASR_Z_P_ZW__ 256 dn esize g m)
  | 512 => (execute_ASR_Z_P_ZW__ 512 dn esize g m)
  | 1024 => (execute_ASR_Z_P_ZW__ 1024 dn esize g m)
  | 2048 => (execute_ASR_Z_P_ZW__ 2048 dn esize g m)
  | _ => (pure ())

def decode_ABS_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_ABS_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_ABS_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_ABS_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_ABS_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_ABS_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_CLS_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_CLS_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_CLS_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_CLS_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_CLS_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_CLS_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_CLZ_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_CLZ_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_CLZ_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_CLZ_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_CLZ_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_CLZ_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_CNOT_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_CNOT_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_CNOT_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_CNOT_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_CNOT_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_CNOT_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_CNT_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_CNT_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_CNT_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_CNT_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_CNT_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_CNT_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_FABS_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FABS_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_FABS_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_FABS_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_FABS_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_FABS_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_FNEG_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_FNEG_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_FNEG_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_FNEG_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_FNEG_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_FNEG_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_NEG_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_NEG_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_NEG_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_NEG_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_NEG_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_NEG_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_NOT_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_NOT_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_NOT_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_NOT_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_NOT_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_NOT_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_RBIT_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_RBIT_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_RBIT_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_RBIT_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_RBIT_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_RBIT_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_UQADD_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UQADD_Z_ZZ__ 128 d esize m n is_unsigned)
  | 256 => (execute_UQADD_Z_ZZ__ 256 d esize m n is_unsigned)
  | 512 => (execute_UQADD_Z_ZZ__ 512 d esize m n is_unsigned)
  | 1024 => (execute_UQADD_Z_ZZ__ 1024 d esize m n is_unsigned)
  | 2048 => (execute_UQADD_Z_ZZ__ 2048 d esize m n is_unsigned)
  | _ => (pure ())

def decode_SQADD_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SQADD_Z_ZZ__ 128 d esize m n is_unsigned)
  | 256 => (execute_SQADD_Z_ZZ__ 256 d esize m n is_unsigned)
  | 512 => (execute_SQADD_Z_ZZ__ 512 d esize m n is_unsigned)
  | 1024 => (execute_SQADD_Z_ZZ__ 1024 d esize m n is_unsigned)
  | 2048 => (execute_SQADD_Z_ZZ__ 2048 d esize m n is_unsigned)
  | _ => (pure ())

def decode_UQSUB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UQSUB_Z_ZZ__ 128 d esize m n is_unsigned)
  | 256 => (execute_UQSUB_Z_ZZ__ 256 d esize m n is_unsigned)
  | 512 => (execute_UQSUB_Z_ZZ__ 512 d esize m n is_unsigned)
  | 1024 => (execute_UQSUB_Z_ZZ__ 1024 d esize m n is_unsigned)
  | 2048 => (execute_UQSUB_Z_ZZ__ 2048 d esize m n is_unsigned)
  | _ => (pure ())

def decode_SQSUB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SQSUB_Z_ZZ__ 128 d esize m n is_unsigned)
  | 256 => (execute_SQSUB_Z_ZZ__ 256 d esize m n is_unsigned)
  | 512 => (execute_SQSUB_Z_ZZ__ 512 d esize m n is_unsigned)
  | 1024 => (execute_SQSUB_Z_ZZ__ 1024 d esize m n is_unsigned)
  | 2048 => (execute_SQSUB_Z_ZZ__ 2048 d esize m n is_unsigned)
  | _ => (pure ())

def decode_UQADD_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size +++ sh) == 0b001#3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat Zdn)
  let imm : Int := (BitVec.toNat imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm := imm
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UQADD_Z_ZI__ 128 dn esize imm is_unsigned)
  | 256 => (execute_UQADD_Z_ZI__ 256 dn esize imm is_unsigned)
  | 512 => (execute_UQADD_Z_ZI__ 512 dn esize imm is_unsigned)
  | 1024 => (execute_UQADD_Z_ZI__ 1024 dn esize imm is_unsigned)
  | 2048 => (execute_UQADD_Z_ZI__ 2048 dn esize imm is_unsigned)
  | _ => (pure ())

def decode_SQADD_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size +++ sh) == 0b001#3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat Zdn)
  let imm : Int := (BitVec.toNat imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm := imm
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SQADD_Z_ZI__ 128 dn esize imm is_unsigned)
  | 256 => (execute_SQADD_Z_ZI__ 256 dn esize imm is_unsigned)
  | 512 => (execute_SQADD_Z_ZI__ 512 dn esize imm is_unsigned)
  | 1024 => (execute_SQADD_Z_ZI__ 1024 dn esize imm is_unsigned)
  | 2048 => (execute_SQADD_Z_ZI__ 2048 dn esize imm is_unsigned)
  | _ => (pure ())

def decode_UQSUB_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size +++ sh) == 0b001#3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat Zdn)
  let imm : Int := (BitVec.toNat imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm := imm
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UQSUB_Z_ZI__ 128 dn esize imm is_unsigned)
  | 256 => (execute_UQSUB_Z_ZI__ 256 dn esize imm is_unsigned)
  | 512 => (execute_UQSUB_Z_ZI__ 512 dn esize imm is_unsigned)
  | 1024 => (execute_UQSUB_Z_ZI__ 1024 dn esize imm is_unsigned)
  | 2048 => (execute_UQSUB_Z_ZI__ 2048 dn esize imm is_unsigned)
  | _ => (pure ())

def decode_SQSUB_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size +++ sh) == 0b001#3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat Zdn)
  let imm : Int := (BitVec.toNat imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm := imm
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SQSUB_Z_ZI__ 128 dn esize imm is_unsigned)
  | 256 => (execute_SQSUB_Z_ZI__ 256 dn esize imm is_unsigned)
  | 512 => (execute_SQSUB_Z_ZI__ 512 dn esize imm is_unsigned)
  | 1024 => (execute_SQSUB_Z_ZI__ 1024 dn esize imm is_unsigned)
  | 2048 => (execute_SQSUB_Z_ZI__ 2048 dn esize imm is_unsigned)
  | _ => (pure ())

def decode_BRKPA_P_P_PP__ (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (B : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := false
  match VL with
  | 128 => (execute_BRKPA_P_P_PP__ 128 d esize g m n setflags)
  | 256 => (execute_BRKPA_P_P_PP__ 256 d esize g m n setflags)
  | 512 => (execute_BRKPA_P_P_PP__ 512 d esize g m n setflags)
  | 1024 => (execute_BRKPA_P_P_PP__ 1024 d esize g m n setflags)
  | 2048 => (execute_BRKPA_P_P_PP__ 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_BRKPAS_P_P_PP__ (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (B : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := true
  match VL with
  | 128 => (execute_BRKPAS_P_P_PP__ 128 d esize g m n setflags)
  | 256 => (execute_BRKPAS_P_P_PP__ 256 d esize g m n setflags)
  | 512 => (execute_BRKPAS_P_P_PP__ 512 d esize g m n setflags)
  | 1024 => (execute_BRKPAS_P_P_PP__ 1024 d esize g m n setflags)
  | 2048 => (execute_BRKPAS_P_P_PP__ 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_BRKPB_P_P_PP__ (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (B : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := false
  match VL with
  | 128 => (execute_BRKPB_P_P_PP__ 128 d esize g m n setflags)
  | 256 => (execute_BRKPB_P_P_PP__ 256 d esize g m n setflags)
  | 512 => (execute_BRKPB_P_P_PP__ 512 d esize g m n setflags)
  | 1024 => (execute_BRKPB_P_P_PP__ 1024 d esize g m n setflags)
  | 2048 => (execute_BRKPB_P_P_PP__ 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_BRKPBS_P_P_PP__ (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (B : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let setflags : Bool := true
  match VL with
  | 128 => (execute_BRKPBS_P_P_PP__ 128 d esize g m n setflags)
  | 256 => (execute_BRKPBS_P_P_PP__ 256 d esize g m n setflags)
  | 512 => (execute_BRKPBS_P_P_PP__ 512 d esize g m n setflags)
  | 1024 => (execute_BRKPBS_P_P_PP__ 1024 d esize g m n setflags)
  | 2048 => (execute_BRKPBS_P_P_PP__ 2048 d esize g m n setflags)
  | _ => (pure ())

def decode_BRKN_P_P_PP__ (S : (BitVec 1)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pdm : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let dm := (BitVec.toNat Pdm)
  let setflags : Bool := false
  match VL with
  | 128 => (execute_BRKN_P_P_PP__ 128 dm g n setflags)
  | 256 => (execute_BRKN_P_P_PP__ 256 dm g n setflags)
  | 512 => (execute_BRKN_P_P_PP__ 512 dm g n setflags)
  | 1024 => (execute_BRKN_P_P_PP__ 1024 dm g n setflags)
  | 2048 => (execute_BRKN_P_P_PP__ 2048 dm g n setflags)
  | _ => (pure ())

def decode_BRKNS_P_P_PP__ (S : (BitVec 1)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pdm : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Pn)
  let dm := (BitVec.toNat Pdm)
  let setflags : Bool := true
  match VL with
  | 128 => (execute_BRKNS_P_P_PP__ 128 dm g n setflags)
  | 256 => (execute_BRKNS_P_P_PP__ 256 dm g n setflags)
  | 512 => (execute_BRKNS_P_P_PP__ 512 dm g n setflags)
  | 1024 => (execute_BRKNS_P_P_PP__ 1024 dm g n setflags)
  | 2048 => (execute_BRKNS_P_P_PP__ 2048 dm g n setflags)
  | _ => (pure ())

def decode_INSR_Z_V__ (size : (BitVec 2)) (Vm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Vm)
  match VL with
  | 128 => (execute_INSR_Z_V__ 128 dn esize m)
  | 256 => (execute_INSR_Z_V__ 256 dn esize m)
  | 512 => (execute_INSR_Z_V__ 512 dn esize m)
  | 1024 => (execute_INSR_Z_V__ 1024 dn esize m)
  | 2048 => (execute_INSR_Z_V__ 2048 dn esize m)
  | _ => (pure ())

def decode_INSR_Z_R__ (size : (BitVec 2)) (Rm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Rm)
  match VL with
  | 128 => (execute_INSR_Z_R__ 128 dn esize m)
  | 256 => (execute_INSR_Z_R__ 256 dn esize m)
  | 512 => (execute_INSR_Z_R__ 512 dn esize m)
  | 1024 => (execute_INSR_Z_R__ 1024 dn esize m)
  | 2048 => (execute_INSR_Z_R__ 2048 dn esize m)
  | _ => (pure ())

def decode_SDOT_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((let b__0 := size
     if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
     then true
     else false : Bool) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SDOT_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_SDOT_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_SDOT_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_SDOT_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_SDOT_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_SDOT_Z_ZZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SDOT_Z_ZZZi_S 128 da esize index m n)
  | 256 => (execute_SDOT_Z_ZZZi_S 256 da esize index m n)
  | 512 => (execute_SDOT_Z_ZZZi_S 512 da esize index m n)
  | 1024 => (execute_SDOT_Z_ZZZi_S 1024 da esize index m n)
  | 2048 => (execute_SDOT_Z_ZZZi_S 2048 da esize index m n)
  | _ => (pure ())

def decode_SDOT_Z_ZZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let index := (BitVec.toNat i1)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SDOT_Z_ZZZi_D 128 da esize index m n)
  | 256 => (execute_SDOT_Z_ZZZi_D 256 da esize index m n)
  | 512 => (execute_SDOT_Z_ZZZi_D 512 da esize index m n)
  | 1024 => (execute_SDOT_Z_ZZZi_D 1024 da esize index m n)
  | 2048 => (execute_SDOT_Z_ZZZi_D 2048 da esize index m n)
  | _ => (pure ())

def decode_UDOT_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((let b__0 := size
     if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
     then true
     else false : Bool) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_UDOT_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_UDOT_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_UDOT_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_UDOT_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_UDOT_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_UDOT_Z_ZZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_UDOT_Z_ZZZi_S 128 da esize index m n)
  | 256 => (execute_UDOT_Z_ZZZi_S 256 da esize index m n)
  | 512 => (execute_UDOT_Z_ZZZi_S 512 da esize index m n)
  | 1024 => (execute_UDOT_Z_ZZZi_S 1024 da esize index m n)
  | 2048 => (execute_UDOT_Z_ZZZi_S 2048 da esize index m n)
  | _ => (pure ())

def decode_UDOT_Z_ZZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let index := (BitVec.toNat i1)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_UDOT_Z_ZZZi_D 128 da esize index m n)
  | 256 => (execute_UDOT_Z_ZZZi_D 256 da esize index m n)
  | 512 => (execute_UDOT_Z_ZZZi_D 512 da esize index m n)
  | 1024 => (execute_UDOT_Z_ZZZi_D 1024 da esize index m n)
  | 2048 => (execute_UDOT_Z_ZZZi_D 2048 da esize index m n)
  | _ => (pure ())

def decode_USDOT_Z_ZZZ_S (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))) <||> (do
       (pure (! (← (HaveInt8MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_USDOT_Z_ZZZ_S 128 da esize m n)
  | 256 => (execute_USDOT_Z_ZZZ_S 256 da esize m n)
  | 512 => (execute_USDOT_Z_ZZZ_S 512 da esize m n)
  | 1024 => (execute_USDOT_Z_ZZZ_S 1024 da esize m n)
  | 2048 => (execute_USDOT_Z_ZZZ_S 2048 da esize m n)
  | _ => (pure ())

def decode_USDOT_Z_ZZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))) <||> (do
       (pure (! (← (HaveInt8MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_USDOT_Z_ZZZi_S 128 da esize index m n)
  | 256 => (execute_USDOT_Z_ZZZi_S 256 da esize index m n)
  | 512 => (execute_USDOT_Z_ZZZi_S 512 da esize index m n)
  | 1024 => (execute_USDOT_Z_ZZZi_S 1024 da esize index m n)
  | 2048 => (execute_USDOT_Z_ZZZi_S 2048 da esize index m n)
  | _ => (pure ())

def decode_SUDOT_Z_ZZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))) <||> (do
       (pure (! (← (HaveInt8MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SUDOT_Z_ZZZi_S 128 da esize index m n)
  | 256 => (execute_SUDOT_Z_ZZZi_S 256 da esize index m n)
  | 512 => (execute_SUDOT_Z_ZZZi_S 512 da esize index m n)
  | 1024 => (execute_SUDOT_Z_ZZZi_S 1024 da esize index m n)
  | 2048 => (execute_SUDOT_Z_ZZZi_S 2048 da esize index m n)
  | _ => (pure ())

def decode_SDOT_Z32_ZZZ__ (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SDOT_Z32_ZZZ__ 128 da esize m n)
  | 256 => (execute_SDOT_Z32_ZZZ__ 256 da esize m n)
  | 512 => (execute_SDOT_Z32_ZZZ__ 512 da esize m n)
  | 1024 => (execute_SDOT_Z32_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_SDOT_Z32_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_SDOT_Z32_ZZZi__ (i2 : (BitVec 2)) (Zm : (BitVec 3)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SDOT_Z32_ZZZi__ 128 da esize index m n)
  | 256 => (execute_SDOT_Z32_ZZZi__ 256 da esize index m n)
  | 512 => (execute_SDOT_Z32_ZZZi__ 512 da esize index m n)
  | 1024 => (execute_SDOT_Z32_ZZZi__ 1024 da esize index m n)
  | 2048 => (execute_SDOT_Z32_ZZZi__ 2048 da esize index m n)
  | _ => (pure ())

def decode_UDOT_Z32_ZZZ__ (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_UDOT_Z32_ZZZ__ 128 da esize m n)
  | 256 => (execute_UDOT_Z32_ZZZ__ 256 da esize m n)
  | 512 => (execute_UDOT_Z32_ZZZ__ 512 da esize m n)
  | 1024 => (execute_UDOT_Z32_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_UDOT_Z32_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_UDOT_Z32_ZZZi__ (i2 : (BitVec 2)) (Zm : (BitVec 3)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_UDOT_Z32_ZZZi__ 128 da esize index m n)
  | 256 => (execute_UDOT_Z32_ZZZi__ 256 da esize index m n)
  | 512 => (execute_UDOT_Z32_ZZZi__ 512 da esize index m n)
  | 1024 => (execute_UDOT_Z32_ZZZi__ 1024 da esize index m n)
  | 2048 => (execute_UDOT_Z32_ZZZi__ 2048 da esize index m n)
  | _ => (pure ())

def decode_SQABS_Z_P_Z__ (size : (BitVec 2)) (Q : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQABS_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_SQABS_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_SQABS_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_SQABS_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_SQABS_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_SQNEG_Z_P_Z__ (size : (BitVec 2)) (Q : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQNEG_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_SQNEG_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_SQNEG_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_SQNEG_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_SQNEG_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_SQDMULH_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (R : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQDMULH_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_SQDMULH_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_SQDMULH_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_SQDMULH_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_SQDMULH_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_SQRDMULH_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (R : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQRDMULH_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_SQRDMULH_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_SQRDMULH_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_SQRDMULH_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_SQRDMULH_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_SQRDMLAH_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SQRDMLAH_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_SQRDMLAH_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_SQRDMLAH_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_SQRDMLAH_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_SQRDMLAH_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_SQRDMLSH_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SQRDMLSH_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_SQRDMLSH_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_SQRDMLSH_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_SQRDMLSH_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_SQRDMLSH_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_ADDP_Z_P_ZZ__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let m := (BitVec.toNat Zm)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_ADDP_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_ADDP_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_ADDP_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_ADDP_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_ADDP_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_UMAXP_Z_P_ZZ__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let m := (BitVec.toNat Zm)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_UMAXP_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_UMAXP_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_UMAXP_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_UMAXP_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_UMAXP_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_SMAXP_Z_P_ZZ__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let m := (BitVec.toNat Zm)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_SMAXP_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_SMAXP_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_SMAXP_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_SMAXP_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_SMAXP_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_UMINP_Z_P_ZZ__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let m := (BitVec.toNat Zm)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_UMINP_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_UMINP_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_UMINP_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_UMINP_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_UMINP_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_SMINP_Z_P_ZZ__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let m := (BitVec.toNat Zm)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_SMINP_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_SMINP_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_SMINP_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_SMINP_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_SMINP_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_SADALP_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SADALP_Z_P_Z__ 128 da esize g n)
  | 256 => (execute_SADALP_Z_P_Z__ 256 da esize g n)
  | 512 => (execute_SADALP_Z_P_Z__ 512 da esize g n)
  | 1024 => (execute_SADALP_Z_P_Z__ 1024 da esize g n)
  | 2048 => (execute_SADALP_Z_P_Z__ 2048 da esize g n)
  | _ => (pure ())

def decode_UADALP_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_UADALP_Z_P_Z__ 128 da esize g n)
  | 256 => (execute_UADALP_Z_P_Z__ 256 da esize g n)
  | 512 => (execute_UADALP_Z_P_Z__ 512 da esize g n)
  | 1024 => (execute_UADALP_Z_P_Z__ 1024 da esize g n)
  | 2048 => (execute_UADALP_Z_P_Z__ 2048 da esize g n)
  | _ => (pure ())

def decode_SHRNB_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 => (execute_SHRNB_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_SHRNB_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_SHRNB_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_SHRNB_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_SHRNB_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SHRNT_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 => (execute_SHRNT_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_SHRNT_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_SHRNT_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_SHRNT_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_SHRNT_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_RSHRNB_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 => (execute_RSHRNB_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_RSHRNB_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_RSHRNB_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_RSHRNB_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_RSHRNB_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_RSHRNT_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 => (execute_RSHRNT_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_RSHRNT_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_RSHRNT_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_RSHRNT_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_RSHRNT_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQSHRNB_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 => (execute_SQSHRNB_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_SQSHRNB_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_SQSHRNB_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_SQSHRNB_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_SQSHRNB_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQSHRNT_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 => (execute_SQSHRNT_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_SQSHRNT_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_SQSHRNT_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_SQSHRNT_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_SQSHRNT_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_UQSHRNB_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 => (execute_UQSHRNB_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_UQSHRNB_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_UQSHRNB_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_UQSHRNB_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_UQSHRNB_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_UQSHRNT_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 => (execute_UQSHRNT_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_UQSHRNT_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_UQSHRNT_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_UQSHRNT_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_UQSHRNT_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQRSHRNB_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 => (execute_SQRSHRNB_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_SQRSHRNB_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_SQRSHRNB_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_SQRSHRNB_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_SQRSHRNB_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQRSHRNT_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 => (execute_SQRSHRNT_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_SQRSHRNT_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_SQRSHRNT_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_SQRSHRNT_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_SQRSHRNT_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_UQRSHRNB_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 => (execute_UQRSHRNB_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_UQRSHRNB_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_UQRSHRNB_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_UQRSHRNB_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_UQRSHRNB_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_UQRSHRNT_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 => (execute_UQRSHRNT_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_UQRSHRNT_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_UQRSHRNT_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_UQRSHRNT_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_UQRSHRNT_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQSHRUNB_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 => (execute_SQSHRUNB_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_SQSHRUNB_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_SQSHRUNB_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_SQSHRUNB_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_SQSHRUNB_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQSHRUNT_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 => (execute_SQSHRUNT_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_SQSHRUNT_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_SQSHRUNT_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_SQSHRUNT_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_SQSHRUNT_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQRSHRUNB_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 => (execute_SQRSHRUNB_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_SQRSHRUNB_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_SQRSHRUNB_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_SQRSHRUNB_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_SQRSHRUNB_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQRSHRUNT_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match VL with
  | 128 => (execute_SQRSHRUNT_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_SQRSHRUNT_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_SQRSHRUNT_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_SQRSHRUNT_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_SQRSHRUNT_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SRSHR_Z_P_ZI__ (tszh : (BitVec 2)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0x0#4 : (BitVec 4))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0x1#4 : (BitVec 4))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 3 1) == (0b001#3 : (BitVec 3))) : Bool)
        then (pure 16)
        else
          (if (((Sail.BitVec.extractLsb b__0 3 2) == (0b01#2 : (BitVec 2))) : Bool)
          then (pure 32)
          else (pure 64)))) ) : SailM Int )
  let esize := esize
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_SRSHR_Z_P_ZI__ 128 dn 8 g shift)
      | 256 => (execute_SRSHR_Z_P_ZI__ 256 dn 8 g shift)
      | 512 => (execute_SRSHR_Z_P_ZI__ 512 dn 8 g shift)
      | 1024 => (execute_SRSHR_Z_P_ZI__ 1024 dn 8 g shift)
      | 2048 => (execute_SRSHR_Z_P_ZI__ 2048 dn 8 g shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_SRSHR_Z_P_ZI__ 128 dn 16 g shift)
      | 256 => (execute_SRSHR_Z_P_ZI__ 256 dn 16 g shift)
      | 512 => (execute_SRSHR_Z_P_ZI__ 512 dn 16 g shift)
      | 1024 => (execute_SRSHR_Z_P_ZI__ 1024 dn 16 g shift)
      | 2048 => (execute_SRSHR_Z_P_ZI__ 2048 dn 16 g shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_SRSHR_Z_P_ZI__ 128 dn 32 g shift)
      | 256 => (execute_SRSHR_Z_P_ZI__ 256 dn 32 g shift)
      | 512 => (execute_SRSHR_Z_P_ZI__ 512 dn 32 g shift)
      | 1024 => (execute_SRSHR_Z_P_ZI__ 1024 dn 32 g shift)
      | 2048 => (execute_SRSHR_Z_P_ZI__ 2048 dn 32 g shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_SRSHR_Z_P_ZI__ 128 dn 64 g shift)
      | 256 => (execute_SRSHR_Z_P_ZI__ 256 dn 64 g shift)
      | 512 => (execute_SRSHR_Z_P_ZI__ 512 dn 64 g shift)
      | 1024 => (execute_SRSHR_Z_P_ZI__ 1024 dn 64 g shift)
      | 2048 => (execute_SRSHR_Z_P_ZI__ 2048 dn 64 g shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:37602.22-37602.23"

def decode_URSHR_Z_P_ZI__ (tszh : (BitVec 2)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0x0#4 : (BitVec 4))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0x1#4 : (BitVec 4))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 3 1) == (0b001#3 : (BitVec 3))) : Bool)
        then (pure 16)
        else
          (if (((Sail.BitVec.extractLsb b__0 3 2) == (0b01#2 : (BitVec 2))) : Bool)
          then (pure 32)
          else (pure 64)))) ) : SailM Int )
  let esize := esize
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_URSHR_Z_P_ZI__ 128 dn 8 g shift)
      | 256 => (execute_URSHR_Z_P_ZI__ 256 dn 8 g shift)
      | 512 => (execute_URSHR_Z_P_ZI__ 512 dn 8 g shift)
      | 1024 => (execute_URSHR_Z_P_ZI__ 1024 dn 8 g shift)
      | 2048 => (execute_URSHR_Z_P_ZI__ 2048 dn 8 g shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_URSHR_Z_P_ZI__ 128 dn 16 g shift)
      | 256 => (execute_URSHR_Z_P_ZI__ 256 dn 16 g shift)
      | 512 => (execute_URSHR_Z_P_ZI__ 512 dn 16 g shift)
      | 1024 => (execute_URSHR_Z_P_ZI__ 1024 dn 16 g shift)
      | 2048 => (execute_URSHR_Z_P_ZI__ 2048 dn 16 g shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_URSHR_Z_P_ZI__ 128 dn 32 g shift)
      | 256 => (execute_URSHR_Z_P_ZI__ 256 dn 32 g shift)
      | 512 => (execute_URSHR_Z_P_ZI__ 512 dn 32 g shift)
      | 1024 => (execute_URSHR_Z_P_ZI__ 1024 dn 32 g shift)
      | 2048 => (execute_URSHR_Z_P_ZI__ 2048 dn 32 g shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_URSHR_Z_P_ZI__ 128 dn 64 g shift)
      | 256 => (execute_URSHR_Z_P_ZI__ 256 dn 64 g shift)
      | 512 => (execute_URSHR_Z_P_ZI__ 512 dn 64 g shift)
      | 1024 => (execute_URSHR_Z_P_ZI__ 1024 dn 64 g shift)
      | 2048 => (execute_URSHR_Z_P_ZI__ 2048 dn 64 g shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:37755.22-37755.23"

def decode_SQSHL_Z_P_ZI__ (tszh : (BitVec 2)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0x0#4 : (BitVec 4))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0x1#4 : (BitVec 4))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 3 1) == (0b001#3 : (BitVec 3))) : Bool)
        then (pure 16)
        else
          (if (((Sail.BitVec.extractLsb b__0 3 2) == (0b01#2 : (BitVec 2))) : Bool)
          then (pure 32)
          else (pure 64)))) ) : SailM Int )
  let esize := esize
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let shift := ((BitVec.toNat (tsize +++ imm3)) -i esize)
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_SQSHL_Z_P_ZI__ 128 dn 8 g shift)
      | 256 => (execute_SQSHL_Z_P_ZI__ 256 dn 8 g shift)
      | 512 => (execute_SQSHL_Z_P_ZI__ 512 dn 8 g shift)
      | 1024 => (execute_SQSHL_Z_P_ZI__ 1024 dn 8 g shift)
      | 2048 => (execute_SQSHL_Z_P_ZI__ 2048 dn 8 g shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_SQSHL_Z_P_ZI__ 128 dn 16 g shift)
      | 256 => (execute_SQSHL_Z_P_ZI__ 256 dn 16 g shift)
      | 512 => (execute_SQSHL_Z_P_ZI__ 512 dn 16 g shift)
      | 1024 => (execute_SQSHL_Z_P_ZI__ 1024 dn 16 g shift)
      | 2048 => (execute_SQSHL_Z_P_ZI__ 2048 dn 16 g shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_SQSHL_Z_P_ZI__ 128 dn 32 g shift)
      | 256 => (execute_SQSHL_Z_P_ZI__ 256 dn 32 g shift)
      | 512 => (execute_SQSHL_Z_P_ZI__ 512 dn 32 g shift)
      | 1024 => (execute_SQSHL_Z_P_ZI__ 1024 dn 32 g shift)
      | 2048 => (execute_SQSHL_Z_P_ZI__ 2048 dn 32 g shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_SQSHL_Z_P_ZI__ 128 dn 64 g shift)
      | 256 => (execute_SQSHL_Z_P_ZI__ 256 dn 64 g shift)
      | 512 => (execute_SQSHL_Z_P_ZI__ 512 dn 64 g shift)
      | 1024 => (execute_SQSHL_Z_P_ZI__ 1024 dn 64 g shift)
      | 2048 => (execute_SQSHL_Z_P_ZI__ 2048 dn 64 g shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:37908.22-37908.23"

def decode_UQSHL_Z_P_ZI__ (tszh : (BitVec 2)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0x0#4 : (BitVec 4))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0x1#4 : (BitVec 4))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 3 1) == (0b001#3 : (BitVec 3))) : Bool)
        then (pure 16)
        else
          (if (((Sail.BitVec.extractLsb b__0 3 2) == (0b01#2 : (BitVec 2))) : Bool)
          then (pure 32)
          else (pure 64)))) ) : SailM Int )
  let esize := esize
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let shift := ((BitVec.toNat (tsize +++ imm3)) -i esize)
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_UQSHL_Z_P_ZI__ 128 dn 8 g shift)
      | 256 => (execute_UQSHL_Z_P_ZI__ 256 dn 8 g shift)
      | 512 => (execute_UQSHL_Z_P_ZI__ 512 dn 8 g shift)
      | 1024 => (execute_UQSHL_Z_P_ZI__ 1024 dn 8 g shift)
      | 2048 => (execute_UQSHL_Z_P_ZI__ 2048 dn 8 g shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_UQSHL_Z_P_ZI__ 128 dn 16 g shift)
      | 256 => (execute_UQSHL_Z_P_ZI__ 256 dn 16 g shift)
      | 512 => (execute_UQSHL_Z_P_ZI__ 512 dn 16 g shift)
      | 1024 => (execute_UQSHL_Z_P_ZI__ 1024 dn 16 g shift)
      | 2048 => (execute_UQSHL_Z_P_ZI__ 2048 dn 16 g shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_UQSHL_Z_P_ZI__ 128 dn 32 g shift)
      | 256 => (execute_UQSHL_Z_P_ZI__ 256 dn 32 g shift)
      | 512 => (execute_UQSHL_Z_P_ZI__ 512 dn 32 g shift)
      | 1024 => (execute_UQSHL_Z_P_ZI__ 1024 dn 32 g shift)
      | 2048 => (execute_UQSHL_Z_P_ZI__ 2048 dn 32 g shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_UQSHL_Z_P_ZI__ 128 dn 64 g shift)
      | 256 => (execute_UQSHL_Z_P_ZI__ 256 dn 64 g shift)
      | 512 => (execute_UQSHL_Z_P_ZI__ 512 dn 64 g shift)
      | 1024 => (execute_UQSHL_Z_P_ZI__ 1024 dn 64 g shift)
      | 2048 => (execute_UQSHL_Z_P_ZI__ 2048 dn 64 g shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:38061.22-38061.23"

def decode_SQSHLU_Z_P_ZI__ (tszh : (BitVec 2)) (L : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 4) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0x0#4 : (BitVec 4))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0x1#4 : (BitVec 4))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 3 1) == (0b001#3 : (BitVec 3))) : Bool)
        then (pure 16)
        else
          (if (((Sail.BitVec.extractLsb b__0 3 2) == (0b01#2 : (BitVec 2))) : Bool)
          then (pure 32)
          else (pure 64)))) ) : SailM Int )
  let esize := esize
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let shift := ((BitVec.toNat (tsize +++ imm3)) -i esize)
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_SQSHLU_Z_P_ZI__ 128 dn 8 g shift)
      | 256 => (execute_SQSHLU_Z_P_ZI__ 256 dn 8 g shift)
      | 512 => (execute_SQSHLU_Z_P_ZI__ 512 dn 8 g shift)
      | 1024 => (execute_SQSHLU_Z_P_ZI__ 1024 dn 8 g shift)
      | 2048 => (execute_SQSHLU_Z_P_ZI__ 2048 dn 8 g shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_SQSHLU_Z_P_ZI__ 128 dn 16 g shift)
      | 256 => (execute_SQSHLU_Z_P_ZI__ 256 dn 16 g shift)
      | 512 => (execute_SQSHLU_Z_P_ZI__ 512 dn 16 g shift)
      | 1024 => (execute_SQSHLU_Z_P_ZI__ 1024 dn 16 g shift)
      | 2048 => (execute_SQSHLU_Z_P_ZI__ 2048 dn 16 g shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_SQSHLU_Z_P_ZI__ 128 dn 32 g shift)
      | 256 => (execute_SQSHLU_Z_P_ZI__ 256 dn 32 g shift)
      | 512 => (execute_SQSHLU_Z_P_ZI__ 512 dn 32 g shift)
      | 1024 => (execute_SQSHLU_Z_P_ZI__ 1024 dn 32 g shift)
      | 2048 => (execute_SQSHLU_Z_P_ZI__ 2048 dn 32 g shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_SQSHLU_Z_P_ZI__ 128 dn 64 g shift)
      | 256 => (execute_SQSHLU_Z_P_ZI__ 256 dn 64 g shift)
      | 512 => (execute_SQSHLU_Z_P_ZI__ 512 dn 64 g shift)
      | 1024 => (execute_SQSHLU_Z_P_ZI__ 1024 dn 64 g shift)
      | 2048 => (execute_SQSHLU_Z_P_ZI__ 2048 dn 64 g shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:38214.22-38214.23"

def decode_SSHLLB_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((BitVec.toNat (tsize +++ imm3)) -i esize)
  match VL with
  | 128 => (execute_SSHLLB_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_SSHLLB_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_SSHLLB_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_SSHLLB_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_SSHLLB_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SSHLLT_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((BitVec.toNat (tsize +++ imm3)) -i esize)
  match VL with
  | 128 => (execute_SSHLLT_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_SSHLLT_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_SSHLLT_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_SSHLLT_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_SSHLLT_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_USHLLB_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((BitVec.toNat (tsize +++ imm3)) -i esize)
  match VL with
  | 128 => (execute_USHLLB_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_USHLLB_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_USHLLB_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_USHLLB_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_USHLLB_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_USHLLT_Z_ZI__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 8
  let esize ← (( do
    let b__0 := tsize
    if ((b__0 == (0b000#3 : (BitVec 3))) : Bool)
    then sailThrow ((Error_Undefined ()))
    else
      (if ((b__0 == (0b001#3 : (BitVec 3))) : Bool)
      then (pure 8)
      else
        (if (((Sail.BitVec.extractLsb b__0 2 1) == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 16)
        else (pure 32))) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((BitVec.toNat (tsize +++ imm3)) -i esize)
  match VL with
  | 128 => (execute_USHLLT_Z_ZI__ 128 d esize n shift)
  | 256 => (execute_USHLLT_Z_ZI__ 256 d esize n shift)
  | 512 => (execute_USHLLT_Z_ZI__ 512 d esize n shift)
  | 1024 => (execute_USHLLT_Z_ZI__ 1024 d esize n shift)
  | 2048 => (execute_USHLLT_Z_ZI__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQXTNB_Z_ZZ__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 16
  let esize ← (( do
    match (tsize : BitVec 3) with
    | 0b001 => (pure 16)
    | 0b010 => (pure 32)
    | 0b100 => (pure 64)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQXTNB_Z_ZZ__ 128 d esize n)
  | 256 => (execute_SQXTNB_Z_ZZ__ 256 d esize n)
  | 512 => (execute_SQXTNB_Z_ZZ__ 512 d esize n)
  | 1024 => (execute_SQXTNB_Z_ZZ__ 1024 d esize n)
  | 2048 => (execute_SQXTNB_Z_ZZ__ 2048 d esize n)
  | _ => (pure ())

def decode_UQXTNB_Z_ZZ__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 16
  let esize ← (( do
    match (tsize : BitVec 3) with
    | 0b001 => (pure 16)
    | 0b010 => (pure 32)
    | 0b100 => (pure 64)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_UQXTNB_Z_ZZ__ 128 d esize n)
  | 256 => (execute_UQXTNB_Z_ZZ__ 256 d esize n)
  | 512 => (execute_UQXTNB_Z_ZZ__ 512 d esize n)
  | 1024 => (execute_UQXTNB_Z_ZZ__ 1024 d esize n)
  | 2048 => (execute_UQXTNB_Z_ZZ__ 2048 d esize n)
  | _ => (pure ())

def decode_SQXTUNB_Z_ZZ__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 16
  let esize ← (( do
    match (tsize : BitVec 3) with
    | 0b001 => (pure 16)
    | 0b010 => (pure 32)
    | 0b100 => (pure 64)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQXTUNB_Z_ZZ__ 128 d esize n)
  | 256 => (execute_SQXTUNB_Z_ZZ__ 256 d esize n)
  | 512 => (execute_SQXTUNB_Z_ZZ__ 512 d esize n)
  | 1024 => (execute_SQXTUNB_Z_ZZ__ 1024 d esize n)
  | 2048 => (execute_SQXTUNB_Z_ZZ__ 2048 d esize n)
  | _ => (pure ())

def decode_SQXTNT_Z_ZZ__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 16
  let esize ← (( do
    match (tsize : BitVec 3) with
    | 0b001 => (pure 16)
    | 0b010 => (pure 32)
    | 0b100 => (pure 64)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQXTNT_Z_ZZ__ 128 d esize n)
  | 256 => (execute_SQXTNT_Z_ZZ__ 256 d esize n)
  | 512 => (execute_SQXTNT_Z_ZZ__ 512 d esize n)
  | 1024 => (execute_SQXTNT_Z_ZZ__ 1024 d esize n)
  | 2048 => (execute_SQXTNT_Z_ZZ__ 2048 d esize n)
  | _ => (pure ())

def decode_UQXTNT_Z_ZZ__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 16
  let esize ← (( do
    match (tsize : BitVec 3) with
    | 0b001 => (pure 16)
    | 0b010 => (pure 32)
    | 0b100 => (pure 64)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_UQXTNT_Z_ZZ__ 128 d esize n)
  | 256 => (execute_UQXTNT_Z_ZZ__ 256 d esize n)
  | 512 => (execute_UQXTNT_Z_ZZ__ 512 d esize n)
  | 1024 => (execute_UQXTNT_Z_ZZ__ 1024 d esize n)
  | 2048 => (execute_UQXTNT_Z_ZZ__ 2048 d esize n)
  | _ => (pure ())

def decode_SQXTUNT_Z_ZZ__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let tsize : (BitVec 3) := (tszh +++ tszl)
  let esize : Nat := 16
  let esize ← (( do
    match (tsize : BitVec 3) with
    | 0b001 => (pure 16)
    | 0b010 => (pure 32)
    | 0b100 => (pure 64)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQXTUNT_Z_ZZ__ 128 d esize n)
  | 256 => (execute_SQXTUNT_Z_ZZ__ 256 d esize n)
  | 512 => (execute_SQXTUNT_Z_ZZ__ 512 d esize n)
  | 1024 => (execute_SQXTUNT_Z_ZZ__ 1024 d esize n)
  | 2048 => (execute_SQXTUNT_Z_ZZ__ 2048 d esize n)
  | _ => (pure ())

def decode_SMULLT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SMULLT_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_SMULLT_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_SMULLT_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_SMULLT_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_SMULLT_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_SMULLB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SMULLB_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_SMULLB_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_SMULLB_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_SMULLB_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_SMULLB_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_UMULLT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_UMULLT_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_UMULLT_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_UMULLT_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_UMULLT_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_UMULLT_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_UMULLB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_UMULLB_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_UMULLB_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_UMULLB_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_UMULLB_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_UMULLB_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_SQDMULLT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQDMULLT_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_SQDMULLT_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_SQDMULLT_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_SQDMULLT_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_SQDMULLT_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_SQDMULLB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQDMULLB_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_SQDMULLB_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_SQDMULLB_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_SQDMULLB_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_SQDMULLB_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_SMLALT_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SMLALT_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_SMLALT_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_SMLALT_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_SMLALT_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_SMLALT_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_SMLALB_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SMLALB_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_SMLALB_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_SMLALB_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_SMLALB_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_SMLALB_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_UMLALT_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_UMLALT_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_UMLALT_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_UMLALT_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_UMLALT_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_UMLALT_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_UMLALB_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_UMLALB_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_UMLALB_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_UMLALB_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_UMLALB_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_UMLALB_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_SQDMLALT_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel1 := 1
  let sel2 := 1
  match VL with
  | 128 => (execute_SQDMLALT_Z_ZZZ__ 128 da esize m n sel1 sel2)
  | 256 => (execute_SQDMLALT_Z_ZZZ__ 256 da esize m n sel1 sel2)
  | 512 => (execute_SQDMLALT_Z_ZZZ__ 512 da esize m n sel1 sel2)
  | 1024 => (execute_SQDMLALT_Z_ZZZ__ 1024 da esize m n sel1 sel2)
  | 2048 => (execute_SQDMLALT_Z_ZZZ__ 2048 da esize m n sel1 sel2)
  | _ => (pure ())


