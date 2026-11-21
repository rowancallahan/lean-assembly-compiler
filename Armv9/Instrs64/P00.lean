import Armv9.Armv9
import Armv9.Flow
import Armv9.Arith
import Armv9.Vector
import Armv9.ReverseEndianness
import Armv9.Prelude
import Armv9.Builtins
import Armv9.V8Base
import Armv9.Stubs
import Armv9.Interrupts
import Armv9.Interface
import Armv9.Impdefs
import Armv9.Sysregs
import Armv9Core.Instrs64

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

/-- Type quantifiers: d : Nat, datasize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_unary_abs (d : Nat) (datasize : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let result := (Int.natAbs (BitVec.toInt operand1))
  (X_set d datasize (integer_subrange result (datasize -i 1) 0))

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, k_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (neg : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int ()) ) : SailM Int )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (pure (BitVec.toInt (← (Elem_read operand e esize))))
        let element : Int :=
          if (neg : Bool)
          then (Neg.neg element)
          else (Int.natAbs element)
        let result ← (Elem_set result e esize (integer_subrange element (esize -i 1) 0))
        (pure (element, result))
    (pure loop_vars) ) : SailM (Int × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, k_setflags : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_add_sub_carry (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) (setflags : Bool) (sub_op : Bool) : SailM Unit := do
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (X_read m datasize) ) : SailM (BitVec datasize) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let operand2 : (BitVec datasize) :=
    if (sub_op : Bool)
    then (Complement.complement operand2)
    else operand2
  let (nzcv, result) ← (( do
    let (tup__0, tup__1) ← do (pure (AddWithCarry operand1 operand2 (← readReg PSTATE).C))
    let result : (BitVec datasize) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (pure (nzcv, result)) ) : SailM ((BitVec 4) × (BitVec datasize)) )
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure ())
  (X_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e esize)
        let element2 ← (Elem_read operand2 e esize)
        let result ← (( do
          if (sub_op : Bool)
          then (do (Elem_set result e esize (element1 - element2)))
          else (do (Elem_set result e esize (element1 + element2))) ) : SailM (BitVec datasize) )
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

def decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  if ((shift == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((sf == 0#1) && ((BitVec.join1 [(BitVec.access imm6 5)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
  let shift_amount := (BitVec.toNat imm6)
  (execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg d datasize m n setflags shift_amount shift_type sub_op)

def decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (sh : (BitVec 1)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let imm ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let imm : (BitVec datasize) :=
    match (sh : BitVec 1) with
    | 0 => (Sail.BitVec.zeroExtend imm12 datasize)
    | _ => (Sail.BitVec.zeroExtend (imm12 +++ (Zeros (n := 12))) datasize)
  let imm := imm
  (execute_aarch64_instrs_integer_arithmetic_add_sub_immediate d datasize imm n setflags sub_op)

/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, k_setflags : Bool, shift : Nat, k_sub_op : Bool, List.elem shift [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (d : Nat) (datasize : Nat) (extend_type : ExtendType) (m : Nat) (n : Nat) (setflags : Bool) (shift : Nat) (sub_op : Bool) : SailM Unit := do
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then (pure (Sail.BitVec.extractLsb (← (SP_read ())) (datasize -i 1) 0))
    else (X_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (ExtendReg m extend_type shift datasize) ) : SailM (BitVec datasize) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let carry_in ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (carry_in, operand2) : ((BitVec 1) × (BitVec datasize)) :=
    if (sub_op : Bool)
    then
      (let operand2 : (BitVec datasize) := (Complement.complement operand2)
      let carry_in : (BitVec 1) := 1#1
      (carry_in, operand2))
    else
      (let carry_in : (BitVec 1) := 0#1
      (carry_in, operand2))
  let (nzcv, result) : ((BitVec 4) × (BitVec datasize)) :=
    let (tup__0, tup__1) := ((AddWithCarry operand1 operand2 carry_in) : ((BitVec datasize) × (BitVec 4)))
    let result : (BitVec datasize) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (nzcv, result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure ())
  if (((d == 31) && (! setflags)) : Bool)
  then (SP_set (Sail.BitVec.zeroExtend result 64))
  else (X_set d datasize result)

/-- Type quantifiers: k_ADD : Bool, d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcaddtag (ADD : Bool) (d : Nat) (n : Nat) (offset : (BitVec 64)) (tag_offset : (BitVec 4)) : SailM Unit := do
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then (SP_read ())
    else (X_read n 64) ) : SailM (BitVec 64) )
  let start_tag : (BitVec 4) := (AArch64_AllocationTagFromAddress operand1)
  let exclude ← (( do (pure (_get_GCR_EL1_Type_Exclude (← readReg GCR_EL1))) ) : SailM (BitVec 16) )
  let result ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let rtag ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let rtag ← (( do
    if ((← (AArch64_AllocationTagAccessIsEnabled (← readReg PSTATE).EL)) : Bool)
    then (pure (AArch64_ChooseNonExcludedTag start_tag tag_offset exclude))
    else (pure 0b0000#4) ) : SailM (BitVec 4) )
  let result : (BitVec 64) :=
    if (ADD : Bool)
    then
      (let (__tup_0, _) := (AddWithCarry operand1 offset 0#1)
      __tup_0)
    else
      (let (__tup_0, _) := (AddWithCarry operand1 (Complement.complement offset) 1#1)
      __tup_0)
  let result ← (( do (AArch64_AddressWithAllocationTag result rtag) ) : SailM (BitVec 64) )
  if ((d == 31) : Bool)
  then (SP_set result)
  else (X_set d 64 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, part : Nat, k_round : Bool, k_sub_op : Bool, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) (round : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let operand2 ← (( do (V_read m (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let sum ← (( do (undefined_int ()) ) : SailM Int )
  let (element1, element2, result, sum) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result, sum)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result, sum) := loop_vars
      loop_vars ← do
        let element1 ← (pure (BitVec.toNat (← (Elem_read operand1 e (2 *i esize)))))
        let element2 ← (pure (BitVec.toNat (← (Elem_read operand2 e (2 *i esize)))))
        let sum : Int :=
          if (sub_op : Bool)
          then (element1 -i element2)
          else (element1 +i element2)
        let sum ← (RShr sum esize round)
        let result ← (Elem_set result e esize (integer_subrange sum (esize -i 1) 0))
        (pure (element1, element2, result, sum))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec datasize) × Int) )
  (Vpart_set d part datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let concat : (BitVec (2 * datasize)) := (operand2 +++ operand1)
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read concat (2 *i e) esize)
        let element2 ← (Elem_read concat ((2 *i e) +i 1) esize)
        let result ← (Elem_set result e esize (element1 + element2))
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_reduce_add_sisd (d : Nat) (datasize : Nat) (esize : Nat) (n : Nat) (op : ReduceOp) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  sail_assert (datasize ≥b esize) "src/instrs64.sail:1153.42-1153.43"
  (V_set d esize (← (Reduce op operand esize)))

/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_reduce_add_simd (d : Nat) (datasize : Nat) (esize : Nat) (n : Nat) (op : ReduceOp) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  (V_set d esize (← (Reduce op operand esize)))

/-- Type quantifiers: d : Nat, k_page : Bool, 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_address_pc_rel (d : Nat) (imm : (BitVec 64)) (page : Bool) : SailM Unit := do
  let base ← (( do (PC_read ()) ) : SailM (BitVec 64) )
  let base : (BitVec 64) :=
    if (page : Bool)
    then (Sail.BitVec.updateSubrange base 11 0 (Zeros (n := 12)))
    else base
  (X_set d 64 (base + imm))

/-- Type quantifiers: d : Nat, k_decrypt : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_aes_round (d : Nat) (decrypt : Bool) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let operand1 ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let operand2 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let result : (BitVec 128) := (operand1 ^^^ operand2)
  let result ← (( do
    if (decrypt : Bool)
    then (do (AESInvSubBytes (AESInvShiftRows result)))
    else (do (AESSubBytes (AESShiftRows result))) ) : SailM (BitVec 128) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, k_decrypt : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_aes_mix (d : Nat) (decrypt : Bool) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let operand ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let result ← (( do
    if (decrypt : Bool)
    then (do (AESInvMixColumns operand))
    else (do (AESMixColumns operand)) ) : SailM (BitVec 128) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_logical_immediate (d : Nat) (datasize : Nat) (imm : (BitVec datasize)) (n : Nat) (op : LogicalOp) (setflags : Bool) : SailM Unit := do
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 : (BitVec datasize) := imm
  let result : (BitVec datasize) :=
    match op with
    | .LogicalOp_AND => (operand1 &&& operand2)
    | .LogicalOp_ORR => (operand1 ||| operand2)
    | .LogicalOp_EOR => (operand1 ^^^ operand2)
  let result := result
  if (setflags : Bool)
  then
    (do
      let split_vec := (((BitVec.join1 [(BitVec.access result (datasize -i 1))]) +++ (IsZeroBit result)) +++ 0b00#2)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure ())
  if (((d == 31) && (! setflags)) : Bool)
  then (SP_set (Sail.BitVec.zeroExtend result 64))
  else (X_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, k_invert : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr (d : Nat) (datasize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : LogicalOp) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let operand2 : (BitVec datasize) :=
    if (invert : Bool)
    then (Complement.complement operand2)
    else operand2
  let result : (BitVec datasize) :=
    match op with
    | .LogicalOp_AND => (operand1 &&& operand2)
    | .LogicalOp_ORR => (operand1 ||| operand2)
    | _ => result
  (V_set d datasize result)

def decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match (opc : BitVec 2) with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  if (((sf == 0#1) && ((BitVec.join1 [(BitVec.access imm6 5)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
  let shift_amount := (BitVec.toNat imm6)
  let invert : Bool := (N == 1#1)
  (execute_aarch64_instrs_integer_logical_shiftedreg d datasize invert m n op setflags shift_amount shift_type)

def decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match (opc : BitVec 2) with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  if (((sf == 0#1) && ((BitVec.join1 [(BitVec.access imm6 5)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
  let shift_amount := (BitVec.toNat imm6)
  let invert : Bool := (N == 1#1)
  (execute_aarch64_instrs_integer_logical_shiftedreg d datasize invert m n op setflags shift_amount shift_type)

def decode_bics_aarch64_instrs_integer_logical_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match (opc : BitVec 2) with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  if (((sf == 0#1) && ((BitVec.join1 [(BitVec.access imm6 5)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
  let shift_amount := (BitVec.toNat imm6)
  let invert : Bool := (N == 1#1)
  (execute_aarch64_instrs_integer_logical_shiftedreg d datasize invert m n op setflags shift_amount shift_type)

def decode_eon_aarch64_instrs_integer_logical_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match (opc : BitVec 2) with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  if (((sf == 0#1) && ((BitVec.join1 [(BitVec.access imm6 5)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
  let shift_amount := (BitVec.toNat imm6)
  let invert : Bool := (N == 1#1)
  (execute_aarch64_instrs_integer_logical_shiftedreg d datasize invert m n op setflags shift_amount shift_type)

def decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match (opc : BitVec 2) with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  if (((sf == 0#1) && ((BitVec.join1 [(BitVec.access imm6 5)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
  let shift_amount := (BitVec.toNat imm6)
  let invert : Bool := (N == 1#1)
  (execute_aarch64_instrs_integer_logical_shiftedreg d datasize invert m n op setflags shift_amount shift_type)

def decode_rorv_aarch64_instrs_integer_shift_variable (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let shift_type ← (( do (DecodeShift op2) ) : SailM ShiftType )
  (execute_aarch64_instrs_integer_shift_variable d datasize m n shift_type)

/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_autda_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  let auth_then_branch : Bool := false
  if ((← (HavePACExt ())) : Bool)
  then
    (do
      if (source_is_sp : Bool)
      then (X_set d 64 (← (AuthDA (← (X_read d 64)) (← (SP_read ())) auth_then_branch)))
      else (X_set d 64 (← (AuthDA (← (X_read d 64)) (← (X_read n 64)) auth_then_branch))))
  else (pure ())

/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_autdb_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  let auth_then_branch : Bool := false
  if ((← (HavePACExt ())) : Bool)
  then
    (do
      if (source_is_sp : Bool)
      then (X_set d 64 (← (AuthDB (← (X_read d 64)) (← (SP_read ())) auth_then_branch)))
      else (X_set d 64 (← (AuthDB (← (X_read d 64)) (← (X_read n 64)) auth_then_branch))))
  else (pure ())

/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_autia_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  let auth_then_branch : Bool := false
  if ((← (HavePACExt ())) : Bool)
  then
    (do
      if (source_is_sp : Bool)
      then (X_set d 64 (← (AuthIA (← (X_read d 64)) (← (SP_read ())) auth_then_branch)))
      else (X_set d 64 (← (AuthIA (← (X_read d 64)) (← (X_read n 64)) auth_then_branch))))
  else (pure ())

/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_autib_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  let auth_then_branch : Bool := false
  if ((← (HavePACExt ())) : Bool)
  then
    (do
      if (source_is_sp : Bool)
      then (X_set d 64 (← (AuthIB (← (X_read d 64)) (← (SP_read ())) auth_then_branch)))
      else (X_set d 64 (← (AuthIB (← (X_read d 64)) (← (X_read n 64)) auth_then_branch))))
  else (pure ())

def execute_aarch64_instrs_integer_flags_axflag (_ : Unit) : SailM Unit := do
  let n : (BitVec 1) := 0#1
  let z ← (( do (pure ((← readReg PSTATE).Z ||| (← readReg PSTATE).V)) ) : SailM (BitVec 1) )
  let c ← (( do (pure ((← readReg PSTATE).C &&& (Complement.complement (← readReg PSTATE).V))) ) : SailM (BitVec 1) )
  let v : (BitVec 1) := 0#1
  writeReg PSTATE { (← readReg PSTATE) with N := n }
  writeReg PSTATE { (← readReg PSTATE) with Z := z }
  writeReg PSTATE { (← readReg PSTATE) with C := c }
  writeReg PSTATE { (← readReg PSTATE) with V := v }

def execute_aarch64_instrs_branch_conditional_hinted (condition : (BitVec 4)) (offset : (BitVec 64)) : SailM Unit := do
  let branch_conditional : Bool := true
  if ((← (ConditionHolds condition)) : Bool)
  then (BranchTo ((← (PC_read ())) + offset) BranchType_DIR branch_conditional)
  else (BranchNotTaken BranchType_DIR branch_conditional)

/-- Type quantifiers: a : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3_bcax (a : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Va ← (( do (V_read a 128) ) : SailM (BitVec 128) )
  (V_set d 128 (Vn ^^^ (Vm &&& (Complement.complement Va))))

/-- Type quantifiers: d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_cvt_bf16_scalar (d : Nat) (n : Nat) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operand ← (( do (V_read n 32) ) : SailM (BitVec 32) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read d 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let result ← (Elem_set result 0 16 (← (FPConvertBF__1 operand fpcr)))
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, elements : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ elements = 4 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_cvt_bf16_vector (d : Nat) (elements : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e 16 (← (FPConvertBF__1 (← (Elem_read operand e 32)) (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec 64) )
  (Vpart_set d part 64 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, i : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem i [0, 1, 2, 3] ∧ List.elem elements [2, 4] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_bfdot (d : Nat) (datasize : Nat) (elements : Nat) (i : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let operand3 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16) )
        let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16) )
        let elt2_a ← (( do (Elem_read operand2 ((2 *i i) +i 0) 16) ) : SailM (BitVec 16) )
        let elt2_b ← (( do (Elem_read operand2 ((2 *i i) +i 1) 16) ) : SailM (BitVec 16) )
        let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        let sum ← (( do (BFDotAdd sum elt1_a elt1_b elt2_a elt2_b (← (FPCR_read ()))) ) : SailM (BitVec 32) )
        (Elem_set result e 32 sum)
    (pure loop_vars) ) : SailM (BitVec datasize) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem elements [2, 4] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_bfdot (d : Nat) (datasize : Nat) (elements : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let operand3 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
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
    (pure loop_vars) ) : SailM (BitVec datasize) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, k_extend : Bool, k_inzero : Bool, n : Nat, r : Nat, s : Nat, 0 ≤ s ∧ s ≤ 63 ∧ 0 ≤ r ∧ r ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_bitfield (d : Nat) (datasize : Nat) (extend : Bool) (inzero : Bool) (n : Nat) (r : Nat) (s : Nat) (tmask : (BitVec datasize)) (wmask : (BitVec datasize)) : SailM Unit := do
  let dst ← (( do
    if (inzero : Bool)
    then (pure (Zeros (n := datasize)))
    else (X_read d datasize) ) : SailM (BitVec datasize) )
  let src ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let bot : (BitVec datasize) := ((dst &&& (Complement.complement wmask)) ||| ((ROR src r) &&& wmask))
  let top ← (( do
    if (extend : Bool)
    then
      (do
        sail_assert ((0 ≤b s) && (s <b datasize)) "src/instrs64.sail:2923.53-2923.54"
        (pure (BitVec.replicateBits (BitVec.join1 [(BitVec.access src s)]) datasize)))
    else (pure dst) ) : SailM (BitVec datasize) )
  (X_set d datasize ((top &&& (Complement.complement tmask)) ||| (bot &&& tmask)))

/-- Type quantifiers: d : Nat, elements : Nat, index : Nat, m : Nat, n : Nat, sel : Nat, List.elem sel [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ elements = 4 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_bf16_long (d : Nat) (elements : Nat) (index : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let operand1 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let operand2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let operand3 ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let element2 ← (( do (Elem_read operand2 index 16) ) : SailM (BitVec 16) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i sel) 16) ) : SailM (BitVec 16) )
        let addend ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        (Elem_set result e 32 (← (BFMulAddH addend element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec 128) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, elements : Nat, m : Nat, n : Nat, sel : Nat, List.elem sel [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ elements = 4 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_acc_bf16_long (d : Nat) (elements : Nat) (m : Nat) (n : Nat) (sel : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let operand2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let operand3 ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let element1 ← (( do (Elem_read operand1 ((2 *i e) +i sel) 16) ) : SailM (BitVec 16) )
        let element2 ← (( do (Elem_read operand2 ((2 *i e) +i sel) 16) ) : SailM (BitVec 16) )
        let addend ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        (Elem_set result e 32 (← (BFMulAddH addend element1 element2 (← (FPCR_read ())))))
    (pure loop_vars) ) : SailM (BitVec 128) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_bfmmla (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let op1 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let op2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let acc ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  (V_set d 128 (← (BFMatMulAdd acc op1 op2)))

/-- Type quantifiers: datasize : Nat, rd : Nat, 0 ≤ rd ∧ rd ≤ 31 ∧ List.elem datasize [64, 128] -/
def execute_aarch64_instrs_vector_logical (datasize : Nat) (imm : (BitVec datasize)) (operation : ImmediateOp) (rd : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let result ← (( do
    match operation with
    | .ImmediateOp_MOVI => (pure imm)
    | .ImmediateOp_MVNI => (pure (Complement.complement imm))
    | .ImmediateOp_ORR =>
      (do
        let operand ← (( do (V_read rd datasize) ) : SailM (BitVec datasize) )
        (pure (operand ||| imm)))
    | .ImmediateOp_BIC =>
      (do
        let operand ← (( do (V_read rd datasize) ) : SailM (BitVec datasize) )
        (pure (operand &&& (Complement.complement imm)))) ) : SailM (BitVec datasize) )
  (V_set rd datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) (op : VBitOp) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let operand3 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let operand4 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let (operand1, operand2, operand3) ← (( do
    match op with
    | .VBitOp_VEOR =>
      (do
        let operand1 ← (V_read m datasize)
        let operand2 : (BitVec datasize) := (Zeros (n := datasize))
        let operand3 : (BitVec datasize) := (Ones (n := datasize))
        (pure (operand1, operand2, operand3)))
    | .VBitOp_VBSL =>
      (do
        let operand1 ← (V_read m datasize)
        let operand2 : (BitVec datasize) := operand1
        let operand3 ← (V_read d datasize)
        (pure (operand1, operand2, operand3)))
    | .VBitOp_VBIT =>
      (do
        let operand1 ← (V_read d datasize)
        let operand2 : (BitVec datasize) := operand1
        let operand3 ← (V_read m datasize)
        (pure (operand1, operand2, operand3)))
    | .VBitOp_VBIF =>
      (do
        let operand1 ← (V_read d datasize)
        let operand2 : (BitVec datasize) := operand1
        let operand3 ← (pure (Complement.complement (← (V_read m datasize))))
        (pure (operand1, operand2, operand3))) ) : SailM ((BitVec datasize) × (BitVec datasize) × (BitVec datasize)) )
  let operand3 := operand3
  let operand2 := operand2
  let operand1 := operand1
  (V_set d datasize (operand1 ^^^ ((operand2 ^^^ operand4) &&& operand3)))

def decode_blra_aarch64_instrs_branch_unconditional_register (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) : SailM Unit := do
  let n : Nat := (BitVec.toNat Rn)
  let branch_type ← (( do (undefined_BranchType ()) ) : SailM BranchType )
  let m := (BitVec.toNat Rm)
  let pac : Bool := (A == 1#1)
  let use_key_a : Bool := (M == 0#1)
  let source_is_sp : Bool := ((Z == 1#1) && (m == 31))
  if (((! pac) && (m != 0)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure pac) <&&> (do
           (pure (! (← (HavePACExt ()))))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ()))
  let branch_type ← (( do
    match (op : BitVec 2) with
    | 0b00 => (pure BranchType_INDIR)
    | 0b01 => (pure BranchType_INDCALL)
    | 0b10 => (pure BranchType_RET)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM BranchType )
  let branch_type := branch_type
  let (n, source_is_sp) ← (( do
    if (pac : Bool)
    then
      (do
        if (((Z == 0#1) && (m != 31)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (n, source_is_sp) ← (( do
          if ((BEq.beq branch_type BranchType_RET) : Bool)
          then
            (do
              if ((n != 31) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let n : Nat := 30
              let source_is_sp : Bool := true
              (pure (n, source_is_sp)))
          else (pure (n, source_is_sp)) ) : SailM (Nat × Bool) )
        (pure (n, source_is_sp)))
    else (pure (n, source_is_sp)) ) : SailM (Nat × Bool) )
  let n := n
  (execute_aarch64_instrs_branch_unconditional_register branch_type m n pac source_is_sp use_key_a)

def decode_bra_aarch64_instrs_branch_unconditional_register (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) : SailM Unit := do
  let n : Nat := (BitVec.toNat Rn)
  let branch_type ← (( do (undefined_BranchType ()) ) : SailM BranchType )
  let m := (BitVec.toNat Rm)
  let pac : Bool := (A == 1#1)
  let use_key_a : Bool := (M == 0#1)
  let source_is_sp : Bool := ((Z == 1#1) && (m == 31))
  if (((! pac) && (m != 0)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure pac) <&&> (do
           (pure (! (← (HavePACExt ()))))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ()))
  let branch_type ← (( do
    match (op : BitVec 2) with
    | 0b00 => (pure BranchType_INDIR)
    | 0b01 => (pure BranchType_INDCALL)
    | 0b10 => (pure BranchType_RET)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM BranchType )
  let branch_type := branch_type
  let (n, source_is_sp) ← (( do
    if (pac : Bool)
    then
      (do
        if (((Z == 0#1) && (m != 31)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (n, source_is_sp) ← (( do
          if ((BEq.beq branch_type BranchType_RET) : Bool)
          then
            (do
              if ((n != 31) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let n : Nat := 30
              let source_is_sp : Bool := true
              (pure (n, source_is_sp)))
          else (pure (n, source_is_sp)) ) : SailM (Nat × Bool) )
        (pure (n, source_is_sp)))
    else (pure (n, source_is_sp)) ) : SailM (Nat × Bool) )
  let n := n
  (execute_aarch64_instrs_branch_unconditional_register branch_type m n pac source_is_sp use_key_a)

def decode_reta_aarch64_instrs_branch_unconditional_register (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) : SailM Unit := do
  let n : Nat := (BitVec.toNat Rn)
  let branch_type ← (( do (undefined_BranchType ()) ) : SailM BranchType )
  let m := (BitVec.toNat Rm)
  let pac : Bool := (A == 1#1)
  let use_key_a : Bool := (M == 0#1)
  let source_is_sp : Bool := ((Z == 1#1) && (m == 31))
  if (((! pac) && (m != 0)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure pac) <&&> (do
           (pure (! (← (HavePACExt ()))))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ()))
  let branch_type ← (( do
    match (op : BitVec 2) with
    | 0b00 => (pure BranchType_INDIR)
    | 0b01 => (pure BranchType_INDCALL)
    | 0b10 => (pure BranchType_RET)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM BranchType )
  let branch_type := branch_type
  let (n, source_is_sp) ← (( do
    if (pac : Bool)
    then
      (do
        if (((Z == 0#1) && (m != 31)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (n, source_is_sp) ← (( do
          if ((BEq.beq branch_type BranchType_RET) : Bool)
          then
            (do
              if ((n != 31) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let n : Nat := 30
              let source_is_sp : Bool := true
              (pure (n, source_is_sp)))
          else (pure (n, source_is_sp)) ) : SailM (Nat × Bool) )
        (pure (n, source_is_sp)))
    else (pure (n, source_is_sp)) ) : SailM (Nat × Bool) )
  let n := n
  (execute_aarch64_instrs_branch_unconditional_register branch_type m n pac source_is_sp use_key_a)

def execute_aarch64_instrs_system_exceptions_debug_breakpoint (comment : (BitVec 16)) : SailM Unit := do
  (AArch64_SoftwareBreakpoint comment)

def execute_aarch64_instrs_system_hints (op : SystemHintOp) : SailM Unit := do
  match op with
  | .SystemHintOp_YIELD => (pure (Hint_Yield ()))
  | .SystemHintOp_DGH => (pure (Hint_DGH ()))
  | .SystemHintOp_WFE =>
    (do
      let localtimeout := (Int.shiftl 1 64)
      (Hint_WFE localtimeout WFxType_WFE))
  | .SystemHintOp_WFI =>
    (do
      let localtimeout := (Int.shiftl 1 64)
      (Hint_WFI localtimeout WFxType_WFI))
  | .SystemHintOp_SEV => (pure (SendEvent ()))
  | .SystemHintOp_SEVL => (SendEventLocal ())
  | .SystemHintOp_ESB =>
    (do
      if ((←((HaveTME ()) <&&> (do
           (pure ((← readReg TSTATE).depth >b 0))))) : Bool)
      then (FailTransaction TMFailure_ERR false)
      else (pure ())
      let _ : Unit := (SynchronizeErrors ())
      (AArch64_ESBOperation ())
      if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
           (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
           (EL2Enabled ())))) : Bool)
      then (AArch64_vESBOperation ())
      else (pure ())
      (TakeUnmaskedSErrorInterrupts ()))
  | .SystemHintOp_PSB => (pure (ProfilingSynchronizationBarrier ()))
  | .SystemHintOp_TSB => (pure (TraceSynchronizationBarrier ()))
  | .SystemHintOp_GCSB => (pure (GCSSynchronizationBarrier ()))
  | .SystemHintOp_CHKFEAT => (X_set 16 64 (← (AArch64_ChkFeat (← (X_read 16 64)))))
  | .SystemHintOp_CSDB => (pure (ConsumptionOfSpeculativeDataBarrier ()))
  | .SystemHintOp_CLRBHB => (pure (Hint_CLRBHB ()))
  | .SystemHintOp_BTI => (SetBTypeNext 0b00#2)
  | .SystemHintOp_NOP => (pure ())
  | _ => (Unreachable ())

/-- Type quantifiers: k_acquire : Bool, datasize : Nat, n : Nat, regsize : Nat, k_release : Bool, s : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_atomicops_cas_single (acquire : Bool) (datasize : Nat) (n : Nat) (regsize : Nat) (release : Bool) (s : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescAtomicOp MemAtomicOp_CAS acquire release tagchecked) ) : SailM AccessDescriptor )
  let comparevalue ← (( do (X_read s datasize) ) : SailM (BitVec datasize) )
  let newvalue ← (( do (X_read t datasize) ) : SailM (BitVec datasize) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let data ← (( do (MemAtomic address comparevalue newvalue accdesc) ) : SailM (BitVec datasize) )
  sail_assert (regsize ≥b datasize) "src/instrs64.sail:6398.44-6398.45"
  (X_set s regsize (Sail.BitVec.zeroExtend data regsize))
  if ((← readReg SPESampleInFlight) : Bool)
  then
    (do
      let ar : (BitVec 1) :=
        if ((acquire || release) : Bool)
        then 1#1
        else 0#1
      let excl : (BitVec 1) := 0#1
      let at' : (BitVec 1) := 1#1
      let is_load : Bool := true
      (SPESampleExtendedLoadStore ar excl at' is_load))
  else (pure ())

/-- Type quantifiers: k_acquire : Bool, datasize : Nat, n : Nat, k_release : Bool, s : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] -/
def execute_aarch64_instrs_memory_atomicops_cas_pair (acquire : Bool) (datasize : Nat) (n : Nat) (release : Bool) (s : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let s1 ← (( do (X_read s datasize) ) : SailM (BitVec datasize) )
  let s2 ← (( do (X_read (s +i 1) datasize) ) : SailM (BitVec datasize) )
  let t1 ← (( do (X_read t datasize) ) : SailM (BitVec datasize) )
  let t2 ← (( do (X_read (t +i 1) datasize) ) : SailM (BitVec datasize) )
  let accdesc ← (( do (CreateAccDescAtomicOp MemAtomicOp_CAS acquire release tagchecked) ) : SailM AccessDescriptor )
  let comparevalue ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (s1 +++ s2))
    else (pure (s2 +++ s1)) ) : SailM (BitVec (2 * datasize)) )
  let newvalue ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (t1 +++ t2))
    else (pure (t2 +++ t1)) ) : SailM (BitVec (2 * datasize)) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let data ← (( do (MemAtomic address comparevalue newvalue accdesc) ) : SailM (BitVec (2 * datasize)) )
  if ((← (BigEndian accdesc.acctype)) : Bool)
  then
    (do
      (X_set s datasize (Sail.BitVec.extractLsb data ((2 *i datasize) -i 1) datasize))
      (X_set (s +i 1) datasize (Sail.BitVec.extractLsb data (datasize -i 1) 0)))
  else
    (do
      (X_set s datasize (Sail.BitVec.extractLsb data (datasize -i 1) 0))
      (X_set (s +i 1) datasize (Sail.BitVec.extractLsb data ((2 *i datasize) -i 1) datasize)))
  if ((← readReg SPESampleInFlight) : Bool)
  then
    (do
      let ar : (BitVec 1) :=
        if ((acquire || release) : Bool)
        then 1#1
        else 0#1
      let excl : (BitVec 1) := 0#1
      let at' : (BitVec 1) := 1#1
      let is_load : Bool := true
      (SPESampleExtendedLoadStore ar excl at' is_load))
  else (pure ())

/-- Type quantifiers: datasize : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] -/
def execute_aarch64_instrs_integer_conditional_compare_register (condition : (BitVec 4)) (datasize : Nat) (flags__arg : (BitVec 4)) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  let flags : (BitVec 4) := flags__arg
  let taken : Bool := false
  let (flags, taken) ← (( do
    if ((← (ConditionHolds condition)) : Bool)
    then
      (do
        let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
        let operand2 ← (( do (X_read m datasize) ) : SailM (BitVec datasize) )
        let carry_in : (BitVec 1) := 0#1
        let (carry_in, operand2) : ((BitVec 1) × (BitVec datasize)) :=
          if (sub_op : Bool)
          then
            (let operand2 : (BitVec datasize) := (Complement.complement operand2)
            let carry_in : (BitVec 1) := 1#1
            (carry_in, operand2))
          else (carry_in, operand2)
        let flags : (BitVec 4) :=
          let (_, __tup_1) := (AddWithCarry operand1 operand2 carry_in)
          __tup_1
        let taken : Bool := true
        (pure (flags, taken)))
    else (pure (flags, taken)) ) : SailM ((BitVec 4) × Bool) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb flags 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb flags 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb flags 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb flags 0 0) }
  if ((← readReg SPESampleInFlight) : Bool)
  then
    (do
      let conditional : Bool := true
      (SPESampleAddOpOther conditional taken))
  else (pure ())

/-- Type quantifiers: datasize : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] -/
def execute_aarch64_instrs_integer_conditional_compare_immediate (condition : (BitVec 4)) (datasize : Nat) (flags__arg : (BitVec 4)) (imm : (BitVec datasize)) (n : Nat) (sub_op : Bool) : SailM Unit := do
  let flags : (BitVec 4) := flags__arg
  let taken : Bool := false
  let (flags, taken) ← (( do
    if ((← (ConditionHolds condition)) : Bool)
    then
      (do
        let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
        let operand2 : (BitVec datasize) := imm
        let carry_in : (BitVec 1) := 0#1
        let (carry_in, operand2) : ((BitVec 1) × (BitVec datasize)) :=
          if (sub_op : Bool)
          then
            (let operand2 : (BitVec datasize) := (Complement.complement operand2)
            let carry_in : (BitVec 1) := 1#1
            (carry_in, operand2))
          else (carry_in, operand2)
        let flags : (BitVec 4) :=
          let (_, __tup_1) := (AddWithCarry operand1 operand2 carry_in)
          __tup_1
        let taken : Bool := true
        (pure (flags, taken)))
    else (pure (flags, taken)) ) : SailM ((BitVec 4) × Bool) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb flags 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb flags 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb flags 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb flags 0 0) }
  if ((← readReg SPESampleInFlight) : Bool)
  then
    (do
      let conditional : Bool := true
      (SPESampleAddOpOther conditional taken))
  else (pure ())

def execute_aarch64_instrs_integer_flags_cfinv (_ : Unit) : SailM Unit := do
  writeReg PSTATE { (← readReg PSTATE) with C := ← (do (pure (Complement.complement (← readReg PSTATE).C))) }

def execute_aarch64_instrs_system_monitors (_ : Unit) : Unit :=
  (ClearExclusiveLocal (ProcessorID ()))

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_clsz (countop : CountOp) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let count ← (( do (undefined_int ()) ) : SailM Int )
  let (count, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (count, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (count, result) := loop_vars
      loop_vars ← do
        let count ← (( do
          if ((BEq.beq countop CountOp_CLS) : Bool)
          then (do (pure (CountLeadingSignBits (← (Elem_read operand e esize)))))
          else (do (pure (CountLeadingZeroBits (← (Elem_read operand e esize))))) ) : SailM Int )
        let result ← (Elem_set result e esize (integer_subrange count (esize -i 1) 0))
        (pure (count, result))
    (pure loop_vars) ) : SailM (Int × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_cnt (d : Nat) (datasize : Nat) (n : Nat) (opcode : CountOp) : SailM Unit := do
  let result ← (( do (undefined_int ()) ) : SailM Int )
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let result : Int :=
    if ((BEq.beq opcode CountOp_CLZ) : Bool)
    then (CountLeadingZeroBits operand1)
    else (CountLeadingSignBits operand1)
  let result := result
  (X_set d datasize (integer_subrange result (datasize -i 1) 0))

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (comparison : CompareOp) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int ()) ) : SailM Int )
  let test_passed ← (( do (undefined_bool ()) ) : SailM Bool )
  let (element, result, test_passed) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result, test_passed)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result, test_passed) := loop_vars
      loop_vars ← do
        let element ← (pure (BitVec.toInt (← (Elem_read operand e esize))))
        let test_passed : Bool :=
          match comparison with
          | .CompareOp_GT => (element >b 0)
          | .CompareOp_GE => (element ≥b 0)
          | .CompareOp_EQ => (element == 0)
          | .CompareOp_LE => (element ≤b 0)
          | .CompareOp_LT => (element <b 0)
        let result ←
          (Elem_set result e esize
            (if (test_passed : Bool)
            then (Ones (n := esize))
            else (Zeros (n := esize))))
        (pure (element, result, test_passed))
    (pure loop_vars) ) : SailM (Int × (BitVec datasize) × Bool) )
  (V_set d datasize result)

/-- Type quantifiers: k_and_test : Bool, d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd (and_test : Bool) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let test_passed ← (( do (undefined_bool ()) ) : SailM Bool )
  let (element1, element2, result, test_passed) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result, test_passed)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result, test_passed) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e esize)
        let element2 ← (Elem_read operand2 e esize)
        let test_passed : Bool :=
          if (and_test : Bool)
          then (! (IsZero (element1 &&& element2)))
          else (element1 == element2)
        let result ←
          (Elem_set result e esize
            (if (test_passed : Bool)
            then (Ones (n := esize))
            else (Zeros (n := esize))))
        (pure (element1, element2, result, test_passed))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize) × Bool) )
  (V_set d datasize result)

/-- Type quantifiers: k_cmp_eq : Bool, d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (cmp_eq : Bool) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let test_passed ← (( do (undefined_bool ()) ) : SailM Bool )
  let (element1, element2, result, test_passed) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result, test_passed)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result, test_passed) := loop_vars
      loop_vars ← do
        let element1 ← (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let test_passed : Bool :=
          if (cmp_eq : Bool)
          then (element1 ≥b element2)
          else (element1 >b element2)
        let result ←
          (Elem_set result e esize
            (if (test_passed : Bool)
            then (Ones (n := esize))
            else (Zeros (n := esize))))
        (pure (element1, element2, result, test_passed))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec datasize) × Bool) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd (comparison : CompareOp) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int ()) ) : SailM Int )
  let test_passed ← (( do (undefined_bool ()) ) : SailM Bool )
  let (element, result, test_passed) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result, test_passed)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result, test_passed) := loop_vars
      loop_vars ← do
        let element ← (pure (BitVec.toInt (← (Elem_read operand e esize))))
        let test_passed : Bool :=
          match comparison with
          | .CompareOp_GT => (element >b 0)
          | .CompareOp_GE => (element ≥b 0)
          | .CompareOp_EQ => (element == 0)
          | .CompareOp_LE => (element ≤b 0)
          | .CompareOp_LT => (element <b 0)
        let result ←
          (Elem_set result e esize
            (if (test_passed : Bool)
            then (Ones (n := esize))
            else (Zeros (n := esize))))
        (pure (element, result, test_passed))
    (pure loop_vars) ) : SailM (Int × (BitVec datasize) × Bool) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_unary_cnt (d : Nat) (datasize : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let result := (BitCount operand1)
  (X_set d datasize (integer_subrange result (datasize -i 1) 0))

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ esize = 8 ∧ List.elem elements [8, 16] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_cnt (d : Nat) (datasize : Nat) (elements : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let count ← (( do (undefined_int ()) ) : SailM Int )
  let (count, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (count, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (count, result) := loop_vars
      loop_vars ← do
        let count ← (pure (BitCount (← (Elem_read operand e esize))))
        let result ← (Elem_set result e esize (integer_subrange count (esize -i 1) 0))
        (pure (count, result))
    (pure loop_vars) ) : SailM (Int × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, n : Nat, s : Nat, 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_memory_mcpymset_cpy (d : Nat) (n : Nat) (options_name : (BitVec 4)) (s : Nat) (stage : MOPSStage) : SailM Unit := do
  let N ← do (MaxBlockSizeCopiedBytes ())
  let toaddress ← (( do (X_read d 64) ) : SailM (BitVec 64) )
  let fromaddress ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let cpysize ← (( do (X_read n 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (pure ((← readReg PSTATE).N +++ ((← readReg PSTATE).Z +++ ((← readReg PSTATE).C +++ (← readReg PSTATE).V)))) ) : SailM (BitVec 4) )
  let stagecpysize ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector (8 *i N)) ) : SailM (BitVec (8 * N)) )
  let B ← (( do (undefined_int ()) ) : SailM Int )
  let supports_option_a ← (( do (CPYOptionA ()) ) : SailM Bool )
  let rprivileged ← (( do
    if (((BitVec.join1 [(BitVec.access options_name 1)]) == 1#1) : Bool)
    then (AArch64_IsUnprivAccessPriv ())
    else (pure ((← readReg PSTATE).EL != EL0)) ) : SailM Bool )
  let wprivileged ← (( do
    if (((BitVec.join1 [(BitVec.access options_name 0)]) == 1#1) : Bool)
    then (AArch64_IsUnprivAccessPriv ())
    else (pure ((← readReg PSTATE).EL != EL0)) ) : SailM Bool )
  let rnontemporal : Bool := ((BitVec.join1 [(BitVec.access options_name 3)]) == 1#1)
  let wnontemporal : Bool := ((BitVec.join1 [(BitVec.access options_name 2)]) == 1#1)
  let raccdesc ← (( do (CreateAccDescMOPS MemOp_LOAD rprivileged rnontemporal) ) : SailM AccessDescriptor )
  let waccdesc ← (( do (CreateAccDescMOPS MemOp_STORE wprivileged wnontemporal) ) : SailM AccessDescriptor )
  let (cpysize, fromaddress, nzcv, stagecpysize, toaddress) ← (( do
    if ((BEq.beq stage MOPSStage_Prologue) : Bool)
    then
      (do
        let cpysize : (BitVec 64) :=
          if (((Sail.BitVec.extractLsb cpysize 63 55) != 0b000000000#9) : Bool)
          then 0x007FFFFFFFFFFFFF#64
          else cpysize
        let forward ← (( do (undefined_bool ()) ) : SailM Bool )
        let forward ← (( do
          if ((((BitVec.toNat (Sail.BitVec.extractLsb fromaddress 55 0)) >b (BitVec.toNat (Sail.BitVec.extractLsb toaddress 55 0))) && (((BitVec.toNat (Sail.BitVec.extractLsb fromaddress 55 0)) <b (BitVec.toNat ((Sail.BitVec.extractLsb toaddress 55 0) + (Sail.BitVec.extractLsb cpysize 55 0)))) : Bool)) : Bool)
          then (pure true)
          else
            (do
              if ((((BitVec.toNat (Sail.BitVec.extractLsb fromaddress 55 0)) <b (BitVec.toNat (Sail.BitVec.extractLsb toaddress 55 0))) && (((BitVec.toNat ((Sail.BitVec.extractLsb fromaddress 55 0) + (Sail.BitVec.extractLsb cpysize 55 0))) >b (BitVec.toNat (Sail.BitVec.extractLsb toaddress 55 0))) : Bool)) : Bool)
              then (pure false)
              else (do (MemCpyDirectionChoice fromaddress toaddress cpysize))) ) : SailM Bool )
        let (cpysize, fromaddress, nzcv, toaddress) : ((BitVec 64) × (BitVec 64) × (BitVec 4) × (BitVec 64)) :=
          if (supports_option_a : Bool)
          then
            (let nzcv : (BitVec 4) := 0b0000#4
            let (cpysize, fromaddress, toaddress) : ((BitVec 64) × (BitVec 64) × (BitVec 64)) :=
              if (forward : Bool)
              then
                (let toaddress : (BitVec 64) := (toaddress + cpysize)
                let fromaddress : (BitVec 64) := (fromaddress + cpysize)
                let cpysize : (BitVec 64) := ((Zeros (n := 64)) - cpysize)
                (cpysize, fromaddress, toaddress))
              else (cpysize, fromaddress, toaddress)
            (cpysize, fromaddress, nzcv, toaddress))
          else
            (let (fromaddress, nzcv, toaddress) : ((BitVec 64) × (BitVec 4) × (BitVec 64)) :=
              if ((! forward) : Bool)
              then
                (let toaddress : (BitVec 64) := (toaddress + cpysize)
                let fromaddress : (BitVec 64) := (fromaddress + cpysize)
                let nzcv : (BitVec 4) := 0b1010#4
                (fromaddress, nzcv, toaddress))
              else
                (let nzcv : (BitVec 4) := 0b0010#4
                (fromaddress, nzcv, toaddress))
            (cpysize, fromaddress, nzcv, toaddress))
        let stagecpysize ← (CPYPreSizeChoice toaddress fromaddress cpysize)
        sail_assert (((BitVec.join1 [(BitVec.access stagecpysize 63)]) == (BitVec.join1 [(BitVec.access cpysize 63)])) || (stagecpysize == (Zeros (n := 64)))) "src/instrs64.sail:7892.78-7892.79"
        if (((BitVec.toInt cpysize) >b 0) : Bool)
        then sail_assert ((BitVec.toInt stagecpysize) ≤b (BitVec.toInt cpysize)) "src/instrs64.sail:7894.54-7894.55"
        else sail_assert ((BitVec.toInt stagecpysize) ≥b (BitVec.toInt cpysize)) "src/instrs64.sail:7896.54-7896.55"
        (pure (cpysize, fromaddress, nzcv, stagecpysize, toaddress)))
    else
      (do
        let zero_size_exceptions ← (( do (MemCpyZeroSizeCheck ()) ) : SailM Bool )
        if ((zero_size_exceptions || (((BitVec.toInt cpysize) != 0) : Bool)) : Bool)
        then
          (do
            if (supports_option_a : Bool)
            then
              (do
                if (((BitVec.join1 [(BitVec.access nzcv 1)]) == 1#1) : Bool)
                then
                  (do
                    let wrong_option : Bool := true
                    let from_epilogue : Bool := (BEq.beq stage MOPSStage_Epilogue)
                    (MismatchedMemCpyException supports_option_a d s n wrong_option from_epilogue options_name))
                else (pure ()))
            else
              (do
                if (((BitVec.join1 [(BitVec.access nzcv 1)]) == 0#1) : Bool)
                then
                  (do
                    let wrong_option : Bool := true
                    let from_epilogue : Bool := (BEq.beq stage MOPSStage_Epilogue)
                    (MismatchedMemCpyException supports_option_a d s n wrong_option from_epilogue options_name))
                else (pure ())))
        else (pure ())
        let postsize ← (( do (CPYPostSizeChoice toaddress fromaddress cpysize) ) : SailM (BitVec 64) )
        sail_assert (((BitVec.join1 [(BitVec.access postsize 63)]) == (BitVec.join1 [(BitVec.access cpysize 63)])) || (((BitVec.toInt postsize) == 0) : Bool)) "src/instrs64.sail:7918.68-7918.69"
        let stagecpysize ← (( do
          if ((BEq.beq stage MOPSStage_Main) : Bool)
          then
            (do
              let stagecpysize : (BitVec 64) := (cpysize - postsize)
              if ((← (MemCpyParametersIllformedM toaddress fromaddress cpysize)) : Bool)
              then
                (do
                  let wrong_option : Bool := false
                  let from_epilogue : Bool := false
                  (MismatchedMemCpyException supports_option_a d s n wrong_option from_epilogue options_name))
              else (pure ())
              (pure stagecpysize))
          else
            (do
              let stagecpysize : (BitVec 64) := postsize
              if ((←((pure (cpysize != postsize)) <||> (do
                   (MemCpyParametersIllformedE toaddress fromaddress cpysize)))) : Bool)
              then
                (do
                  let wrong_option : Bool := false
                  let from_epilogue : Bool := true
                  (MismatchedMemCpyException supports_option_a d s n wrong_option from_epilogue options_name))
              else (pure ())
              (pure stagecpysize)) ) : SailM (BitVec 64) )
        (pure (cpysize, fromaddress, nzcv, stagecpysize, toaddress))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec 4) × (BitVec 64) × (BitVec 64)) )
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleMemCopy ())
  else (pure ())
  let (cpysize, fromaddress, toaddress) ← (( do
    if (supports_option_a : Bool)
    then
      (do
        let (B, cpysize, readdata, stagecpysize) ← (( do
          let mut loop_vars_1 := (B, cpysize, readdata, stagecpysize)
          while (λ (B, cpysize, readdata, stagecpysize) => ((BitVec.toInt stagecpysize) != 0)) loop_vars_1 do
            let (B, cpysize, readdata, stagecpysize) := loop_vars_1
            loop_vars_1 ← do
              let B ← (CPYSizeChoice toaddress fromaddress cpysize)
              let (cpysize, readdata, stagecpysize) ← (( do
                let B := B
                let (cpysize, readdata, stagecpysize) ← (( do
                  if (((BitVec.toInt cpysize) <b 0) : Bool)
                  then
                    (do
                      sail_assert (B ≤b ((Neg.neg 1) *i (BitVec.toInt stagecpysize))) "src/instrs64.sail:7946.64-7946.65"
                      sail_assert ((0 ≤b ((B *i 8) -i 1)) && (((B *i 8) -i 1) <b (8 *i N))) "src/instrs64.sail:7947.80-7947.81"
                      let readdata ← (pure (Sail.BitVec.updateSubrange readdata ((B *i 8) -i 1) 0 (← (Mem_read (fromaddress + cpysize) B raccdesc))))
                      (Mem_set (toaddress + cpysize) B waccdesc (Sail.BitVec.extractLsb readdata ((B *i 8) -i 1) 0))
                      let cpysize : (BitVec 64) := (BitVec.addInt cpysize B)
                      let stagecpysize : (BitVec 64) := (BitVec.addInt stagecpysize B)
                      (pure (cpysize, readdata, stagecpysize)))
                  else
                    (do
                      sail_assert (B ≤b (BitVec.toInt stagecpysize)) "src/instrs64.sail:7953.52-7953.53"
                      let cpysize : (BitVec 64) := (BitVec.subInt cpysize B)
                      let stagecpysize : (BitVec 64) := (BitVec.subInt stagecpysize B)
                      sail_assert ((0 ≤b ((B *i 8) -i 1)) && (((B *i 8) -i 1) <b (8 *i N))) "src/instrs64.sail:7956.80-7956.81"
                      let readdata ← (pure (Sail.BitVec.updateSubrange readdata ((B *i 8) -i 1) 0 (← (Mem_read (fromaddress + cpysize) B raccdesc))))
                      (Mem_set (toaddress + cpysize) B waccdesc (Sail.BitVec.extractLsb readdata ((B *i 8) -i 1) 0))
                      (pure (cpysize, readdata, stagecpysize))) ) : SailM ((BitVec 64) × (BitVec (8 * N)) × (BitVec 64)) )
                (pure (cpysize, readdata, stagecpysize)) ) : SailM ((BitVec 64) × (BitVec (8 * N)) × (BitVec 64)) )
              if ((bne stage MOPSStage_Prologue) : Bool)
              then (X_set n 64 cpysize)
              else (pure ())
              (pure (B, cpysize, readdata, stagecpysize))
          (pure loop_vars_1) ) : SailM (Int × (BitVec 64) × (BitVec (8 * N)) × (BitVec 64)) )
        (pure (cpysize, fromaddress, toaddress)))
    else
      (do
        let (B, cpysize, fromaddress, readdata, stagecpysize, toaddress) ← (( do
          let mut loop_vars := (B, cpysize, fromaddress, readdata, stagecpysize, toaddress)
          while (λ (B, cpysize, fromaddress, readdata, stagecpysize, toaddress) => ((BitVec.toNat stagecpysize) >b 0)) loop_vars do
            let (B, cpysize, fromaddress, readdata, stagecpysize, toaddress) := loop_vars
            loop_vars ← do
              let B ← (CPYSizeChoice toaddress fromaddress cpysize)
              sail_assert (B ≤b (BitVec.toNat stagecpysize)) "src/instrs64.sail:7969.42-7969.43"
              let (fromaddress, readdata, toaddress) ← (( do
                let B := B
                let (fromaddress, readdata, toaddress) ← (( do
                  if (((BitVec.join1 [(BitVec.access nzcv 3)]) == 0#1) : Bool)
                  then
                    (do
                      sail_assert ((0 ≤b ((B *i 8) -i 1)) && (((B *i 8) -i 1) <b (8 *i N))) "src/instrs64.sail:7973.80-7973.81"
                      let readdata ← (pure (Sail.BitVec.updateSubrange readdata ((B *i 8) -i 1) 0 (← (Mem_read fromaddress B raccdesc))))
                      (Mem_set toaddress B waccdesc (Sail.BitVec.extractLsb readdata ((B *i 8) -i 1) 0))
                      let fromaddress : (BitVec 64) := (BitVec.addInt fromaddress B)
                      let toaddress : (BitVec 64) := (BitVec.addInt toaddress B)
                      (pure (fromaddress, readdata, toaddress)))
                  else
                    (do
                      sail_assert ((0 ≤b ((B *i 8) -i 1)) && (((B *i 8) -i 1) <b (8 *i N))) "src/instrs64.sail:7979.80-7979.81"
                      let readdata ← (pure (Sail.BitVec.updateSubrange readdata ((B *i 8) -i 1) 0 (← (Mem_read (BitVec.subInt fromaddress B) B raccdesc))))
                      (Mem_set (BitVec.subInt toaddress B) B waccdesc (Sail.BitVec.extractLsb readdata ((B *i 8) -i 1) 0))
                      let fromaddress : (BitVec 64) := (BitVec.subInt fromaddress B)
                      let toaddress : (BitVec 64) := (BitVec.subInt toaddress B)
                      (pure (fromaddress, readdata, toaddress))) ) : SailM ((BitVec 64) × (BitVec (8 * N)) × (BitVec 64)) )
                (pure (fromaddress, readdata, toaddress)) ) : SailM ((BitVec 64) × (BitVec (8 * N)) × (BitVec 64)) )
              let cpysize : (BitVec 64) := (BitVec.subInt cpysize B)
              let stagecpysize : (BitVec 64) := (BitVec.subInt stagecpysize B)
              if ((bne stage MOPSStage_Prologue) : Bool)
              then
                (do
                  (X_set n 64 cpysize)
                  (X_set d 64 toaddress)
                  (X_set s 64 fromaddress))
              else (pure ())
              (pure (B, cpysize, fromaddress, readdata, stagecpysize, toaddress))
          (pure loop_vars) ) : SailM (Int × (BitVec 64) × (BitVec 64) × (BitVec (8 * N)) × (BitVec 64) × (BitVec 64)) )
        (pure (cpysize, fromaddress, toaddress))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec 64)) )
  if ((BEq.beq stage MOPSStage_Prologue) : Bool)
  then
    (do
      (X_set n 64 cpysize)
      (X_set d 64 toaddress)
      (X_set s 64 fromaddress)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure ())

/-- Type quantifiers: d : Nat, n : Nat, s : Nat, 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_memory_mcpymset_cpyf (d : Nat) (n : Nat) (options_name : (BitVec 4)) (s : Nat) (stage : MOPSStage) : SailM Unit := do
  let N ← do (MaxBlockSizeCopiedBytes ())
  let toaddress ← (( do (X_read d 64) ) : SailM (BitVec 64) )
  let fromaddress ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let cpysize ← (( do (X_read n 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (pure ((← readReg PSTATE).N +++ ((← readReg PSTATE).Z +++ ((← readReg PSTATE).C +++ (← readReg PSTATE).V)))) ) : SailM (BitVec 4) )
  let stagecpysize ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector (8 *i N)) ) : SailM (BitVec (8 * N)) )
  let B ← (( do (undefined_int ()) ) : SailM Int )
  let supports_option_a ← (( do (CPYFOptionA ()) ) : SailM Bool )
  let rprivileged ← (( do
    if (((BitVec.join1 [(BitVec.access options_name 1)]) == 1#1) : Bool)
    then (AArch64_IsUnprivAccessPriv ())
    else (pure ((← readReg PSTATE).EL != EL0)) ) : SailM Bool )
  let wprivileged ← (( do
    if (((BitVec.join1 [(BitVec.access options_name 0)]) == 1#1) : Bool)
    then (AArch64_IsUnprivAccessPriv ())
    else (pure ((← readReg PSTATE).EL != EL0)) ) : SailM Bool )
  let rnontemporal : Bool := ((BitVec.join1 [(BitVec.access options_name 3)]) == 1#1)
  let wnontemporal : Bool := ((BitVec.join1 [(BitVec.access options_name 2)]) == 1#1)
  let raccdesc ← (( do (CreateAccDescMOPS MemOp_LOAD rprivileged rnontemporal) ) : SailM AccessDescriptor )
  let waccdesc ← (( do (CreateAccDescMOPS MemOp_STORE wprivileged wnontemporal) ) : SailM AccessDescriptor )
  let (cpysize, fromaddress, nzcv, stagecpysize, toaddress) ← (( do
    if ((BEq.beq stage MOPSStage_Prologue) : Bool)
    then
      (do
        let cpysize : (BitVec 64) :=
          if (((BitVec.join1 [(BitVec.access cpysize 63)]) == 1#1) : Bool)
          then 0x7FFFFFFFFFFFFFFF#64
          else cpysize
        let (cpysize, fromaddress, nzcv, toaddress) : ((BitVec 64) × (BitVec 64) × (BitVec 4) × (BitVec 64)) :=
          if (supports_option_a : Bool)
          then
            (let nzcv : (BitVec 4) := 0b0000#4
            let toaddress : (BitVec 64) := (toaddress + cpysize)
            let fromaddress : (BitVec 64) := (fromaddress + cpysize)
            let cpysize : (BitVec 64) := ((Zeros (n := 64)) - cpysize)
            (cpysize, fromaddress, nzcv, toaddress))
          else
            (let nzcv : (BitVec 4) := 0b0010#4
            (cpysize, fromaddress, nzcv, toaddress))
        let stagecpysize ← (CPYPreSizeChoice toaddress fromaddress cpysize)
        sail_assert (((BitVec.join1 [(BitVec.access stagecpysize 63)]) == (BitVec.join1 [(BitVec.access cpysize 63)])) || (stagecpysize == (Zeros (n := 64)))) "src/instrs64.sail:8956.78-8956.79"
        if (((BitVec.toInt cpysize) >b 0) : Bool)
        then sail_assert ((BitVec.toInt stagecpysize) ≤b (BitVec.toInt cpysize)) "src/instrs64.sail:8958.54-8958.55"
        else sail_assert ((BitVec.toInt stagecpysize) ≥b (BitVec.toInt cpysize)) "src/instrs64.sail:8960.54-8960.55"
        (pure (cpysize, fromaddress, nzcv, stagecpysize, toaddress)))
    else
      (do
        let zero_size_exceptions ← (( do (MemCpyZeroSizeCheck ()) ) : SailM Bool )
        if ((zero_size_exceptions || (((BitVec.toInt cpysize) != 0) : Bool)) : Bool)
        then
          (do
            if (supports_option_a : Bool)
            then
              (do
                if (((BitVec.join1 [(BitVec.access nzcv 1)]) == 1#1) : Bool)
                then
                  (do
                    let wrong_option : Bool := true
                    let from_epilogue : Bool := (BEq.beq stage MOPSStage_Epilogue)
                    (MismatchedMemCpyException supports_option_a d s n wrong_option from_epilogue options_name))
                else (pure ()))
            else
              (do
                if (((BitVec.join1 [(BitVec.access nzcv 1)]) == 0#1) : Bool)
                then
                  (do
                    let wrong_option : Bool := true
                    let from_epilogue : Bool := (BEq.beq stage MOPSStage_Epilogue)
                    (MismatchedMemCpyException supports_option_a d s n wrong_option from_epilogue options_name))
                else (pure ())))
        else (pure ())
        let postsize ← (( do (CPYPostSizeChoice toaddress fromaddress cpysize) ) : SailM (BitVec 64) )
        sail_assert (((BitVec.join1 [(BitVec.access postsize 63)]) == (BitVec.join1 [(BitVec.access cpysize 63)])) || (((BitVec.toInt postsize) == 0) : Bool)) "src/instrs64.sail:8982.68-8982.69"
        let stagecpysize ← (( do
          if ((BEq.beq stage MOPSStage_Main) : Bool)
          then
            (do
              let stagecpysize : (BitVec 64) := (cpysize - postsize)
              if ((← (MemCpyParametersIllformedM toaddress fromaddress cpysize)) : Bool)
              then
                (do
                  let wrong_option : Bool := false
                  let from_epilogue : Bool := false
                  (MismatchedMemCpyException supports_option_a d s n wrong_option from_epilogue options_name))
              else (pure ())
              (pure stagecpysize))
          else
            (do
              let stagecpysize : (BitVec 64) := postsize
              if ((←((pure (cpysize != postsize)) <||> (do
                   (MemCpyParametersIllformedE toaddress fromaddress cpysize)))) : Bool)
              then
                (do
                  let wrong_option : Bool := false
                  let from_epilogue : Bool := true
                  (MismatchedMemCpyException supports_option_a d s n wrong_option from_epilogue options_name))
              else (pure ())
              (pure stagecpysize)) ) : SailM (BitVec 64) )
        (pure (cpysize, fromaddress, nzcv, stagecpysize, toaddress))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec 4) × (BitVec 64) × (BitVec 64)) )
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleMemCopy ())
  else (pure ())
  let (cpysize, fromaddress, toaddress) ← (( do
    if (supports_option_a : Bool)
    then
      (do
        let (B, cpysize, readdata, stagecpysize) ← (( do
          let mut loop_vars_1 := (B, cpysize, readdata, stagecpysize)
          while (λ (B, cpysize, readdata, stagecpysize) => ((BitVec.toInt stagecpysize) != 0)) loop_vars_1 do
            let (B, cpysize, readdata, stagecpysize) := loop_vars_1
            loop_vars_1 ← do
              let B ← (CPYSizeChoice toaddress fromaddress cpysize)
              sail_assert (B ≤b ((Neg.neg 1) *i (BitVec.toInt stagecpysize))) "src/instrs64.sail:9007.54-9007.55"
              let readdata ← (( do
                let B := B
                sail_assert ((0 ≤b ((B *i 8) -i 1)) && (((B *i 8) -i 1) <b (8 *i N))) "src/instrs64.sail:9010.76-9010.77"
                (pure (Sail.BitVec.updateSubrange readdata ((B *i 8) -i 1) 0 (← (Mem_read (fromaddress + cpysize) B raccdesc)))) ) : SailM (BitVec (8 * N)) )
              let B := B
              sail_assert ((0 ≤b ((B *i 8) -i 1)) && (((B *i 8) -i 1) <b (8 *i N))) "src/instrs64.sail:9015.76-9015.77"
              (Mem_set (toaddress + cpysize) B waccdesc (Sail.BitVec.extractLsb readdata ((B *i 8) -i 1) 0))
              let cpysize : (BitVec 64) := (BitVec.addInt cpysize B)
              let stagecpysize : (BitVec 64) := (BitVec.addInt stagecpysize B)
              if ((bne stage MOPSStage_Prologue) : Bool)
              then (X_set n 64 cpysize)
              else (pure ())
              (pure (B, cpysize, readdata, stagecpysize))
          (pure loop_vars_1) ) : SailM (Int × (BitVec 64) × (BitVec (8 * N)) × (BitVec 64)) )
        (pure (cpysize, fromaddress, toaddress)))
    else
      (do
        let (B, cpysize, fromaddress, readdata, stagecpysize, toaddress) ← (( do
          let mut loop_vars := (B, cpysize, fromaddress, readdata, stagecpysize, toaddress)
          while (λ (B, cpysize, fromaddress, readdata, stagecpysize, toaddress) => ((BitVec.toNat stagecpysize) >b 0)) loop_vars do
            let (B, cpysize, fromaddress, readdata, stagecpysize, toaddress) := loop_vars
            loop_vars ← do
              let B ← (CPYSizeChoice toaddress fromaddress cpysize)
              sail_assert (B ≤b (BitVec.toNat stagecpysize)) "src/instrs64.sail:9028.42-9028.43"
              let readdata ← (( do
                let B := B
                sail_assert ((0 ≤b ((B *i 8) -i 1)) && (((B *i 8) -i 1) <b (8 *i N))) "src/instrs64.sail:9031.76-9031.77"
                (pure (Sail.BitVec.updateSubrange readdata ((B *i 8) -i 1) 0 (← (Mem_read fromaddress B raccdesc)))) ) : SailM (BitVec (8 * N)) )
              let B := B
              sail_assert ((0 ≤b ((B *i 8) -i 1)) && (((B *i 8) -i 1) <b (8 *i N))) "src/instrs64.sail:9036.76-9036.77"
              (Mem_set toaddress B waccdesc (Sail.BitVec.extractLsb readdata ((B *i 8) -i 1) 0))
              let fromaddress : (BitVec 64) := (BitVec.addInt fromaddress B)
              let toaddress : (BitVec 64) := (BitVec.addInt toaddress B)
              let cpysize : (BitVec 64) := (BitVec.subInt cpysize B)
              let stagecpysize : (BitVec 64) := (BitVec.subInt stagecpysize B)
              if ((bne stage MOPSStage_Prologue) : Bool)
              then
                (do
                  (X_set n 64 cpysize)
                  (X_set d 64 toaddress)
                  (X_set s 64 fromaddress))
              else (pure ())
              (pure (B, cpysize, fromaddress, readdata, stagecpysize, toaddress))
          (pure loop_vars) ) : SailM (Int × (BitVec 64) × (BitVec 64) × (BitVec (8 * N)) × (BitVec 64) × (BitVec 64)) )
        (pure (cpysize, fromaddress, toaddress))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec 64)) )
  if ((BEq.beq stage MOPSStage_Prologue) : Bool)
  then
    (do
      (X_set n 64 cpysize)
      (X_set d 64 toaddress)
      (X_set s 64 fromaddress)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure ())

/-- Type quantifiers: k_crc32c : Bool, d : Nat, m : Nat, n : Nat, size : Nat, List.elem size [8, 16, 32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_crc (crc32c : Bool) (d : Nat) (m : Nat) (n : Nat) (size : Nat) : SailM Unit := do
  let acc ← (( do (X_read n 32) ) : SailM (BitVec 32) )
  let val_name ← (( do (X_read m size) ) : SailM (BitVec size) )
  let poly : (BitVec 32) :=
    (integer_subrange
      (if (crc32c : Bool)
      then (BitVec.toNat 0x1EDC6F41#32)
      else (BitVec.toNat 0x04C11DB7#32)) 31 0)
  let tempacc ← (( do (pure ((← (BitReverse acc)) +++ (Zeros (n := size)))) ) : SailM (BitVec (32 + size)) )
  let tempval ← (( do (pure ((← (BitReverse val_name)) +++ (Zeros (n := 32)))) ) : SailM (BitVec (size + 32)) )
  (X_set d 32 (← (BitReverse (← (Poly32Mod2 (tempacc ^^^ tempval) poly)))))

def decode_csinv_aarch64_instrs_integer_conditional_select (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let condition : (BitVec 4) := cond
  let else_inv : Bool := (op == 1#1)
  let else_inc : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_integer_conditional_select condition d datasize else_inc else_inv m n)

def decode_csneg_aarch64_instrs_integer_conditional_select (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let condition : (BitVec 4) := cond
  let else_inv : Bool := (op == 1#1)
  let else_inc : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_integer_conditional_select condition d datasize else_inc else_inv m n)

/-- Type quantifiers: d : Nat, datasize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_unary_ctz (d : Nat) (datasize : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let result ← do (pure (CountLeadingZeroBits (← (BitReverse operand1))))
  (X_set d datasize (integer_subrange result (datasize -i 1) 0))

def execute_aarch64_instrs_system_exceptions_debug_exception (target_level : (BitVec 2)) : SailM Unit := do
  (DCPSInstruction target_level)

def execute_aarch64_instrs_system_barriers_dmb (domain : MBReqDomain) (types : MBReqTypes) : SailM Unit := do
  (DataMemoryBarrier domain types)

def execute_aarch64_instrs_branch_unconditional_dret (_ : Unit) : SailM Unit := do
  (DRPSInstruction ())

/-- Type quantifiers: k_nXS : Bool -/
def execute_aarch64_instrs_system_barriers_dsb (alias' : DSBAlias) (domain : MBReqDomain) (nXS__arg : Bool) (types : MBReqTypes) : SailM Unit := do
  let nXS : Bool := nXS__arg
  match alias' with
  | .DSBAlias_SSBB => (pure (SpeculativeStoreBypassBarrierToVA ()))
  | .DSBAlias_PSSBB => (pure (SpeculativeStoreBypassBarrierToPA ()))
  | .DSBAlias_DSB =>
    (do
      if ((←((HaveTME ()) <&&> (do
           (pure ((← readReg TSTATE).depth >b 0))))) : Bool)
      then (FailTransaction TMFailure_ERR false)
      else (pure ())
      let nXS ← (( do
        if ((←((pure (! nXS)) <&&> (do
             (HaveFeatXS ())))) : Bool)
        then (do (pure ((← readReg PSTATE).EL == EL0)) <||> (do (pure ((← readReg PSTATE).EL == EL1))) <&&> (do (IsHCRXEL2Enabled ())) <&&> (do (pure ((_get_HCRX_EL2_Type_FnXS (← readReg HCRX_EL2)) == 1#1))))
        else (pure nXS) ) : SailM Bool )
      (DataSynchronizationBarrier domain types nXS))

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index : Int, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem idxdsize [64, 128] ∧ List.elem esize [8, 16, 32, 64, 128, 256] ∧ List.elem datasize [8, 16, 32, 64, 128, 256] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Int) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n idxdsize) ) : SailM (BitVec idxdsize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (Elem_read operand index esize) ) : SailM (BitVec esize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e esize element)
    (pure loop_vars) ) : SailM (BitVec datasize) )
  sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:10473.56-10473.57"
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64, 128, 256] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_integer_dup (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:10541.48-10541.49"
  let element ← (( do (X_read n esize) ) : SailM (BitVec esize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e esize element)
    (pure loop_vars) ) : SailM (BitVec datasize) )
  (V_set d datasize result)

/-- Type quantifiers: a : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3_eor3 (a : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Va ← (( do (V_read a 128) ) : SailM (BitVec 128) )
  (V_set d 128 ((Vn ^^^ Vm) ^^^ Va))

/-- Type quantifiers: k_pac : Bool, k_use_key_a : Bool -/
def execute_aarch64_instrs_branch_unconditional_eret (pac : Bool) (use_key_a : Bool) : SailM Unit := do
  (AArch64_CheckForERetTrap pac use_key_a)
  let target ← (( do (ELR_read__1 ()) ) : SailM (BitVec 64) )
  let modifier ← (( do (SP_read ()) ) : SailM (BitVec 64) )
  let auth_then_branch : Bool := true
  let target ← (( do
    if (pac : Bool)
    then
      (do
        if (use_key_a : Bool)
        then (do (AuthIA target modifier auth_then_branch))
        else (do (AuthIB target modifier auth_then_branch)))
    else (pure target) ) : SailM (BitVec 64) )
  (return_exception (Sail.BitVec.extractLsb target 55 0))
  (AArch64_ExceptionReturn target (← (SPSR_read (N := 64))))

/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, position : Int, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_vector_extract (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) (position : Int) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let hi ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let lo ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let concat : (BitVec (datasize * 2)) := (hi +++ lo)
  sail_assert ((0 ≤b position) && (((position +i datasize) -i 1) <b (datasize *i 2))) "src/instrs64.sail:10696.83-10696.84"
  (V_set d datasize (Sail.BitVec.extractLsb concat ((position +i datasize) -i 1) position))

/-- Type quantifiers: d : Nat, datasize : Nat, lsb : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ lsb ∧ lsb ≤ 63 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_ins_ext_extract_immediate (d : Nat) (datasize : Nat) (lsb : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (X_read m datasize) ) : SailM (BitVec datasize) )
  let concat : (BitVec (2 * datasize)) := (operand1 +++ operand2)
  sail_assert (((lsb +i datasize) -i 1) <b (2 *i datasize)) "src/instrs64.sail:10732.59-10732.60"
  let result : (BitVec datasize) := (Sail.BitVec.extractLsb concat ((lsb +i datasize) -i 1) lsb)
  (X_set d datasize result)

/-- Type quantifiers: k_abs : Bool, d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd (abs : Bool) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let diff ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (pure (elements == 1)) <&&> (do (IsMerging fpcr)) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read n 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let (diff, element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (diff, element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (diff, element1, element2, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e esize)
        let element2 ← (Elem_read operand2 e esize)
        let diff ← (FPSub element1 element2 fpcr)
        let result ←
          (Elem_set result e esize
            (← (do
              if (abs : Bool)
              then (FPAbs diff)
              else (pure diff))))
        (pure (diff, element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_arithmetic_unary (d : Nat) (esize : Nat) (fpop : FPUnaryOp) (n : Nat) : SailM Unit := do
  (CheckFPEnabled64 ())
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (pure (bne fpop FPUnaryOp_MOV)) <&&> (do (IsMerging fpcr)) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read d 128)
    else (pure (integer_subrange 0 127 0)) ) : SailM (BitVec 128) )
  let operand ← (( do (V_read n esize) ) : SailM (BitVec esize) )
  let result ← (( do
    match fpop with
    | .FPUnaryOp_MOV => (do (Elem_set result 0 esize operand))
    | .FPUnaryOp_ABS => (do (Elem_set result 0 esize (← (FPAbs operand))))
    | .FPUnaryOp_NEG => (do (Elem_set result 0 esize (← (FPNeg operand))))
    | .FPUnaryOp_SQRT => (do (Elem_set result 0 esize (← (FPSqrt operand fpcr)))) ) : SailM (BitVec 128) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, k_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (neg : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e esize)
        let element ← (( do
          if (neg : Bool)
          then (do (FPNeg element))
          else (do (FPAbs element)) ) : SailM (BitVec esize) )
        let result ← (Elem_set result e esize element)
        (pure (element, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: k_abs : Bool, d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd (abs : Bool) (cmp : CompareOp) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let test_passed ← (( do (undefined_bool ()) ) : SailM Bool )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (pure (elements == 1)) <&&> (do (IsMerging fpcr)) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read m 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let (element1, element2, result, test_passed) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result, test_passed)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result, test_passed) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e esize)
        let element2 ← (Elem_read operand2 e esize)
        let (element1, element2) ← (( do
          if (abs : Bool)
          then
            (do
              let element1 ← (FPAbs element1)
              let element2 ← (FPAbs element2)
              (pure (element1, element2)))
          else (pure (element1, element2)) ) : SailM ((BitVec esize) × (BitVec esize)) )
        let test_passed ← (( do
          match cmp with
          | .CompareOp_EQ => (do (FPCompareEQ element1 element2 fpcr))
          | .CompareOp_GE => (do (FPCompareGE element1 element2 fpcr))
          | .CompareOp_GT => (do (FPCompareGT element1 element2 fpcr))
          | _ => (pure test_passed) ) : SailM Bool )
        let result ←
          (Elem_set result e esize
            (if (test_passed : Bool)
            then (Ones (n := esize))
            else (Zeros (n := esize))))
        (pure (element1, element2, result, test_passed))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec 128) × Bool) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, k_pair : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (pair : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let concat : (BitVec (2 * datasize)) := (operand2 +++ operand1)
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let (element1, element2) ← (( do
          if (pair : Bool)
          then
            (do
              let element1 ← (Elem_read concat (2 *i e) esize)
              let element2 ← (Elem_read concat ((2 *i e) +i 1) esize)
              (pure (element1, element2)))
          else
            (do
              let element1 ← (Elem_read operand1 e esize)
              let element2 ← (Elem_read operand2 e esize)
              (pure (element1, element2))) ) : SailM ((BitVec esize) × (BitVec esize)) )
        let result ← (Elem_set result e esize (← (FPAdd element1 element2 (← (FPCR_read ())))))
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_arithmetic_add_sub (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operand1 ← (( do (V_read n esize) ) : SailM (BitVec esize) )
  let operand2 ← (( do (V_read m esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read n 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let result ← (( do
    if (sub_op : Bool)
    then (do (Elem_set result 0 esize (← (FPSub operand1 operand2 fpcr))))
    else (do (Elem_set result 0 esize (← (FPAdd operand1 operand2 fpcr)))) ) : SailM (BitVec 128) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_reduce_fp16_add_sisd (d : Nat) (datasize : Nat) (esize : Nat) (n : Nat) (op : ReduceOp) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  sail_assert (datasize ≥b esize) "src/instrs64.sail:12626.42-12626.43"
  (V_set d esize (← (Reduce op operand esize)))

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp_complex (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (rot : (BitVec 1)) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element3 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element3, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := ((fdiv_int elements 2) -i 1)
    let mut loop_vars := (element1, element3, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element3, result) := loop_vars
      loop_vars ← do
        let (element1, element3) ← (( do
          match (rot : BitVec 1) with
          | 0 =>
            (do
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:12690.55-12690.56"
              let element1 ← (FPNeg (← (Elem_read operand2 ((e *i 2) +i 1) esize)))
              let element3 ← (Elem_read operand2 (e *i 2) esize)
              (pure (element1, element3)))
          | _ =>
            (do
              let element1 ← (Elem_read operand2 ((e *i 2) +i 1) esize)
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:12696.55-12696.56"
              let element3 ← (FPNeg (← (Elem_read operand2 (e *i 2) esize)))
              (pure (element1, element3))) ) : SailM ((BitVec esize) × (BitVec esize)) )
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:12700.49-12700.50"
        let result ← (Elem_set result (e *i 2) esize (← (FPAdd (← (Elem_read operand1 (e *i 2) esize)) element1 (← (FPCR_read ())))))
        let result ← (Elem_set result ((e *i 2) +i 1) esize (← (FPAdd (← (Elem_read operand1 ((e *i 2) +i 1) esize)) element3 (← (FPCR_read ())))))
        (pure (element1, element3, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: datasize : Nat, m : Nat, n : Nat, k_signal_all_nans : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [16, 32, 64] -/
def execute_aarch64_instrs_float_compare_cond (condition : (BitVec 4)) (datasize : Nat) (flags__arg : (BitVec 4)) (m : Nat) (n : Nat) (signal_all_nans : Bool) : SailM Unit := do
  let flags : (BitVec 4) := flags__arg
  (CheckFPEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let taken : Bool := false
  let (flags, taken) ← (( do
    if ((← (ConditionHolds condition)) : Bool)
    then
      (do
        let flags ← (FPCompare operand1 operand2 signal_all_nans (← (FPCR_read ())))
        let taken : Bool := true
        (pure (flags, taken)))
    else (pure (flags, taken)) ) : SailM ((BitVec 4) × Bool) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb flags 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb flags 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb flags 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb flags 0 0) }
  if ((← readReg SPESampleInFlight) : Bool)
  then
    (do
      let conditional : Bool := true
      (SPESampleAddOpOther conditional taken))
  else (pure ())

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd (comparison : CompareOp) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let zero ← (( do (FPZero 0#1 esize) ) : SailM (BitVec esize) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let test_passed ← (( do (undefined_bool ()) ) : SailM Bool )
  let (element, result, test_passed) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result, test_passed)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result, test_passed) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e esize)
        let test_passed ← (( do
          match comparison with
          | .CompareOp_GT => (do (FPCompareGT element zero (← (FPCR_read ()))))
          | .CompareOp_GE => (do (FPCompareGE element zero (← (FPCR_read ()))))
          | .CompareOp_EQ => (do (FPCompareEQ element zero (← (FPCR_read ()))))
          | .CompareOp_LE => (do (FPCompareGE zero element (← (FPCR_read ()))))
          | .CompareOp_LT => (do (FPCompareGT zero element (← (FPCR_read ())))) ) : SailM Bool )
        let result ←
          (Elem_set result e esize
            (if (test_passed : Bool)
            then (Ones (n := esize))
            else (Zeros (n := esize))))
        (pure (element, result, test_passed))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec datasize) × Bool) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_complex (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (rot : (BitVec 2)) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let operand3 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element3 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element4 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let (element1, element2, element3, element4, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := ((fdiv_int elements 2) -i 1)
    let mut loop_vars := (element1, element2, element3, element4, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, element3, element4, result) := loop_vars
      loop_vars ← do
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
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:13536.55-13536.56"
              let element1 ← (FPNeg (← (Elem_read operand2 ((e *i 2) +i 1) esize)))
              let element2 ← (Elem_read operand1 ((e *i 2) +i 1) esize)
              let element3 ← (Elem_read operand2 (e *i 2) esize)
              let element4 ← (Elem_read operand1 ((e *i 2) +i 1) esize)
              (pure (element1, element2, element3, element4)))
          | 0b10 =>
            (do
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:13543.55-13543.56"
              let element1 ← (FPNeg (← (Elem_read operand2 (e *i 2) esize)))
              let element2 ← (Elem_read operand1 (e *i 2) esize)
              let element3 ← (FPNeg (← (Elem_read operand2 ((e *i 2) +i 1) esize)))
              let element4 ← (Elem_read operand1 (e *i 2) esize)
              (pure (element1, element2, element3, element4)))
          | _ =>
            (do
              let element1 ← (Elem_read operand2 ((e *i 2) +i 1) esize)
              let element2 ← (Elem_read operand1 ((e *i 2) +i 1) esize)
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:13552.55-13552.56"
              let element3 ← (FPNeg (← (Elem_read operand2 (e *i 2) esize)))
              let element4 ← (Elem_read operand1 ((e *i 2) +i 1) esize)
              (pure (element1, element2, element3, element4))) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize)) )
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:13557.49-13557.50"
        let result ← (Elem_set result (e *i 2) esize (← (FPMulAdd (← (Elem_read operand3 (e *i 2) esize)) element2 element1 fpcr)))
        let result ← (Elem_set result ((e *i 2) +i 1) esize (← (FPMulAdd (← (Elem_read operand3 ((e *i 2) +i 1) esize)) element4 element3 fpcr)))
        (pure (element1, element2, element3, element4, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_complex (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (rot : (BitVec 2)) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let operand3 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := ((fdiv_int elements 2) -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
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
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:13623.55-13623.56"
              let element1 ← (FPNeg (← (Elem_read operand2 ((index *i 2) +i 1) esize)))
              let element2 ← (Elem_read operand1 ((e *i 2) +i 1) esize)
              let element3 ← (Elem_read operand2 (index *i 2) esize)
              let element4 ← (Elem_read operand1 ((e *i 2) +i 1) esize)
              (pure (element1, element2, element3, element4)))
          | 0b10 =>
            (do
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:13630.55-13630.56"
              let element1 ← (FPNeg (← (Elem_read operand2 (index *i 2) esize)))
              let element2 ← (Elem_read operand1 (e *i 2) esize)
              let element3 ← (FPNeg (← (Elem_read operand2 ((index *i 2) +i 1) esize)))
              let element4 ← (Elem_read operand1 (e *i 2) esize)
              (pure (element1, element2, element3, element4)))
          | _ =>
            (do
              let element1 ← (Elem_read operand2 ((index *i 2) +i 1) esize)
              let element2 ← (Elem_read operand1 ((e *i 2) +i 1) esize)
              sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:13639.55-13639.56"
              let element3 ← (FPNeg (← (Elem_read operand2 (index *i 2) esize)))
              let element4 ← (Elem_read operand1 ((e *i 2) +i 1) esize)
              (pure (element1, element2, element3, element4))) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize)) )
        let element4 := element4
        let element3 := element3
        let element2 := element2
        let element1 := element1
        sail_assert (((esize == 16) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:13648.49-13648.50"
        let result ← (Elem_set result (e *i 2) esize (← (FPMulAdd (← (Elem_read operand3 (e *i 2) esize)) element2 element1 fpcr)))
        (Elem_set result ((e *i 2) +i 1) esize (← (FPMulAdd (← (Elem_read operand3 ((e *i 2) +i 1) esize)) element4 element3 fpcr)))
    (pure loop_vars) ) : SailM (BitVec datasize) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd (comparison : CompareOp) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let zero ← (( do (FPZero 0#1 esize) ) : SailM (BitVec esize) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let test_passed ← (( do (undefined_bool ()) ) : SailM Bool )
  let (element, result, test_passed) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result, test_passed)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result, test_passed) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e esize)
        let test_passed ← (( do
          match comparison with
          | .CompareOp_GT => (do (FPCompareGT element zero (← (FPCR_read ()))))
          | .CompareOp_GE => (do (FPCompareGE element zero (← (FPCR_read ()))))
          | .CompareOp_EQ => (do (FPCompareEQ element zero (← (FPCR_read ()))))
          | .CompareOp_LE => (do (FPCompareGE zero element (← (FPCR_read ()))))
          | .CompareOp_LT => (do (FPCompareGT zero element (← (FPCR_read ())))) ) : SailM Bool )
        let result ←
          (Elem_set result e esize
            (if (test_passed : Bool)
            then (Ones (n := esize))
            else (Zeros (n := esize))))
        (pure (element, result, test_passed))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec datasize) × Bool) )
  (V_set d datasize result)

/-- Type quantifiers: k_cmp_with_zero : Bool, datasize : Nat, m : Nat, n : Nat, k_signal_all_nans : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [16, 32, 64] -/
def execute_aarch64_instrs_float_compare_uncond (cmp_with_zero : Bool) (datasize : Nat) (m : Nat) (n : Nat) (signal_all_nans : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do
    if (cmp_with_zero : Bool)
    then (FPZero 0#1 datasize)
    else (V_read m datasize) ) : SailM (BitVec datasize) )
  let split_vec ← do (FPCompare operand1 operand2 signal_all_nans (← (FPCR_read ())))
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }

/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_move_fp_select (condition : (BitVec 4)) (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPEnabled64 ())
  let result ← (( do
    if ((← (ConditionHolds condition)) : Bool)
    then (V_read n datasize)
    else (V_read m datasize) ) : SailM (BitVec datasize) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, dstsize : Nat, n : Nat, srcsize : Nat, List.elem srcsize [16, 32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem dstsize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_convert_fp (d : Nat) (dstsize : Nat) (n : Nat) (srcsize : Nat) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operand ← (( do (V_read n srcsize) ) : SailM (BitVec srcsize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read d 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let result ← (Elem_set result 0 dstsize (← (FPConvert__1 operand fpcr dstsize)))
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (pure (elements == 1)) <&&> (do (IsMerging fpcr)) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read d 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e esize)
        let result ← (Elem_set result e esize (← (FPToFixed element 0 is_unsigned fpcr rounding esize)))
        (pure (element, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, fltsize : Nat, intsize : Nat, k_is_unsigned : Bool, n : Nat, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem intsize [32, 64] ∧ List.elem fltsize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_convert_int (d : Nat) (fltsize : Nat) (intsize : Nat) (n : Nat) (op : FPConvOp) (part : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  if ((BEq.beq op FPConvOp_CVT_FtoI_JS) : Bool)
  then (CheckFPAdvSIMDEnabled64 ())
  else (CheckFPEnabled64 ())
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let fsize :=
    if (((BEq.beq op FPConvOp_CVT_ItoF) && merge) : Bool)
    then 128
    else fltsize
  let fltval ← (( do (undefined_bitvector fsize) ) : SailM (BitVec fsize) )
  let intval ← (( do (undefined_bitvector intsize) ) : SailM (BitVec intsize) )
  match op with
  | .FPConvOp_CVT_FtoI =>
    (do
      let fltval ← (( do (V_read n fsize) ) : SailM (BitVec fsize) )
      sail_assert ((((fsize == 16) || (fsize == 32)) || (fsize == 64)) && (((intsize == 16) || (intsize == 32)) || (intsize == 64))) "src/instrs64.sail:14270.80-14270.81"
      let intval ← (( do (FPToFixed fltval 0 is_unsigned fpcr rounding intsize) ) : SailM (BitVec intsize) )
      (X_set d intsize intval))
  | .FPConvOp_CVT_ItoF =>
    (do
      let intval ← (( do (X_read n intsize) ) : SailM (BitVec intsize) )
      let fltval ← (( do
        if (merge : Bool)
        then (V_read d fsize)
        else (pure (Zeros (n := fsize))) ) : SailM (BitVec fsize) )
      sail_assert ((((fltsize == 16) || (fltsize == 32)) || (fltsize == 64)) && (((intsize == 16) || (intsize == 32)) || (intsize == 64))) "src/instrs64.sail:14278.82-14278.83"
      let fltval ← (Elem_set fltval 0 fltsize (← (FixedToFP intval 0 is_unsigned fpcr rounding fltsize)))
      (V_set d fsize fltval))
  | .FPConvOp_MOV_FtoI =>
    (do
      let fltval ← (( do (Vpart_read n part fsize) ) : SailM (BitVec fsize) )
      sail_assert ((fsize ≥b 0) && (intsize ≥b fsize)) "src/instrs64.sail:14284.63-14284.64"
      let intval : (BitVec intsize) := (Sail.BitVec.zeroExtend fltval intsize)
      (X_set d intsize intval))
  | .FPConvOp_MOV_ItoF =>
    (do
      let intval ← (( do (X_read n intsize) ) : SailM (BitVec intsize) )
      sail_assert ((0 ≤b (fsize -i 1)) && ((fsize -i 1) <b intsize)) "src/instrs64.sail:14290.70-14290.71"
      let fltval : (BitVec fsize) := (Sail.BitVec.extractLsb intval (fsize -i 1) 0)
      (Vpart_set d part fsize fltval))
  | .FPConvOp_CVT_FtoI_JS =>
    (do
      let z ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let fltval ← (( do (V_read n fsize) ) : SailM (BitVec fsize) )
      sail_assert (fsize == 64) "src/instrs64.sail:14297.41-14297.42"
      sail_assert (intsize == 32) "src/instrs64.sail:14298.43-14298.44"
      let (intval, z) ← (( do
        let (tup__0, tup__1) ← do (FPToFixedJS fltval fpcr true intsize)
        let intval : (BitVec intsize) := tup__0
        let z : (BitVec 1) := tup__1
        (pure (intval, z)) ) : SailM ((BitVec intsize) × (BitVec 1)) )
      let split_vec := ((0#1 +++ z) +++ 0b00#2)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb split_vec 0 0) }
      (X_set d intsize intval))

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_float_widen (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (Vpart_read n part datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e (2 *i esize) (← (FPConvert__1 (← (Elem_read operand e esize)) (← (FPCR_read ())) (2 *i esize))))
    (pure loop_vars) ) : SailM (BitVec (2 * datasize)) )
  (V_set d (2 *i datasize) result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (pure (elements == 1)) <&&> (do (IsMerging fpcr)) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read d 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e esize)
        let result ← (Elem_set result e esize (← (FPToFixed element 0 is_unsigned fpcr rounding esize)))
        (pure (element, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_float_narrow (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e esize (← (FPConvert__1 (← (Elem_read operand e (2 *i esize))) (← (FPCR_read ())) esize)))
    (pure loop_vars) ) : SailM (BitVec datasize) )
  (Vpart_set d part datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, esize : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ esize = 32 ∧ List.elem elements [1, 2] ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd (d : Nat) (datasize : Nat) (elements : Nat) (esize : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (pure (elements == 1)) <&&> (do (IsMerging fpcr)) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read d 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e esize (← (FPConvert (← (Elem_read operand e (2 *i esize))) fpcr FPRounding_ODD esize)))
    (pure loop_vars) ) : SailM (BitVec 128) )
  if (merge : Bool)
  then (V_set d 128 result)
  else (Vpart_set d part datasize (← (Elem_read result 0 datasize)))

/-- Type quantifiers: d : Nat, fltsize : Nat, fracbits : Nat, intsize : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem intsize [32, 64] ∧ 1 ≤ fracbits ∧ fracbits ≤ 64 ∧ List.elem fltsize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_convert_fix (d : Nat) (fltsize : Nat) (fracbits : Nat) (intsize : Nat) (n : Nat) (op : FPConvOp) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let fsize :=
    if (((BEq.beq op FPConvOp_CVT_ItoF) && merge) : Bool)
    then 128
    else fltsize
  let fltval ← (( do (undefined_bitvector fsize) ) : SailM (BitVec fsize) )
  let intval ← (( do (undefined_bitvector intsize) ) : SailM (BitVec intsize) )
  match op with
  | .FPConvOp_CVT_FtoI =>
    (do
      let fltval ← (( do (V_read n fsize) ) : SailM (BitVec fsize) )
      sail_assert ((((fsize == 16) || (fsize == 32)) || (fsize == 64)) && (((intsize == 16) || (intsize == 32)) || (intsize == 64))) "src/instrs64.sail:16857.80-16857.81"
      let intval ← (( do (FPToFixed fltval fracbits is_unsigned fpcr rounding intsize) ) : SailM (BitVec intsize) )
      (X_set d intsize intval))
  | .FPConvOp_CVT_ItoF =>
    (do
      let intval ← (( do (X_read n intsize) ) : SailM (BitVec intsize) )
      let fltval ← (( do
        if (merge : Bool)
        then (V_read d fsize)
        else (pure (Zeros (n := fsize))) ) : SailM (BitVec fsize) )
      let fltval ← (Elem_set fltval 0 fltsize (← (FixedToFP intval fracbits is_unsigned fpcr rounding fltsize)))
      (V_set d fsize fltval))
  | _ => (pure ())

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, fracbits : Int, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_conv_float_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (fracbits : Int) (n : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (pure (elements == 1)) <&&> (do (IsMerging fpcr)) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read d 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e esize)
        let result ← (Elem_set result e esize (← (FPToFixed element fracbits is_unsigned fpcr rounding esize)))
        (pure (element, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16 (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e esize)
        let element2 ← (Elem_read operand2 e esize)
        let result ← (Elem_set result e esize (← (FPDiv element1 element2 (← (FPCR_read ())))))
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_arithmetic_div (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operand1 ← (( do (V_read n esize) ) : SailM (BitVec esize) )
  let operand2 ← (( do (V_read m esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read n 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let result ← (Elem_set result 0 esize (← (FPDiv operand1 operand2 (← (FPCR_read ())))))
  (V_set d 128 result)

/-- Type quantifiers: a : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_opa_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 -/
def execute_aarch64_instrs_float_arithmetic_mul_add_sub (a : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (opa_neg : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operanda ← (( do (V_read a esize) ) : SailM (BitVec esize) )
  let operand1 ← (( do (V_read n esize) ) : SailM (BitVec esize) )
  let operand2 ← (( do (V_read m esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read a 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let operanda ← (( do
    if (opa_neg : Bool)
    then (do (FPNeg operanda))
    else (pure operanda) ) : SailM (BitVec esize) )
  let operand1 ← (( do
    if (op1_neg : Bool)
    then (do (FPNeg operand1))
    else (pure operand1) ) : SailM (BitVec esize) )
  let result ← (Elem_set result 0 esize (← (FPMulAdd operanda operand1 operand2 fpcr)))
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_arithmetic_max_min (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (operation : FPMaxMinOp) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operand1 ← (( do (V_read n esize) ) : SailM (BitVec esize) )
  let operand2 ← (( do (V_read m esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read n 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let result ← (( do
    match operation with
    | .FPMaxMinOp_MAX => (do (Elem_set result 0 esize (← (FPMax operand1 operand2 fpcr))))
    | .FPMaxMinOp_MIN => (do (Elem_set result 0 esize (← (FPMin operand1 operand2 fpcr))))
    | .FPMaxMinOp_MAXNUM => (do (Elem_set result 0 esize (← (FPMaxNum operand1 operand2 fpcr))))
    | .FPMaxMinOp_MINNUM => (do (Elem_set result 0 esize (← (FPMinNum operand1 operand2 fpcr)))) ) : SailM (BitVec 128) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, k_minimum : Bool, n : Nat, k_pair : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (minimum : Bool) (n : Nat) (pair : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let concat : (BitVec (2 * datasize)) := (operand2 +++ operand1)
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let (element1, element2) ← (( do
          if (pair : Bool)
          then
            (do
              let element1 ← (Elem_read concat (2 *i e) esize)
              let element2 ← (Elem_read concat ((2 *i e) +i 1) esize)
              (pure (element1, element2)))
          else
            (do
              let element1 ← (Elem_read operand1 e esize)
              let element2 ← (Elem_read operand2 e esize)
              (pure (element1, element2))) ) : SailM ((BitVec esize) × (BitVec esize)) )
        let result ← (( do
          if (minimum : Bool)
          then (do (Elem_set result e esize (← (FPMin element1 element2 (← (FPCR_read ()))))))
          else (do (Elem_set result e esize (← (FPMax element1 element2 (← (FPCR_read ())))))) ) : SailM (BitVec datasize) )
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, k_minimum : Bool, n : Nat, k_pair : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (minimum : Bool) (n : Nat) (pair : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let concat : (BitVec (2 * datasize)) := (operand2 +++ operand1)
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let (element1, element2) ← (( do
          if (pair : Bool)
          then
            (do
              let element1 ← (Elem_read concat (2 *i e) esize)
              let element2 ← (Elem_read concat ((2 *i e) +i 1) esize)
              (pure (element1, element2)))
          else
            (do
              let element1 ← (Elem_read operand1 e esize)
              let element2 ← (Elem_read operand2 e esize)
              (pure (element1, element2))) ) : SailM ((BitVec esize) × (BitVec esize)) )
        let result ← (( do
          if (minimum : Bool)
          then (do (Elem_set result e esize (← (FPMinNum element1 element2 (← (FPCR_read ()))))))
          else (do (Elem_set result e esize (← (FPMaxNum element1 element2 (← (FPCR_read ())))))) ) : SailM (BitVec datasize) )
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_reduce_fp16_maxnm_sisd (d : Nat) (datasize : Nat) (esize : Nat) (n : Nat) (op : ReduceOp) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let altfp : Bool := false
  sail_assert (datasize ≥b esize) "src/instrs64.sail:18425.42-18425.43"
  (V_set d esize (← (Reduce__1 op operand esize altfp)))

/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_reduce_fp16_maxnm_simd (d : Nat) (datasize : Nat) (esize : Nat) (n : Nat) (op : ReduceOp) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let altfp : Bool := false
  (V_set d esize (← (Reduce__1 op operand esize altfp)))

/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_reduce_fp16_max_sisd (d : Nat) (datasize : Nat) (esize : Nat) (n : Nat) (op : ReduceOp) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  sail_assert (datasize ≥b esize) "src/instrs64.sail:18641.42-18641.43"
  (V_set d esize (← (Reduce op operand esize)))

/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_reduce_fp16_max_simd (d : Nat) (datasize : Nat) (esize : Nat) (n : Nat) (op : ReduceOp) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  (V_set d esize (← (Reduce op operand esize)))

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem idxdsize [64, 128] ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m idxdsize) ) : SailM (BitVec idxdsize) )
  let operand3 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (Elem_read operand2 index esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (pure (elements == 1)) <&&> (do (IsMerging fpcr)) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read d 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let (element1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e esize)
        let element1 ← (( do
          if (sub_op : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec esize) )
        let result ← (Elem_set result e esize (← (FPMulAdd (← (Elem_read operand3 e esize)) element1 element2 fpcr)))
        (pure (element1, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let operand3 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e esize)
        let element2 ← (Elem_read operand2 e esize)
        let element1 ← (( do
          if (sub_op : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec esize) )
        let result ← (Elem_set result e esize (← (FPMulAdd (← (Elem_read operand3 e esize)) element1 element2 (← (FPCR_read ())))))
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, index : Nat, m : Nat, n : Nat, part : Nat, k_sub_op : Bool, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_lower (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (part : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (Vpart_read n part (Int.ediv datasize 2)) ) : SailM (BitVec (datasize / 2)) )
  let operand2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let operand3 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
  let element2 ← (( do (Elem_read operand2 index (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
  let (element1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e (Int.ediv esize 2))
        let element1 ← (( do
          if (sub_op : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec (esize / 2)) )
        let result ← (Elem_set result e esize (← (FPMulAddH (← (Elem_read operand3 e esize)) element1 element2 (← (FPCR_read ())))))
        (pure (element1, result))
    (pure loop_vars) ) : SailM ((BitVec (esize / 2)) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, part : Nat, k_sub_op : Bool, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 32 ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (Vpart_read n part (Int.ediv datasize 2)) ) : SailM (BitVec (datasize / 2)) )
  let operand2 ← (( do (Vpart_read m part (Int.ediv datasize 2)) ) : SailM (BitVec (datasize / 2)) )
  let operand3 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
  let element2 ← (( do (undefined_bitvector (Int.ediv esize 2)) ) : SailM (BitVec (esize / 2)) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e (Int.ediv esize 2))
        let element2 ← (Elem_read operand2 e (Int.ediv esize 2))
        let element1 ← (( do
          if (sub_op : Bool)
          then (do (FPNeg element1))
          else (pure element1) ) : SailM (BitVec (esize / 2)) )
        let result ← (Elem_set result e esize (← (FPMulAddH (← (Elem_read operand3 e esize)) element1 element2 (← (FPCR_read ())))))
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec (esize / 2)) × (BitVec (esize / 2)) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: datasize : Nat, rd : Nat, 0 ≤ rd ∧ rd ≤ 31 ∧ List.elem datasize [64, 128] -/
def execute_aarch64_instrs_vector_fp16_movi (datasize : Nat) (imm : (BitVec datasize)) (rd : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  (V_set rd datasize imm)

/-- Type quantifiers: d : Nat, datasize : Nat, List.elem datasize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_move_fp_imm (d : Nat) (datasize : Nat) (imm : (BitVec datasize)) : SailM Unit := do
  (CheckFPEnabled64 ())
  (V_set d datasize imm)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e esize)
        let element2 ← (Elem_read operand2 e esize)
        let result ← (Elem_set result e esize (← (FPMul element1 element2 (← (FPCR_read ())))))
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, esize : Nat, m : Nat, n : Nat, k_negated : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_arithmetic_mul_product (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (negated : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operand1 ← (( do (V_read n esize) ) : SailM (BitVec esize) )
  let operand2 ← (( do (V_read m esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read n 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let product ← (( do (FPMul operand1 operand2 fpcr) ) : SailM (BitVec esize) )
  let product ← (( do
    if (negated : Bool)
    then (do (FPNeg product))
    else (pure product) ) : SailM (BitVec esize) )
  let result ← (Elem_set result 0 esize product)
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index : Nat, m : Nat, k_mulx_op : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem idxdsize [64, 128] ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (mulx_op : Bool) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m idxdsize) ) : SailM (BitVec idxdsize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (Elem_read operand2 index esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (pure (elements == 1)) <&&> (do (IsMerging fpcr)) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read n 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let (element1, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e esize)
        let result ← (( do
          if (mulx_op : Bool)
          then (do (Elem_set result e esize (← (FPMulX element1 element2 fpcr))))
          else (do (Elem_set result e esize (← (FPMul element1 element2 fpcr)))) ) : SailM (BitVec 128) )
        (pure (element1, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  if ((elements == 1) : Bool)
  then (CheckFPEnabled64 ())
  else (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (pure (elements == 1)) <&&> (do (IsMerging fpcr)) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read n 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e esize)
        let element2 ← (Elem_read operand2 e esize)
        let result ← (Elem_set result e esize (← (FPMulX element1 element2 fpcr)))
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  if ((elements == 1) : Bool)
  then (CheckFPEnabled64 ())
  else (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (pure (elements == 1)) <&&> (do (IsMerging fpcr)) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read d 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e esize)
        let result ← (Elem_set result e esize (← (FPRecipEstimate element (← (FPCR_read ())))))
        (pure (element, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  if ((elements == 1) : Bool)
  then (CheckFPEnabled64 ())
  else (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (pure (elements == 1)) <&&> (do (IsMerging fpcr)) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read n 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e esize)
        let element2 ← (Elem_read operand2 e esize)
        let result ← (Elem_set result e esize (← (FPRecipStepFused element1 element2)))
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16 (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operand ← (( do (V_read n esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read d 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let result ← (Elem_set result 0 esize (← (FPRecpX operand fpcr)))
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, intsize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem intsize [32, 64] ∧ List.elem esize [32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (intsize : Nat) (n : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e esize)
        let result ← (Elem_set result e esize (← (FPRoundIntN element (← (FPCR_read ())) rounding intsize)))
        (pure (element, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, esize : Nat, intsize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem intsize [32, 64] ∧ List.elem esize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_arithmetic_round_frint_32_64 (d : Nat) (esize : Nat) (intsize : Nat) (n : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckFPEnabled64 ())
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read d 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let operand ← (( do (V_read n esize) ) : SailM (BitVec esize) )
  let result ← (Elem_set result 0 esize (← (FPRoundIntN operand fpcr rounding intsize)))
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_exact : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_fp16_round (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (exact : Bool) (n : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e esize)
        let result ← (Elem_set result e esize (← (FPRoundInt element (← (FPCR_read ())) rounding exact)))
        (pure (element, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, esize : Nat, k_exact : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_arithmetic_round_frint (d : Nat) (esize : Nat) (exact : Bool) (n : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckFPEnabled64 ())
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read d 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let operand ← (( do (V_read n esize) ) : SailM (BitVec esize) )
  let result ← (Elem_set result 0 esize (← (FPRoundInt operand fpcr rounding exact)))
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  if ((elements == 1) : Bool)
  then (CheckFPEnabled64 ())
  else (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (pure (elements == 1)) <&&> (do (IsMerging fpcr)) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read d 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e esize)
        let result ← (Elem_set result e esize (← (FPRSqrtEstimate element fpcr)))
        (pure (element, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  if ((elements == 1) : Bool)
  then (CheckFPEnabled64 ())
  else (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (pure (elements == 1)) <&&> (do (IsMerging fpcr)) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read n 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e esize)
        let element2 ← (Elem_read operand2 e esize)
        let result ← (Elem_set result e esize (← (FPRSqrtStepFused element1 element2)))
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16 (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e esize)
        let result ← (Elem_set result e esize (← (FPSqrt element (← (FPCR_read ())))))
        (pure (element, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: k_abs : Bool, d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd (abs : Bool) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let diff ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let (diff, element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (diff, element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (diff, element1, element2, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e esize)
        let element2 ← (Elem_read operand2 e esize)
        let diff ← (FPSub element1 element2 fpcr)
        let result ←
          (Elem_set result e esize
            (← (do
              if (abs : Bool)
              then (FPAbs diff)
              else (pure diff))))
        (pure (diff, element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: k_is_gcssttr : Bool, n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_gcs_general_register (is_gcssttr : Bool) (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let effective_el ← (( do
    if ((←((pure (! is_gcssttr)) <||> (do
         (AArch64_IsUnprivAccessPriv ())))) : Bool)
    then (pure (← readReg PSTATE).EL)
    else (pure EL0) ) : SailM (BitVec 2) )
  if ((effective_el == (← readReg PSTATE).EL) : Bool)
  then (CheckGCSSTREnabled ())
  else (pure ())
  let accdesc ← (( do (CreateAccDescGCS effective_el MemOp_STORE) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let data ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  (Mem_set address 8 accdesc data)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcinserttagmask (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let address ← (( do
    if ((n == 31) : Bool)
    then (SP_read ())
    else (X_read n 64) ) : SailM (BitVec 64) )
  let mask ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let tag : (BitVec 4) := (AArch64_AllocationTagFromAddress address)
  let mask : (BitVec 64) := (BitVec.update mask (BitVec.toNat tag) (Bit 1#1))
  (X_set d 64 mask)

def execute_aarch64_instrs_system_exceptions_debug_halt (_ : Unit) : SailM Unit := do
  let is_async : Bool := false
  (Halt__1 DebugHalt_HaltInstruction is_async)

def execute_aarch64_instrs_system_exceptions_runtime_hvc (imm : (BitVec 16)) : SailM Unit := do
  if ((←((pure (! (HaveEL EL2))) <||> (do
       (pure ((← readReg PSTATE).EL == EL0))) <||> (do
       (pure ((← readReg PSTATE).EL == EL1)) <&&> (do
         (pure (! (← (EL2Enabled ())))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let hvc_enable ← (( do
    if ((HaveEL EL3) : Bool)
    then (pure (_get_SCR_EL3_Type_HCE (← readReg SCR_EL3)))
    else (pure (Complement.complement (_get_HCR_EL2_Type_HCD (← readReg HCR_EL2)))) ) : SailM (BitVec 1) )
  if ((hvc_enable == 0#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (AArch64_CallHypervisor imm)

/-- Type quantifiers: d : Nat, dst_index : Int, esize : Nat, idxdsize : Nat, n : Nat, src_index : Int, 0 ≤ n ∧ n ≤ 31 ∧ List.elem idxdsize [64, 128] ∧ List.elem esize [8, 16, 32, 64, 128, 256] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_vector_insert (d : Nat) (dst_index : Int) (esize : Nat) (idxdsize : Nat) (n : Nat) (src_index : Int) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n idxdsize) ) : SailM (BitVec idxdsize) )
  let result ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let result ← (Elem_set result dst_index esize (← (Elem_read operand src_index esize)))
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, index : Int, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64, 128, 256] ∧ datasize = 128 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_integer_insert (d : Nat) (datasize : Nat) (esize : Nat) (index : Int) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:22661.48-22661.49"
  let element ← (( do (X_read n esize) ) : SailM (BitVec esize) )
  let result ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (Elem_set result index esize element)
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcinsertrandomtag (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let operand ← (( do
    if ((n == 31) : Bool)
    then (SP_read ())
    else (X_read n 64) ) : SailM (BitVec 64) )
  let exclude_reg ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let exclude ← (( do (pure ((Sail.BitVec.extractLsb exclude_reg 15 0) ||| (_get_GCR_EL1_Type_Exclude (← readReg GCR_EL1)))) ) : SailM (BitVec 16) )
  let rtag ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let rtag ← (( do
    if ((← (AArch64_AllocationTagAccessIsEnabled (← readReg PSTATE).EL)) : Bool)
    then
      (do
        if (((_get_GCR_EL1_Type_RRND (← readReg GCR_EL1)) == 1#1) : Bool)
        then
          (do
            if ((IsOnes exclude) : Bool)
            then (pure 0b0000#4)
            else (do (ChooseRandomNonExcludedTag exclude)))
        else
          (do
            let start_tag ← (( do (pure (_get_RGSR_EL1_Type_TAG (← readReg RGSR_EL1))) ) : SailM (BitVec 4) )
            let offset ← (( do (AArch64_RandomTag ()) ) : SailM (BitVec 4) )
            let rtag : (BitVec 4) := (AArch64_ChooseNonExcludedTag start_tag offset exclude)
            writeReg RGSR_EL1 (Sail.BitVec.updateSubrange (← readReg RGSR_EL1) 3 0 rtag)
            (pure rtag)))
    else (pure 0b0000#4) ) : SailM (BitVec 4) )
  let result ← (( do (AArch64_AddressWithAllocationTag operand rtag) ) : SailM (BitVec 64) )
  if ((d == 31) : Bool)
  then (SP_set result)
  else (X_set d 64 result)

def execute_aarch64_instrs_system_barriers_isb (_ : Unit) : SailM Unit := do
  (InstructionSynchronizationBarrier ())
  if ((←((HaveBRBExt ()) <&&> (do
       (BRBEBranchOnISB ())))) : Bool)
  then (BRBEISB ())
  else (pure ())
  if ((← (HaveStatisticalProfiling ())) : Bool)
  then (SPEISB ())
  else (pure ())

/-- Type quantifiers: datasize : Nat, esize : Nat, index : Int, m : Int, n : Nat, k_nontemporal : Bool, k_replicate : Bool, selem : Nat, t__arg : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ List.elem selem [1, 2, 3, 4] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] -/
def execute_aarch64_instrs_memory_vector_single_no_wb (datasize : Nat) (esize : Nat) (index : Int) (m : Int) (memop : MemOp) (n : Nat) (nontemporal : Bool) (replicate : Bool) (selem : Nat) (t__arg : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  let t : Int := t__arg
  (CheckFPAdvSIMDEnabled64 ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let rval ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let ebytes := (Int.ediv esize 8)
  let accdesc ← (( do (CreateAccDescASIMD memop nontemporal tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let offs : (BitVec 64) := (Zeros (n := 64))
  let offs ← (( do
    if (replicate : Bool)
    then
      (do
        let (element, offs, t) ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (selem -i 1)
          let mut loop_vars_1 := (element, offs, t)
          for s in [loop_s_lower:loop_s_upper:1]i do
            let (element, offs, t) := loop_vars_1
            loop_vars_1 ← do
              let element ← (Mem_read (address + offs) ebytes accdesc)
              (V_set t datasize (BitVec.replicateBits element (Int.ediv datasize esize)))
              let offs : (BitVec 64) := (BitVec.addInt offs ebytes)
              let t : Int := (fmod_int (t +i 1) 32)
              (pure (element, offs, t))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec 64) × Int) )
        (pure offs))
    else
      (do
        let (offs, rval, t) ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (selem -i 1)
          let mut loop_vars := (offs, rval, t)
          for s in [loop_s_lower:loop_s_upper:1]i do
            let (offs, rval, t) := loop_vars
            loop_vars ← do
              let rval ← (V_read t 128)
              let rval ← (( do
                if ((BEq.beq memop MemOp_LOAD) : Bool)
                then
                  (do
                    let rval ← (Elem_set rval index esize (← (Mem_read (address + offs) ebytes accdesc)))
                    (V_set t 128 rval)
                    (pure rval))
                else
                  (do
                    (Mem_set (address + offs) ebytes accdesc (← (Elem_read rval index esize)))
                    (pure rval)) ) : SailM (BitVec 128) )
              let offs : (BitVec 64) := (BitVec.addInt offs ebytes)
              let t : Int := (fmod_int (t +i 1) 32)
              (pure (offs, rval, t))
          (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 128) × Int) )
        (pure offs)) ) : SailM (BitVec 64) )
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleSIMDFPLoadStore ())
  else (pure ())
  if (wback : Bool)
  then
    (do
      let offs ← (( do
        if ((m != 31) : Bool)
        then (do (X_read m 64))
        else (pure offs) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then (SP_set (address + offs))
      else (X_set n 64 (address + offs)))
  else (pure ())

/-- Type quantifiers: datasize : Nat, elements : Int, esize : Nat, m : Int, n : Nat, k_nontemporal : Bool, rpt : Nat, selem : Nat, t : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t ∧ t ≤ 31 ∧ List.elem selem [1, 2, 3, 4] ∧ List.elem rpt [1, 2, 3, 4] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] -/
def execute_aarch64_instrs_memory_vector_multiple_no_wb (datasize : Nat) (elements : Int) (esize : Nat) (m : Int) (memop : MemOp) (n : Nat) (nontemporal : Bool) (rpt : Nat) (selem : Nat) (t : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let rval ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let tt ← (( do (undefined_int ()) ) : SailM Int )
  let ebytes := (Int.ediv esize 8)
  let accdesc ← (( do (CreateAccDescASIMD memop nontemporal tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let offs : (BitVec 64) := (Zeros (n := 64))
  let (offs, rval, tt) ← (( do
    let loop_r_lower := 0
    let loop_r_upper := (rpt -i 1)
    let mut loop_vars := (offs, rval, tt)
    for r in [loop_r_lower:loop_r_upper:1]i do
      let (offs, rval, tt) := loop_vars
      loop_vars ← do
        let (offs, rval, tt) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements -i 1)
          let mut loop_vars_1 := (offs, rval, tt)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (offs, rval, tt) := loop_vars_1
            loop_vars_1 ← do
              let tt : Int := (Nat.mod (t +i r) 32)
              let (offs, rval, tt) ← (( do
                let loop_s_lower := 0
                let loop_s_upper := (selem -i 1)
                let mut loop_vars_2 := (offs, rval, tt)
                for s in [loop_s_lower:loop_s_upper:1]i do
                  let (offs, rval, tt) := loop_vars_2
                  loop_vars_2 ← do
                    let rval ← (( do
                      let tt := tt
                      (V_read tt datasize) ) : SailM (BitVec datasize) )
                    let rval ← (( do
                      let tt := tt
                      if ((BEq.beq memop MemOp_LOAD) : Bool)
                      then
                        (do
                          let rval ← (Elem_set rval e esize (← (Mem_read (address + offs) ebytes accdesc)))
                          (V_set tt datasize rval)
                          (pure rval))
                      else
                        (do
                          (Mem_set (address + offs) ebytes accdesc (← (Elem_read rval e esize)))
                          (pure rval)) ) : SailM (BitVec datasize) )
                    let offs : (BitVec 64) := (BitVec.addInt offs ebytes)
                    let tt : Int := (fmod_int (tt +i 1) 32)
                    (pure (offs, rval, tt))
                (pure loop_vars_2) ) : SailM ((BitVec 64) × (BitVec datasize) × Int) )
              (pure (offs, rval, tt))
          (pure loop_vars_1) ) : SailM ((BitVec 64) × (BitVec datasize) × Int) )
        (pure (offs, rval, tt))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec datasize) × Int) )
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleSIMDFPLoadStore ())
  else (pure ())
  if (wback : Bool)
  then
    (do
      let offs ← (( do
        if ((m != 31) : Bool)
        then (do (X_read m 64))
        else (pure offs) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then (SP_set (address + offs))
      else (X_set n 64 (address + offs)))
  else (pure ())

/-- Type quantifiers: n : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_atomicops_ld_acc (lst : (BitVec 2)) (memop : MemOp) (n : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  (CheckLDST64BEnabled ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let value_name ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescLS64 memop tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let _ : Unit := (SetLoadStoreType lst)
  let _ : Unit := (AArch64_SetLSInstructionSyndrome 64 false t true false)
  let data ← (( do (MemLoad64B address accdesc) ) : SailM (BitVec 512) )
  let value_name ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 7
    let mut loop_vars := value_name
    for i in [loop_i_lower:loop_i_upper:1]i do
      let value_name := loop_vars
      loop_vars ← do
        let value_name : (BitVec 64) := (Sail.BitVec.extractLsb data (63 +i (64 *i i)) (64 *i i))
        let value_name ← (( do
          if ((← (BigEndian accdesc.acctype)) : Bool)
          then (pure (reverse_endianness value_name))
          else (pure value_name) ) : SailM (BitVec 64) )
        (X_set (t +i i) 64 value_name)
        (pure value_name)
    (pure loop_vars) ) : SailM (BitVec 64) )
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleGeneralPurposeLoadStore ())
  else (pure ())

/-- Type quantifiers: k_acquire : Bool, datasize : Nat, k_is_load : Bool, n : Nat, regsize : Nat, k_release : Bool, s : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_atomicops_ld (acquire : Bool) (datasize : Nat) (is_load : Bool) (n : Nat) (op : MemAtomicOp) (regsize : Nat) (release : Bool) (s : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescAtomicOp op acquire release tagchecked) ) : SailM AccessDescriptor )
  let value_name ← (( do (X_read s datasize) ) : SailM (BitVec datasize) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let comparevalue ← (( do (__UNKNOWN_bits datasize) ) : SailM (BitVec datasize) )
  let data ← (( do (MemAtomic address comparevalue value_name accdesc) ) : SailM (BitVec datasize) )
  if ((t != 31) : Bool)
  then
    (do
      sail_assert ((datasize ≥b 0) && (regsize ≥b datasize)) "src/instrs64.sail:25715.67-25715.68"
      (X_set t regsize (Sail.BitVec.zeroExtend data regsize)))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then
    (do
      let ar : (BitVec 1) :=
        if ((acquire || release) : Bool)
        then 1#1
        else 0#1
      let excl : (BitVec 1) := 0#1
      let at' : (BitVec 1) := 1#1
      (SPESampleExtendedLoadStore ar excl at' is_load))
  else (pure ())

/-- Type quantifiers: datasize : Nat, esize : Nat, index : Int, m : Int, n : Nat, k_replicate : Bool, selem : Nat, t__arg : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t__arg ∧ t__arg ≤ 31 ∧ List.elem selem [1, 2, 3, 4] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] -/
def execute_aarch64_instrs_memory_vector_single_no_wb_ordered (datasize : Nat) (esize : Nat) (index : Int) (m : Int) (memop : MemOp) (n : Nat) (replicate : Bool) (selem : Nat) (t__arg : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  let t : Int := t__arg
  (CheckFPAdvSIMDEnabled64 ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let rval ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let ebytes := (Int.ediv esize 8)
  let accdesc ← (( do (CreateAccDescASIMDAcqRel memop tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let offs : (BitVec 64) := (Zeros (n := 64))
  let offs ← (( do
    if (replicate : Bool)
    then
      (do
        let (element, offs, t) ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (selem -i 1)
          let mut loop_vars_1 := (element, offs, t)
          for s in [loop_s_lower:loop_s_upper:1]i do
            let (element, offs, t) := loop_vars_1
            loop_vars_1 ← do
              let element ← (Mem_read (address + offs) ebytes accdesc)
              (V_set t datasize (BitVec.replicateBits element (Int.ediv datasize esize)))
              let offs : (BitVec 64) := (BitVec.addInt offs ebytes)
              let t : Int := (fmod_int (t +i 1) 32)
              (pure (element, offs, t))
          (pure loop_vars_1) ) : SailM ((BitVec esize) × (BitVec 64) × Int) )
        (pure offs))
    else
      (do
        let (offs, rval, t) ← (( do
          let loop_s_lower := 0
          let loop_s_upper := (selem -i 1)
          let mut loop_vars := (offs, rval, t)
          for s in [loop_s_lower:loop_s_upper:1]i do
            let (offs, rval, t) := loop_vars
            loop_vars ← do
              let rval ← (V_read t 128)
              let rval ← (( do
                if ((BEq.beq memop MemOp_LOAD) : Bool)
                then
                  (do
                    let rval ← (Elem_set rval index esize (← (Mem_read (address + offs) ebytes accdesc)))
                    (V_set t 128 rval)
                    (pure rval))
                else
                  (do
                    (Mem_set (address + offs) ebytes accdesc (← (Elem_read rval index esize)))
                    (pure rval)) ) : SailM (BitVec 128) )
              let offs : (BitVec 64) := (BitVec.addInt offs ebytes)
              let t : Int := (fmod_int (t +i 1) 32)
              (pure (offs, rval, t))
          (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 128) × Int) )
        (pure offs)) ) : SailM (BitVec 64) )
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleSIMDFPLoadStore ())
  else (pure ())
  if (wback : Bool)
  then
    (do
      let offs ← (( do
        if ((m != 31) : Bool)
        then (do (X_read m 64))
        else (pure offs) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then (SP_set (address + offs))
      else (X_set n 64 (address + offs)))
  else (pure ())

/-- Type quantifiers: datasize : Nat, n : Nat, offset : Nat, regsize : Nat, t : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback : Bool, 0 ≤ t ∧ t ≤ 31 ∧ List.elem regsize [32, 64] ∧ List.elem offset [0, 1, 2, 4, 8] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_ordered_rcpc (datasize : Nat) (n : Nat) (offset : Nat) (regsize : Nat) (t : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let dbytes := (Int.ediv datasize 8)
  let accdesc ← (( do (CreateAccDescLDAcqPC tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let data ← (( do (Mem_read address dbytes accdesc) ) : SailM (BitVec datasize) )
  sail_assert (regsize ≥b datasize) "src/instrs64.sail:27327.44-27327.45"
  (X_set t regsize (Sail.BitVec.zeroExtend data regsize))
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then (do (__UNKNOWN_bits 64))
        else (pure (BitVec.addInt address offset)) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then
    (do
      let ar : (BitVec 1) := 1#1
      let excl : (BitVec 1) := 0#1
      let at' : (BitVec 1) := 0#1
      let is_load : Bool := true
      (SPESampleExtendedLoadStore ar excl at' is_load))
  else (pure ())

/-- Type quantifiers: datasize : Nat, k_is_signed : Bool, n : Nat, k_postindex : Bool, regsize : Nat, k_rt_unknown : Bool, t : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback : Bool, 0 ≤ t ∧ t ≤ 31 ∧ List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (datasize : Nat) (memop : MemOp) (n : Nat) (offset : (BitVec 64)) (postindex : Bool) (regsize : Nat) (rt_unknown : Bool) (is_signed : Bool) (t : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let accdesc ← (( do (undefined_AccessDescriptor ()) ) : SailM AccessDescriptor )
  let accdesc ← (( do
    if ((BEq.beq memop MemOp_LOAD) : Bool)
    then (do (CreateAccDescLDAcqPC tagchecked))
    else
      (do
        if ((BEq.beq memop MemOp_STORE) : Bool)
        then (do (CreateAccDescAcqRel memop tagchecked))
        else (pure accdesc)) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((bne memop MemOp_PREFETCH) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      let data ← (( do
        if (rt_unknown : Bool)
        then (do (__UNKNOWN_bits datasize))
        else (do (X_read t datasize)) ) : SailM (BitVec datasize) )
      let _ : Unit :=
        if ((! wback) : Bool)
        then (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) false t (regsize == 64) false)
        else ()
      (Mem_set address (Int.ediv datasize 8) accdesc data))
  | .MemOp_LOAD =>
    (do
      let _ : Unit :=
        if ((! wback) : Bool)
        then (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) is_signed t (regsize == 64) false)
        else ()
      let data ← (( do (Mem_read address (Int.ediv datasize 8) accdesc) ) : SailM (BitVec datasize) )
      if (is_signed : Bool)
      then
        (do
          sail_assert ((datasize >b 0) && (regsize ≥b datasize)) "src/instrs64.sail:27521.72-27521.73"
          (X_set t regsize (sign_extend data regsize)))
      else
        (do
          sail_assert ((datasize ≥b 0) && (regsize ≥b datasize)) "src/instrs64.sail:27524.73-27524.74"
          (X_set t regsize (Sail.BitVec.zeroExtend data regsize))))
  | .MemOp_PREFETCH => (Prefetch address (integer_subrange t 4 0))
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then (do (__UNKNOWN_bits 64))
        else
          (if (postindex : Bool)
          then (pure (address + offset))
          else (pure address)) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleGeneralPurposeLoadStore ())
  else (pure ())

/-- Type quantifiers: datasize : Nat, n : Nat, k_postindex : Bool, t : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64, 128, 256, 512, 1024] -/
def execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered (datasize : Nat) (memop : MemOp) (n : Nat) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let accdesc ← (( do (CreateAccDescASIMDAcqRel memop tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:28335.62-28335.63"
      let data ← (( do (V_read t datasize) ) : SailM (BitVec datasize) )
      (Mem_set address (Int.ediv datasize 8) accdesc data))
  | .MemOp_LOAD =>
    (do
      let data ← (( do (Mem_read address (Int.ediv datasize 8) accdesc) ) : SailM (BitVec datasize) )
      sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:28341.62-28341.63"
      (V_set t datasize data))
  | _ => (pure ())
  if (wback : Bool)
  then
    (do
      let address : (BitVec 64) :=
        if (postindex : Bool)
        then (address + offset)
        else address
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleSIMDFPLoadStore ())
  else (pure ())

/-- Type quantifiers: datasize : Nat, k_limitedordered : Bool, n : Nat, offset : Int, regsize : Nat, k_rt_unknown : Bool, t : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t ∧ t ≤ 31 ∧ List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_ordered (datasize : Nat) (limitedordered : Bool) (memop : MemOp) (n : Nat) (offset : Int) (regsize : Nat) (rt_unknown : Bool) (t : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let dbytes := (Int.ediv datasize 8)
  let accdesc ← (( do (undefined_AccessDescriptor ()) ) : SailM AccessDescriptor )
  let accdesc ← (( do
    if (limitedordered : Bool)
    then (do (CreateAccDescLOR memop tagchecked))
    else (do (CreateAccDescAcqRel memop tagchecked)) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  match memop with
  | .MemOp_STORE =>
    (do
      let address : (BitVec 64) := (BitVec.addInt address offset)
      let data ← (( do
        if (rt_unknown : Bool)
        then (do (__UNKNOWN_bits datasize))
        else (do (X_read t datasize)) ) : SailM (BitVec datasize) )
      let _ : Unit := (AArch64_SetLSInstructionSyndrome dbytes false t (regsize == 64) true)
      (Mem_set address dbytes accdesc data)
      if (wback : Bool)
      then
        (do
          if ((n == 31) : Bool)
          then (SP_set address)
          else (X_set n 64 address))
      else (pure ()))
  | .MemOp_LOAD =>
    (do
      let _ : Unit := (AArch64_SetLSInstructionSyndrome dbytes false t (regsize == 64) true)
      let data ← (( do (Mem_read address dbytes accdesc) ) : SailM (BitVec datasize) )
      sail_assert ((datasize ≥b 0) && (regsize ≥b datasize)) "src/instrs64.sail:28464.69-28464.70"
      (X_set t regsize (Sail.BitVec.zeroExtend data regsize)))
  | _ => (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then
    (do
      let ar : (BitVec 1) := 1#1
      let excl : (BitVec 1) := 0#1
      let at' : (BitVec 1) := 0#1
      let is_load : Bool := (BEq.beq memop MemOp_LOAD)
      (SPESampleExtendedLoadStore ar excl at' is_load))
  else (pure ())

/-- Type quantifiers: k_acqrel : Bool, datasize : Nat, elsize : Nat, n : Nat, k_pair : Bool, regsize : Nat, k_rn_unknown : Bool, k_rt_unknown : Bool, s : Nat, t : Nat, t2 : Nat, k_tagchecked : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem elsize [32, 64] ∧ List.elem datasize [32, 64, 128] -/
def execute_aarch64_instrs_memory_exclusive_pair (acqrel : Bool) (datasize : Nat) (elsize : Nat) (memop : MemOp) (n : Nat) (pair : Bool) (regsize : Nat) (rn_unknown : Bool) (rt_unknown : Bool) (s : Nat) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let dbytes := (Int.ediv datasize 8)
  let accdesc ← (( do (CreateAccDescExLDST memop acqrel tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        if (rn_unknown : Bool)
        then (do (__UNKNOWN_bits 64))
        else (do (X_read n 64))) ) : SailM (BitVec 64) )
  match memop with
  | .MemOp_STORE =>
    (do
      let data ← (( do
        if (rt_unknown : Bool)
        then (do (__UNKNOWN_bits datasize))
        else
          (do
            if (pair : Bool)
            then
              (do
                let el1 ← (( do (X_read t (Int.ediv datasize 2)) ) : SailM (BitVec (datasize / 2)) )
                let el2 ← (( do (X_read t2 (Int.ediv datasize 2)) ) : SailM (BitVec (datasize / 2)) )
                if ((← (BigEndian accdesc.acctype)) : Bool)
                then (pure (el1 +++ el2))
                else (pure (el2 +++ el1)))
            else
              (do
                sail_assert ((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) "src/instrs64.sail:28968.61-28968.62"
                (X_read t datasize))) ) : SailM (BitVec datasize) )
      let status : (BitVec 1) := 1#1
      let status ← (( do
        if ((← (AArch64_ExclusiveMonitorsPass address dbytes)) : Bool)
        then
          (do
            (Mem_set address dbytes accdesc data)
            (pure (ExclusiveMonitorsStatus ())))
        else
          (do
            if ((← readReg SPESampleInFlight) : Bool)
            then (SPESetDataVirtualAddress address)
            else (pure ())
            (pure status)) ) : SailM (BitVec 1) )
      (X_set s 32 (Sail.BitVec.zeroExtend status 32)))
  | .MemOp_LOAD =>
    (do
      (AArch64_SetExclusiveMonitors address dbytes)
      if (pair : Bool)
      then
        (do
          if (rt_unknown : Bool)
          then
            (do
              sail_assert ((datasize == 32) || (datasize == 64)) "src/instrs64.sail:28984.58-28984.59"
              (X_set t datasize (← (__UNKNOWN_bits datasize))))
          else
            (do
              if ((elsize == 32) : Bool)
              then
                (do
                  let data ← (( do (Mem_read address dbytes accdesc) ) : SailM (BitVec datasize) )
                  if ((← (BigEndian accdesc.acctype)) : Bool)
                  then
                    (do
                      sail_assert ((0 ≤b elsize) && ((elsize ≤b (datasize -i 1)) && ((datasize -i 1) <b datasize))) "src/instrs64.sail:28989.110-28989.111"
                      sail_assert (((datasize -i elsize) == 32) || ((datasize -i elsize) == 64)) "src/instrs64.sail:28990.96-28990.97"
                      (X_set t (datasize -i elsize) (Sail.BitVec.extractLsb data (datasize -i 1) elsize))
                      (X_set t2 elsize (Sail.BitVec.extractLsb data (elsize -i 1) 0)))
                  else
                    (do
                      (X_set t elsize (Sail.BitVec.extractLsb data (elsize -i 1) 0))
                      sail_assert ((0 ≤b elsize) && ((elsize ≤b (datasize -i 1)) && ((datasize -i 1) <b datasize))) "src/instrs64.sail:28995.110-28995.111"
                      sail_assert (((datasize -i elsize) == 32) || ((datasize -i elsize) == 64)) "src/instrs64.sail:28996.96-28996.97"
                      (X_set t2 (datasize -i elsize) (Sail.BitVec.extractLsb data (datasize -i 1) elsize))))
              else
                (do
                  if ((! (IsAligned__1 address dbytes)) : Bool)
                  then (AArch64_Abort address (← (AlignmentFault accdesc)))
                  else (pure ())
                  (X_set t 64 (← (Mem_read (BitVec.addInt address 0) 8 accdesc)))
                  (X_set t2 64 (← (Mem_read (BitVec.addInt address 8) 8 accdesc))))))
      else
        (do
          let data ← (( do (Mem_read address dbytes accdesc) ) : SailM (BitVec datasize) )
          sail_assert ((datasize ≥b 0) && (regsize ≥b datasize)) "src/instrs64.sail:29008.73-29008.74"
          (X_set t regsize (Sail.BitVec.zeroExtend data regsize))))
  | _ => (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then
    (do
      let ar : (BitVec 1) :=
        if (acqrel : Bool)
        then 1#1
        else 0#1
      let excl : (BitVec 1) := 1#1
      let at' : (BitVec 1) := 0#1
      let is_load : Bool := (BEq.beq memop MemOp_LOAD)
      (SPESampleExtendedLoadStore ar excl at' is_load))
  else (pure ())

/-- Type quantifiers: k_acqrel : Bool, datasize : Nat, elsize : Nat, n : Nat, k_pair : Bool, regsize : Nat, k_rn_unknown : Bool, k_rt_unknown : Bool, s : Nat, t : Nat, t2 : Nat, k_tagchecked : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem elsize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] -/
def execute_aarch64_instrs_memory_exclusive_single (acqrel : Bool) (datasize : Nat) (elsize : Nat) (memop : MemOp) (n : Nat) (pair : Bool) (regsize : Nat) (rn_unknown : Bool) (rt_unknown : Bool) (s : Nat) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let dbytes := (Int.ediv datasize 8)
  let accdesc ← (( do (CreateAccDescExLDST memop acqrel tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        if (rn_unknown : Bool)
        then (do (__UNKNOWN_bits 64))
        else (do (X_read n 64))) ) : SailM (BitVec 64) )
  match memop with
  | .MemOp_STORE =>
    (do
      let data ← (( do
        if (rt_unknown : Bool)
        then (do (__UNKNOWN_bits datasize))
        else
          (do
            if (pair : Bool)
            then
              (do
                sail_assert (((Int.ediv datasize 2) == 8) || (((Int.ediv datasize 2) == 16) || (((Int.ediv datasize 2) == 32) || ((Int.ediv datasize 2) == 64)))) "src/instrs64.sail:29382.135-29382.136"
                let el1 ← (( do (X_read t (Int.ediv datasize 2)) ) : SailM (BitVec (datasize / 2)) )
                let el2 ← (( do (X_read t2 (Int.ediv datasize 2)) ) : SailM (BitVec (datasize / 2)) )
                if ((← (BigEndian accdesc.acctype)) : Bool)
                then (pure (el1 +++ el2))
                else (pure (el2 +++ el1)))
            else
              (do
                sail_assert ((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) "src/instrs64.sail:29387.61-29387.62"
                (X_read t datasize))) ) : SailM (BitVec datasize) )
      let status : (BitVec 1) := 1#1
      let status ← (( do
        if ((← (AArch64_ExclusiveMonitorsPass address dbytes)) : Bool)
        then
          (do
            (Mem_set address dbytes accdesc data)
            (pure (ExclusiveMonitorsStatus ())))
        else
          (do
            if ((← readReg SPESampleInFlight) : Bool)
            then (SPESetDataVirtualAddress address)
            else (pure ())
            (pure status)) ) : SailM (BitVec 1) )
      (X_set s 32 (Sail.BitVec.zeroExtend status 32)))
  | .MemOp_LOAD =>
    (do
      (AArch64_SetExclusiveMonitors address dbytes)
      if (pair : Bool)
      then
        (do
          if (rt_unknown : Bool)
          then
            (do
              sail_assert ((datasize == 32) || (datasize == 64)) "src/instrs64.sail:29403.58-29403.59"
              (X_set t datasize (← (__UNKNOWN_bits datasize))))
          else
            (do
              if ((elsize == 32) : Bool)
              then
                (do
                  let data ← (( do (Mem_read address dbytes accdesc) ) : SailM (BitVec datasize) )
                  if ((← (BigEndian accdesc.acctype)) : Bool)
                  then
                    (do
                      sail_assert ((0 ≤b elsize) && ((elsize ≤b (datasize -i 1)) && ((datasize -i 1) <b datasize))) "src/instrs64.sail:29408.110-29408.111"
                      sail_assert (((datasize -i elsize) == 32) || ((datasize -i elsize) == 64)) "src/instrs64.sail:29409.96-29409.97"
                      (X_set t (datasize -i elsize) (Sail.BitVec.extractLsb data (datasize -i 1) elsize))
                      (X_set t2 elsize (Sail.BitVec.extractLsb data (elsize -i 1) 0)))
                  else
                    (do
                      sail_assert ((0 ≤b (elsize -i 1)) && ((elsize -i 1) <b datasize)) "src/instrs64.sail:29413.85-29413.86"
                      (X_set t elsize (Sail.BitVec.extractLsb data (elsize -i 1) 0))
                      sail_assert ((0 ≤b elsize) && ((elsize ≤b (datasize -i 1)) && ((datasize -i 1) <b datasize))) "src/instrs64.sail:29415.110-29415.111"
                      sail_assert (((datasize -i elsize) == 32) || ((datasize -i elsize) == 64)) "src/instrs64.sail:29416.96-29416.97"
                      (X_set t2 (datasize -i elsize) (Sail.BitVec.extractLsb data (datasize -i 1) elsize))))
              else
                (do
                  if ((! (IsAligned__1 address dbytes)) : Bool)
                  then (AArch64_Abort address (← (AlignmentFault accdesc)))
                  else (pure ())
                  (X_set t 64 (← (Mem_read (BitVec.addInt address 0) 8 accdesc)))
                  (X_set t2 64 (← (Mem_read (BitVec.addInt address 8) 8 accdesc))))))
      else
        (do
          let data ← (( do (Mem_read address dbytes accdesc) ) : SailM (BitVec datasize) )
          sail_assert ((datasize ≥b 0) && (regsize ≥b datasize)) "src/instrs64.sail:29428.73-29428.74"
          (X_set t regsize (Sail.BitVec.zeroExtend data regsize))))
  | _ => (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then
    (do
      let ar : (BitVec 1) :=
        if (acqrel : Bool)
        then 1#1
        else 0#1
      let excl : (BitVec 1) := 1#1
      let at' : (BitVec 1) := 0#1
      let is_load : Bool := (BEq.beq memop MemOp_LOAD)
      (SPESampleExtendedLoadStore ar excl at' is_load))
  else (pure ())

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_atomicops_ld_128_ldclrp (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let value1_name ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value2_name ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescAtomicOp op acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let store_value ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (value1_name +++ value2_name))
    else (pure (value2_name +++ value1_name)) ) : SailM (BitVec 128) )
  let comparevalue ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
  let data ← (( do (MemAtomic address comparevalue store_value accdesc) ) : SailM (BitVec 128) )
  if ((← (BigEndian accdesc.acctype)) : Bool)
  then
    (do
      (X_set t 64 (Sail.BitVec.extractLsb data 127 64))
      (X_set t2 64 (Sail.BitVec.extractLsb data 63 0)))
  else
    (do
      (X_set t 64 (Sail.BitVec.extractLsb data 63 0))
      (X_set t2 64 (Sail.BitVec.extractLsb data 127 64)))

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcgettag (n : Nat) (offset : (BitVec 64)) (t : Nat) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) := (address + offset)
  let address : (BitVec 64) := (Align_bits address TAG_GRANULE)
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_LOAD) ) : SailM AccessDescriptor )
  let tag ← (( do (AArch64_MemTag_read address accdesc) ) : SailM (BitVec 4) )
  (X_set t 64 (← (AArch64_AddressWithAllocationTag (← (X_read t 64)) tag)))

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcgettagarray (n : Nat) (t : Nat) : SailM Unit := do
  if (((← readReg PSTATE).EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let data : (BitVec 64) := (Zeros (n := 64))
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let size ← do (pure (4 *i (2 ^i (BitVec.toNat (_get_GMID_EL1_Type_BS (← readReg GMID_EL1))))))
  let address : (BitVec 64) := (Align_bits address size)
  let count := (Int.shiftr size LOG2_TAG_GRANULE)
  let index : Int := (BitVec.toNat (Sail.BitVec.extractLsb address (LOG2_TAG_GRANULE +i 3) LOG2_TAG_GRANULE))
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_LOAD) ) : SailM AccessDescriptor )
  let (address, data, index) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (count -i 1)
    let mut loop_vars := (address, data, index)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (address, data, index) := loop_vars
      loop_vars ← do
        let tag ← (( do (AArch64_MemTag_read address accdesc) ) : SailM (BitVec 4) )
        let data ← (( do
          let index := index
          sail_assert ((0 ≤b (index *i 4)) && (((index *i 4) +i 3) <b 64)) "src/instrs64.sail:30614.72-30614.73"
          (pure (Sail.BitVec.updateSubrange data ((index *i 4) +i 3) (index *i 4) tag)) ) : SailM (BitVec 64) )
        let address : (BitVec 64) := (BitVec.addInt address TAG_GRANULE)
        let index : Int := (index +i 1)
        (pure (address, data, index))
    (pure loop_vars) ) : SailM ((BitVec 64) × (BitVec 64) × Int) )
  (X_set t 64 data)

/-- Type quantifiers: datasize : Nat, n : Nat, offset : Int, k_postindex : Bool, k_rt_unknown : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] -/
def execute_aarch64_instrs_memory_ordered_pair_ldiapp (datasize : Nat) (memop : MemOp) (n : Nat) (offset : Int) (postindex : Bool) (rt_unknown : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data1 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let data2 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let dbytes := (Int.ediv datasize 8)
  let accdesc ← (( do (CreateAccDescAcqRel memop tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (BitVec.addInt address offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      let data1 ← (( do
        if ((rt_unknown && (t == n)) : Bool)
        then (do (__UNKNOWN_bits datasize))
        else (do (X_read t datasize)) ) : SailM (BitVec datasize) )
      let data2 ← (( do
        if ((rt_unknown && (t2 == n)) : Bool)
        then (do (__UNKNOWN_bits datasize))
        else (do (X_read t2 datasize)) ) : SailM (BitVec datasize) )
      if ((← (HaveLSE2Ext ())) : Bool)
      then
        (do
          let full_data ← (( do (undefined_bitvector (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
          let full_data ← (( do
            if ((← (BigEndian accdesc.acctype)) : Bool)
            then (pure (data1 +++ data2))
            else (pure (data2 +++ data1)) ) : SailM (BitVec (2 * datasize)) )
          let ispair : Bool := true
          let highestAddressfirst : Bool := ((! postindex) && (offset <b 0))
          (Mem_set__2 address (2 *i dbytes) accdesc ispair highestAddressfirst full_data))
      else
        (do
          if (((! postindex) && (offset <b 0)) : Bool)
          then
            (do
              (Mem_set (BitVec.addInt address dbytes) dbytes accdesc data2)
              (Mem_set (BitVec.addInt address 0) dbytes accdesc data1))
          else
            (do
              (Mem_set (BitVec.addInt address 0) dbytes accdesc data1)
              (Mem_set (BitVec.addInt address dbytes) dbytes accdesc data2))))
  | .MemOp_LOAD =>
    (do
      let (data1, data2) ← (( do
        if ((← (HaveLSE2Ext ())) : Bool)
        then
          (do
            let ispair : Bool := true
            let full_data ← (( do (Mem_read__1 address (2 *i dbytes) accdesc ispair) ) : SailM (BitVec (2 * datasize)) )
            let (data1, data2) ← (( do
              if ((← (BigEndian accdesc.acctype)) : Bool)
              then
                (let data2 : (BitVec datasize) := (Sail.BitVec.extractLsb full_data (datasize -i 1) 0)
                let data1 : (BitVec datasize) := (Sail.BitVec.extractLsb full_data ((2 *i datasize) -i 1) datasize)
                (pure (data1, data2)))
              else
                (let data1 : (BitVec datasize) := (Sail.BitVec.extractLsb full_data (datasize -i 1) 0)
                let data2 : (BitVec datasize) := (Sail.BitVec.extractLsb full_data ((2 *i datasize) -i 1) datasize)
                (pure (data1, data2))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
            (pure (data1, data2)))
        else
          (do
            let data1 ← (Mem_read (BitVec.addInt address 0) dbytes accdesc)
            let data2 ← (Mem_read (BitVec.addInt address dbytes) dbytes accdesc)
            (pure (data1, data2))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      let (data1, data2) ← (( do
        if (rt_unknown : Bool)
        then
          (do
            let data1 ← (__UNKNOWN_bits datasize)
            let data2 ← (__UNKNOWN_bits datasize)
            (pure (data1, data2)))
        else (pure (data1, data2)) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      (X_set t datasize data1)
      (X_set t2 datasize data2))
  | _ => (pure ())
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then (do (__UNKNOWN_bits 64))
        else
          (if (postindex : Bool)
          then (pure (BitVec.addInt address offset))
          else (pure address)) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleGeneralPurposeLoadStore ())
  else (pure ())

/-- Type quantifiers: datasize : Nat, n : Nat, k_nontemporal : Bool, k_postindex : Bool, k_rt_unknown : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] -/
def execute_aarch64_instrs_memory_pair_general_no_alloc (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (rt_unknown : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data1 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let data2 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let dbytes := (Int.ediv datasize 8)
  let privileged ← (( do (pure ((← readReg PSTATE).EL != EL0)) ) : SailM Bool )
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      let data1 ← (( do
        if ((rt_unknown && (t == n)) : Bool)
        then (do (__UNKNOWN_bits datasize))
        else (do (X_read t datasize)) ) : SailM (BitVec datasize) )
      let data2 ← (( do
        if ((rt_unknown && (t2 == n)) : Bool)
        then (do (__UNKNOWN_bits datasize))
        else (do (X_read t2 datasize)) ) : SailM (BitVec datasize) )
      (Mem_set (BitVec.addInt address 0) dbytes accdesc data1)
      (Mem_set (BitVec.addInt address dbytes) dbytes accdesc data2))
  | .MemOp_LOAD =>
    (do
      let (data1, data2) ← (( do
        if ((← (HaveLSE2Ext ())) : Bool)
        then
          (do
            let ispair : Bool := true
            let full_data ← (( do (Mem_read__1 address (2 *i dbytes) accdesc ispair) ) : SailM (BitVec (2 * datasize)) )
            let (data1, data2) ← (( do
              if ((← (BigEndian accdesc.acctype)) : Bool)
              then
                (let data2 : (BitVec datasize) := (Sail.BitVec.extractLsb full_data (datasize -i 1) 0)
                let data1 : (BitVec datasize) := (Sail.BitVec.extractLsb full_data ((2 *i datasize) -i 1) datasize)
                (pure (data1, data2)))
              else
                (let data1 : (BitVec datasize) := (Sail.BitVec.extractLsb full_data (datasize -i 1) 0)
                let data2 : (BitVec datasize) := (Sail.BitVec.extractLsb full_data ((2 *i datasize) -i 1) datasize)
                (pure (data1, data2))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
            (pure (data1, data2)))
        else
          (do
            let data1 ← (Mem_read (BitVec.addInt address 0) dbytes accdesc)
            let data2 ← (Mem_read (BitVec.addInt address dbytes) dbytes accdesc)
            (pure (data1, data2))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      let (data1, data2) ← (( do
        if (rt_unknown : Bool)
        then
          (do
            let data1 ← (__UNKNOWN_bits datasize)
            let data2 ← (__UNKNOWN_bits datasize)
            (pure (data1, data2)))
        else (pure (data1, data2)) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      (X_set t datasize data1)
      (X_set t2 datasize data2))
  | _ => (pure ())
  if (wback : Bool)
  then
    (do
      let address : (BitVec 64) :=
        if (postindex : Bool)
        then (address + offset)
        else address
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleGeneralPurposeLoadStore ())
  else (pure ())

/-- Type quantifiers: datasize : Nat, n : Nat, k_nontemporal : Bool, k_postindex : Bool, k_rt_unknown : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64, 128, 256] -/
def execute_aarch64_instrs_memory_pair_simdfp_no_alloc (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (rt_unknown : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data1 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let data2 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let dbytes := (Int.ediv datasize 8)
  let accdesc ← (( do (CreateAccDescASIMD memop nontemporal tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:31021.62-31021.63"
      let data1 ← (( do (V_read t datasize) ) : SailM (BitVec datasize) )
      let data2 ← (( do (V_read t2 datasize) ) : SailM (BitVec datasize) )
      (Mem_set (BitVec.addInt address 0) dbytes accdesc data1)
      (Mem_set (BitVec.addInt address dbytes) dbytes accdesc data2))
  | .MemOp_LOAD =>
    (do
      let data1 ← (( do (Mem_read (BitVec.addInt address 0) dbytes accdesc) ) : SailM (BitVec datasize) )
      let data2 ← (( do (Mem_read (BitVec.addInt address dbytes) dbytes accdesc) ) : SailM (BitVec datasize) )
      let (data1, data2) ← (( do
        if (rt_unknown : Bool)
        then
          (do
            let data1 ← (__UNKNOWN_bits datasize)
            let data2 ← (__UNKNOWN_bits datasize)
            (pure (data1, data2)))
        else (pure (data1, data2)) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:31034.62-31034.63"
      (V_set t datasize data1)
      (V_set t2 datasize data2))
  | _ => (pure ())
  if (wback : Bool)
  then
    (do
      let address : (BitVec 64) :=
        if (postindex : Bool)
        then (address + offset)
        else address
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleSIMDFPLoadStore ())
  else (pure ())

/-- Type quantifiers: datasize : Nat, n : Nat, k_nontemporal : Bool, k_postindex : Bool, k_rt_unknown : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64, 128, 256] -/
def execute_aarch64_instrs_memory_pair_simdfp_post_idx (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (rt_unknown : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data1 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let data2 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let dbytes := (Int.ediv datasize 8)
  let accdesc ← (( do (CreateAccDescASIMD memop nontemporal tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:31176.62-31176.63"
      let data1 ← (( do (V_read t datasize) ) : SailM (BitVec datasize) )
      let data2 ← (( do (V_read t2 datasize) ) : SailM (BitVec datasize) )
      (Mem_set (BitVec.addInt address 0) dbytes accdesc data1)
      (Mem_set (BitVec.addInt address dbytes) dbytes accdesc data2))
  | .MemOp_LOAD =>
    (do
      let data1 ← (( do (Mem_read (BitVec.addInt address 0) dbytes accdesc) ) : SailM (BitVec datasize) )
      let data2 ← (( do (Mem_read (BitVec.addInt address dbytes) dbytes accdesc) ) : SailM (BitVec datasize) )
      let (data1, data2) ← (( do
        if (rt_unknown : Bool)
        then
          (do
            let data1 ← (__UNKNOWN_bits datasize)
            let data2 ← (__UNKNOWN_bits datasize)
            (pure (data1, data2)))
        else (pure (data1, data2)) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:31189.62-31189.63"
      (V_set t datasize data1)
      (V_set t2 datasize data2))
  | _ => (pure ())
  if (wback : Bool)
  then
    (do
      let address : (BitVec 64) :=
        if (postindex : Bool)
        then (address + offset)
        else address
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleSIMDFPLoadStore ())
  else (pure ())

/-- Type quantifiers: datasize : Nat, k_is_signed : Bool, n : Nat, k_nontemporal : Bool, k_postindex : Bool, k_rt_unknown : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] -/
def execute_aarch64_instrs_memory_pair_general_post_idx (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (rt_unknown : Bool) (is_signed : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data1 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let data2 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let dbytes := (Int.ediv datasize 8)
  let privileged ← (( do (pure ((← readReg PSTATE).EL != EL0)) ) : SailM Bool )
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      let data1 ← (( do
        if ((rt_unknown && (t == n)) : Bool)
        then (do (__UNKNOWN_bits datasize))
        else (do (X_read t datasize)) ) : SailM (BitVec datasize) )
      let data2 ← (( do
        if ((rt_unknown && (t2 == n)) : Bool)
        then (do (__UNKNOWN_bits datasize))
        else (do (X_read t2 datasize)) ) : SailM (BitVec datasize) )
      if ((← (HaveLSE2Ext ())) : Bool)
      then
        (do
          let full_data ← (( do (undefined_bitvector (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
          let full_data ← (( do
            if ((← (BigEndian accdesc.acctype)) : Bool)
            then (pure (data1 +++ data2))
            else (pure (data2 +++ data1)) ) : SailM (BitVec (2 * datasize)) )
          let ispair : Bool := true
          (Mem_set__1 address (2 *i dbytes) accdesc ispair full_data))
      else
        (do
          (Mem_set (BitVec.addInt address 0) dbytes accdesc data1)
          (Mem_set (BitVec.addInt address dbytes) dbytes accdesc data2)))
  | .MemOp_LOAD =>
    (do
      let (data1, data2) ← (( do
        if (((← (HaveLSE2Ext ())) && (! is_signed)) : Bool)
        then
          (do
            let ispair : Bool := true
            let full_data ← (( do (Mem_read__1 address (2 *i dbytes) accdesc ispair) ) : SailM (BitVec (2 * datasize)) )
            let (data1, data2) ← (( do
              if ((← (BigEndian accdesc.acctype)) : Bool)
              then
                (let data2 : (BitVec datasize) := (Sail.BitVec.extractLsb full_data (datasize -i 1) 0)
                let data1 : (BitVec datasize) := (Sail.BitVec.extractLsb full_data ((2 *i datasize) -i 1) datasize)
                (pure (data1, data2)))
              else
                (let data1 : (BitVec datasize) := (Sail.BitVec.extractLsb full_data (datasize -i 1) 0)
                let data2 : (BitVec datasize) := (Sail.BitVec.extractLsb full_data ((2 *i datasize) -i 1) datasize)
                (pure (data1, data2))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
            (pure (data1, data2)))
        else
          (do
            let data1 ← (Mem_read (BitVec.addInt address 0) dbytes accdesc)
            let data2 ← (Mem_read (BitVec.addInt address dbytes) dbytes accdesc)
            (pure (data1, data2))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      let (data1, data2) ← (( do
        if (rt_unknown : Bool)
        then
          (do
            let data1 ← (__UNKNOWN_bits datasize)
            let data2 ← (__UNKNOWN_bits datasize)
            (pure (data1, data2)))
        else (pure (data1, data2)) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      if (is_signed : Bool)
      then
        (do
          (X_set t 64 (sign_extend data1 64))
          (X_set t2 64 (sign_extend data2 64)))
      else
        (do
          (X_set t datasize data1)
          (X_set t2 datasize data2)))
  | _ => (pure ())
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then (do (__UNKNOWN_bits 64))
        else
          (if (postindex : Bool)
          then (pure (address + offset))
          else (pure address)) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleGeneralPurposeLoadStore ())
  else (pure ())

/-- Type quantifiers: datasize : Nat, n : Nat, k_nontemporal : Bool, k_postindex : Bool, t : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64, 128, 256, 512, 1024] -/
def execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let accdesc ← (( do (CreateAccDescASIMD memop nontemporal tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:32419.62-32419.63"
      let data ← (( do (V_read t datasize) ) : SailM (BitVec datasize) )
      (Mem_set address (Int.ediv datasize 8) accdesc data))
  | .MemOp_LOAD =>
    (do
      let data ← (( do (Mem_read address (Int.ediv datasize 8) accdesc) ) : SailM (BitVec datasize) )
      sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:32425.62-32425.63"
      (V_set t datasize data))
  | _ => (pure ())
  if (wback : Bool)
  then
    (do
      let address : (BitVec 64) :=
        if (postindex : Bool)
        then (address + offset)
        else address
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleSIMDFPLoadStore ())
  else (pure ())

/-- Type quantifiers: k_is_signed : Bool, k_nontemporal : Bool, size : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ List.elem size [4, 8] -/
def execute_aarch64_instrs_memory_literal_general (memop : MemOp) (nontemporal : Bool) (offset : (BitVec 64)) (is_signed : Bool) (size : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (pure ((← (PC_read ())) + offset)) ) : SailM (BitVec 64) )
  let data ← (( do (undefined_bitvector (size *i 8)) ) : SailM (BitVec (size * 8)) )
  let privileged ← (( do (pure ((← readReg PSTATE).EL != EL0)) ) : SailM Bool )
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM AccessDescriptor )
  match memop with
  | .MemOp_LOAD =>
    (do
      let data ← (( do (Mem_read address size accdesc) ) : SailM (BitVec (size * 8)) )
      if (is_signed : Bool)
      then (X_set t 64 (sign_extend data 64))
      else (X_set t (size *i 8) data))
  | .MemOp_PREFETCH => (Prefetch address (integer_subrange t 4 0))
  | _ => (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleGeneralPurposeLoadStore ())
  else (pure ())

/-- Type quantifiers: k_nontemporal : Bool, size : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ List.elem size [4, 8, 16] -/
def execute_aarch64_instrs_memory_literal_simdfp (nontemporal : Bool) (offset : (BitVec 64)) (size : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (pure ((← (PC_read ())) + offset)) ) : SailM (BitVec 64) )
  let privileged ← (( do (pure ((← readReg PSTATE).EL != EL0)) ) : SailM Bool )
  (CheckFPEnabled64 ())
  let accdesc ← (( do (CreateAccDescASIMD MemOp_LOAD nontemporal tagchecked) ) : SailM AccessDescriptor )
  let data ← (( do (Mem_read address size accdesc) ) : SailM (BitVec (size * 8)) )
  (V_set t (size *i 8) data)
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleSIMDFPLoadStore ())
  else (pure ())

def decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := true
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33437.113-33437.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33456.107-33456.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33523.113-33523.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33542.107-33542.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldrh_imm_aarch64_instrs_memory_single_general_immediate_unsigned (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := ((Sail.BitVec.zeroExtend imm12 64) <<< scale)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33609.113-33609.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33628.107-33628.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := true
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33695.113-33695.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33714.107-33714.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33781.113-33781.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33800.107-33800.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldrsb_imm_aarch64_instrs_memory_single_general_immediate_unsigned (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := ((Sail.BitVec.zeroExtend imm12 64) <<< scale)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33867.113-33867.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33886.107-33886.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := true
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33953.113-33953.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33972.107-33972.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34039.113-34039.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34058.107-34058.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldrsh_imm_aarch64_instrs_memory_single_general_immediate_unsigned (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := ((Sail.BitVec.zeroExtend imm12 64) <<< scale)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34125.113-34125.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34144.107-34144.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := true
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34211.113-34211.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34230.107-34230.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34297.113-34297.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34316.107-34316.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldrsw_imm_aarch64_instrs_memory_single_general_immediate_unsigned (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := ((Sail.BitVec.zeroExtend imm12 64) <<< scale)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34383.113-34383.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34402.107-34402.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := true
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34985.113-34985.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35004.107-35004.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_strh_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35071.113-35071.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35090.107-35090.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_strh_imm_aarch64_instrs_memory_single_general_immediate_unsigned (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := ((Sail.BitVec.zeroExtend imm12 64) <<< scale)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35157.113-35157.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35176.107-35176.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

/-- Type quantifiers: datasize : Nat, k_is_signed : Bool, m : Nat, n : Nat, k_nontemporal : Bool, k_postindex : Bool, regsize : Nat, k_rt_unknown : Bool, shift : Nat, t : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback : Bool, 0 ≤ t ∧ t ≤ 31 ∧ List.elem shift [0, 1, 2, 3] ∧ List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_single_general_register (datasize : Nat) (extend_type : ExtendType) (m : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (postindex : Bool) (regsize : Nat) (rt_unknown : Bool) (shift : Nat) (is_signed : Bool) (t : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let offset ← (( do (ExtendReg m extend_type shift 64) ) : SailM (BitVec 64) )
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let privileged ← (( do (pure ((← readReg PSTATE).EL != EL0)) ) : SailM Bool )
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((bne memop MemOp_PREFETCH) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      let data ← (( do
        if (rt_unknown : Bool)
        then (do (__UNKNOWN_bits datasize))
        else (do (X_read t datasize)) ) : SailM (BitVec datasize) )
      let _ : Unit :=
        if ((! wback) : Bool)
        then (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) false t (regsize == 64) false)
        else ()
      (Mem_set address (Int.ediv datasize 8) accdesc data))
  | .MemOp_LOAD =>
    (do
      let _ : Unit :=
        if ((! wback) : Bool)
        then (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) is_signed t (regsize == 64) false)
        else ()
      let data ← (( do (Mem_read address (Int.ediv datasize 8) accdesc) ) : SailM (BitVec datasize) )
      if (is_signed : Bool)
      then
        (do
          sail_assert ((datasize >b 0) && (regsize ≥b datasize)) "src/instrs64.sail:35245.72-35245.73"
          (X_set t regsize (sign_extend data regsize)))
      else
        (do
          sail_assert ((datasize ≥b 0) && (regsize ≥b datasize)) "src/instrs64.sail:35248.73-35248.74"
          (X_set t regsize (Sail.BitVec.zeroExtend data regsize))))
  | .MemOp_PREFETCH => (Prefetch address (integer_subrange t 4 0))
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then (do (__UNKNOWN_bits 64))
        else
          (if (postindex : Bool)
          then (pure (address + offset))
          else (pure address)) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleGeneralPurposeLoadStore ())
  else (pure ())

/-- Type quantifiers: datasize : Nat, m : Nat, n : Nat, k_nontemporal : Bool, k_postindex : Bool, shift : Nat, t : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t ∧ t ≤ 31 ∧ List.elem shift [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [8, 16, 32, 64, 128, 256, 512, 1024] -/
def execute_aarch64_instrs_memory_single_simdfp_register (datasize : Nat) (extend_type : ExtendType) (m : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (postindex : Bool) (shift : Nat) (t : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  let offset ← (( do (ExtendReg m extend_type shift 64) ) : SailM (BitVec 64) )
  (CheckFPEnabled64 ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let accdesc ← (( do (CreateAccDescASIMD memop nontemporal tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:36272.62-36272.63"
      let data ← (( do (V_read t datasize) ) : SailM (BitVec datasize) )
      (Mem_set address (Int.ediv datasize 8) accdesc data))
  | .MemOp_LOAD =>
    (do
      let data ← (( do (Mem_read address (Int.ediv datasize 8) accdesc) ) : SailM (BitVec datasize) )
      sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:36278.62-36278.63"
      (V_set t datasize data))
  | _ => (pure ())
  if (wback : Bool)
  then
    (do
      let address : (BitVec 64) :=
        if (postindex : Bool)
        then (address + offset)
        else address
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleSIMDFPLoadStore ())
  else (pure ())

/-- Type quantifiers: n : Nat, k_nontemporal : Bool, t : Nat, k_tagchecked : Bool, k_use_key_a : Bool, k_wback : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_single_general_immediate_signed_pac (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (t : Nat) (tagchecked : Bool) (use_key_a : Bool) (wback__arg : Bool) : SailM Unit := do
  let wback : Bool := wback__arg
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let privileged ← (( do (pure ((← readReg PSTATE).EL != EL0)) ) : SailM Bool )
  let wb_unknown : Bool := false
  let auth_then_branch : Bool := true
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM AccessDescriptor )
  let (wb_unknown, wback) ← (( do
    if (((wback && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:36386.113-36386.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (wb_unknown, wback)))
    else (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
  let address ← (( do
    if ((n == 31) : Bool)
    then (do (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let _ : Unit :=
    if ((! wback) : Bool)
    then (AArch64_SetLSInstructionSyndrome 8 false t true false)
    else ()
  let address ← (( do
    if (use_key_a : Bool)
    then (do (AuthDA address (← (X_read 31 64)) auth_then_branch))
    else (do (AuthDB address (← (X_read 31 64)) auth_then_branch)) ) : SailM (BitVec 64) )
  if ((n == 31) : Bool)
  then (CheckSPAlignment ())
  else (pure ())
  let address : (BitVec 64) := (address + offset)
  let data ← (( do (Mem_read address 8 accdesc) ) : SailM (BitVec 64) )
  (X_set t 64 data)
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then (do (__UNKNOWN_bits 64))
        else (pure address) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleGeneralPurposeLoadStore ())
  else (pure ())

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_atomicops_ld_128_ldsetp (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let value1_name ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value2_name ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescAtomicOp op acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let store_value ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (value1_name +++ value2_name))
    else (pure (value2_name +++ value1_name)) ) : SailM (BitVec 128) )
  let comparevalue ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
  let data ← (( do (MemAtomic address comparevalue store_value accdesc) ) : SailM (BitVec 128) )
  if ((← (BigEndian accdesc.acctype)) : Bool)
  then
    (do
      (X_set t 64 (Sail.BitVec.extractLsb data 127 64))
      (X_set t2 64 (Sail.BitVec.extractLsb data 63 0)))
  else
    (do
      (X_set t 64 (Sail.BitVec.extractLsb data 63 0))
      (X_set t2 64 (Sail.BitVec.extractLsb data 127 64)))

/-- Type quantifiers: datasize : Nat, k_is_signed : Bool, n : Nat, k_nontemporal : Bool, k_postindex : Bool, regsize : Nat, k_rt_unknown : Bool, t : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback : Bool, 0 ≤ t ∧ t ≤ 31 ∧ List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (regsize : Nat) (rt_unknown : Bool) (is_signed : Bool) (t : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let privileged ← (( do (AArch64_IsUnprivAccessPriv ()) ) : SailM Bool )
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((bne memop MemOp_PREFETCH) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      let data ← (( do
        if (rt_unknown : Bool)
        then (do (__UNKNOWN_bits datasize))
        else (do (X_read t datasize)) ) : SailM (BitVec datasize) )
      let _ : Unit :=
        if ((! wback) : Bool)
        then (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) false t (regsize == 64) false)
        else ()
      (Mem_set address (Int.ediv datasize 8) accdesc data))
  | .MemOp_LOAD =>
    (do
      let _ : Unit :=
        if ((! wback) : Bool)
        then (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) is_signed t (regsize == 64) false)
        else ()
      let data ← (( do (Mem_read address (Int.ediv datasize 8) accdesc) ) : SailM (BitVec datasize) )
      if (is_signed : Bool)
      then
        (do
          sail_assert ((datasize >b 0) && (regsize ≥b datasize)) "src/instrs64.sail:36581.72-36581.73"
          (X_set t regsize (sign_extend data regsize)))
      else
        (do
          sail_assert ((datasize ≥b 0) && (regsize ≥b datasize)) "src/instrs64.sail:36584.73-36584.74"
          (X_set t regsize (Sail.BitVec.zeroExtend data regsize))))
  | .MemOp_PREFETCH => (Prefetch address (integer_subrange t 4 0))
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then (do (__UNKNOWN_bits 64))
        else
          (if (postindex : Bool)
          then (pure (address + offset))
          else (pure address)) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleGeneralPurposeLoadStore ())
  else (pure ())

/-- Type quantifiers: datasize : Nat, n : Nat, k_nontemporal : Bool, k_postindex : Bool, t : Nat, k_tagchecked : Bool, k_wback : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64, 128, 256, 512, 1024] -/
def execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (tagchecked : Bool) (wback : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let accdesc ← (( do (CreateAccDescASIMD memop nontemporal tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:37404.62-37404.63"
      let data ← (( do (V_read t datasize) ) : SailM (BitVec datasize) )
      (Mem_set address (Int.ediv datasize 8) accdesc data))
  | .MemOp_LOAD =>
    (do
      let data ← (( do (Mem_read address (Int.ediv datasize 8) accdesc) ) : SailM (BitVec datasize) )
      sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:37410.62-37410.63"
      (V_set t datasize data))
  | _ => (pure ())
  if (wback : Bool)
  then
    (do
      let address : (BitVec 64) :=
        if (postindex : Bool)
        then (address + offset)
        else address
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleSIMDFPLoadStore ())
  else (pure ())

def decode_ldurb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then
            (do
              let memop : MemOp := MemOp_PREFETCH
              if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              (pure (is_signed, memop, regsize)))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37689.113-37689.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37708.107-37708.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldurh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then
            (do
              let memop : MemOp := MemOp_PREFETCH
              if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              (pure (is_signed, memop, regsize)))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37779.113-37779.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37798.107-37798.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldursb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then
            (do
              let memop : MemOp := MemOp_PREFETCH
              if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              (pure (is_signed, memop, regsize)))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37869.113-37869.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37888.107-37888.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldursh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then
            (do
              let memop : MemOp := MemOp_PREFETCH
              if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              (pure (is_signed, memop, regsize)))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37959.113-37959.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37978.107-37978.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldursw_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then
            (do
              let memop : MemOp := MemOp_PREFETCH
              if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              (pure (is_signed, memop, regsize)))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:38049.113-38049.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:38068.107-38068.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_prfum_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then
            (do
              let memop : MemOp := MemOp_PREFETCH
              if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              (pure (is_signed, memop, regsize)))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:38139.113-38139.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:38158.107-38158.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_sturb_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then
            (do
              let memop : MemOp := MemOp_PREFETCH
              if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              (pure (is_signed, memop, regsize)))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:38319.113-38319.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:38338.107-38338.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_sturh_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let is_signed ← (( do (undefined_bool ()) ) : SailM Bool )
  let regsize : Nat := 32
  let (is_signed, memop, regsize) ← (( do
    if (((BitVec.join1 [(BitVec.access opc 1)]) == 0#1) : Bool)
    then
      (let memop : MemOp :=
        if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
        then MemOp_LOAD
        else MemOp_STORE
      let regsize : Int :=
        if ((size == 0b11#2) : Bool)
        then 64
        else 32
      let is_signed : Bool := false
      (pure (is_signed, memop, regsize)))
    else
      (do
        let (is_signed, memop, regsize) ← (( do
          if ((size == 0b11#2) : Bool)
          then
            (do
              let memop : MemOp := MemOp_PREFETCH
              if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              (pure (is_signed, memop, regsize)))
          else
            (do
              let memop : MemOp := MemOp_LOAD
              if (((size == 0b10#2) && ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let regsize : Int :=
                if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
                then 32
                else 64
              let is_signed : Bool := true
              (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
        (pure (is_signed, memop, regsize))) ) : SailM (Bool × MemOp × Int) )
  let regsize := regsize
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:38409.113-38409.114"
        let (wb_unknown, wback) ← (( do
          match c with
          | .Constraint_WBSUPPRESS =>
            (let wback : Bool := false
            (pure (wb_unknown, wback)))
          | .Constraint_UNKNOWN =>
            (let wb_unknown : Bool := true
            (pure (wb_unknown, wback)))
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ())
              (pure (wb_unknown, wback)))
          | _ => (pure (wb_unknown, wback)) ) : SailM (Bool × Bool) )
        (pure (c, wb_unknown, wback)))
    else (pure (c, wb_unknown, wback)) ) : SailM (Constraint × Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:38428.107-38428.108"
        match c with
        | .Constraint_NONE => (pure false)
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let a := (BitVec.toNat Ra)
  let destsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let datasize := destsize
  let sub_op : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub a d datasize destsize m n sub_op)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let operand3 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let product ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element2, product, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, product, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, product, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e esize)
        let element2 ← (Elem_read operand2 e esize)
        let product : (BitVec esize) := (integer_subrange ((BitVec.toNat element1) *i (BitVec.toNat element2)) (esize -i 1) 0)
        let result ← (( do
          if (sub_op : Bool)
          then (do (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product)))
          else (do (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))) ) : SailM (BitVec datasize) )
        (pure (element1, element2, product, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem idxdsize [64, 128] ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m idxdsize) ) : SailM (BitVec idxdsize) )
  let operand3 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let product ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 index esize))))
  let (element1, product, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, product, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, product, result) := loop_vars
      loop_vars ← do
        let element1 ← (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
        let result ← (( do
          if (sub_op : Bool)
          then (do (Elem_set result e esize ((← (Elem_read operand3 e esize)) - product)))
          else (do (Elem_set result e esize ((← (Elem_read operand3 e esize)) + product))) ) : SailM (BitVec datasize) )
        (pure (element1, product, result))
    (pure loop_vars) ) : SailM (Int × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

def decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide (Rd : (BitVec 5)) (imm16 : (BitVec 16)) (hw : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let imm : (BitVec 16) := imm16
  let opcode ← (( do (undefined_MoveWideOp ()) ) : SailM MoveWideOp )
  let opcode ← (( do
    match (opc : BitVec 2) with
    | 0b00 => (pure MoveWideOp_N)
    | 0b10 => (pure MoveWideOp_Z)
    | 0b11 => (pure MoveWideOp_K)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MoveWideOp )
  let opcode := opcode
  if (((sf == 0#1) && ((BitVec.join1 [(BitVec.access hw 1)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let pos := (BitVec.toNat (hw +++ 0b0000#4))
  (execute_aarch64_instrs_integer_ins_ext_insert_movewide d datasize imm opcode pos)

/-- Type quantifiers: k_read : Bool, sys_crm : Nat, sys_crn : Nat, sys_op0 : Nat, sys_op1 : Nat, sys_op2 : Nat, t : Nat, t2 : Nat, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ List.elem sys_op2 [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem sys_op1 [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem sys_op0 [2, 3] ∧ 0 ≤ sys_crn ∧ sys_crn ≤ 15 ∧ 0 ≤ sys_crm ∧ sys_crm ≤ 15 -/
def execute_aarch64_instrs_system_register_system_128 (read : Bool) (sys_crm : Nat) (sys_crn : Nat) (sys_op0 : Nat) (sys_op1 : Nat) (sys_op2 : Nat) (t : Nat) (t2 : Nat) : SailM Unit := do
  if (read : Bool)
  then (AArch64_SysRegRead128 sys_op0 sys_op1 sys_crn sys_crm sys_op2 t t2)
  else (AArch64_SysRegWrite128 sys_op0 sys_op1 sys_crn sys_crm sys_op2 t t2)

/-- Type quantifiers: k_read : Bool, sys_crm : Nat, sys_crn : Nat, sys_op0 : Nat, sys_op1 : Nat, sys_op2 : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ List.elem sys_op2 [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem sys_op1 [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem sys_op0 [2, 3] ∧ 0 ≤ sys_crn ∧ sys_crn ≤ 15 ∧ 0 ≤ sys_crm ∧ sys_crm ≤ 15 -/
def execute_aarch64_instrs_system_register_system (read : Bool) (sys_crm : Nat) (sys_crn : Nat) (sys_op0 : Nat) (sys_op1 : Nat) (sys_op2 : Nat) (t : Nat) : SailM Unit := do
  if (read : Bool)
  then (AArch64_SysRegRead sys_op0 sys_op1 sys_crn sys_crm sys_op2 t)
  else (AArch64_SysRegWrite sys_op0 sys_op1 sys_crn sys_crm sys_op2 t)

def execute_aarch64_instrs_system_register_cpsr (field : PSTATEField) (operand : (BitVec 4)) : SailM Unit := do
  match field with
  | .PSTATEField_SSBS => writeReg PSTATE { (← readReg PSTATE) with SSBS := (BitVec.join1 [(BitVec.access operand 0)]) }
  | .PSTATEField_SP => writeReg PSTATE { (← readReg PSTATE) with SP := (BitVec.join1 [(BitVec.access operand 0)]) }
  | .PSTATEField_DAIFSet =>
    (do
      writeReg PSTATE { (← readReg PSTATE) with D := ← (do (pure ((← readReg PSTATE).D ||| (BitVec.join1 [(BitVec.access operand 3)])))) }
      writeReg PSTATE { (← readReg PSTATE) with A := ← (do (pure ((← readReg PSTATE).A ||| (BitVec.join1 [(BitVec.access operand 2)])))) }
      writeReg PSTATE { (← readReg PSTATE) with I := ← (do (pure ((← readReg PSTATE).I ||| (BitVec.join1 [(BitVec.access operand 1)])))) }
      writeReg PSTATE { (← readReg PSTATE) with F := ← (do (pure ((← readReg PSTATE).F ||| (BitVec.join1 [(BitVec.access operand 0)])))) })
  | .PSTATEField_DAIFClr =>
    (do
      writeReg PSTATE { (← readReg PSTATE) with D := ← (do (pure ((← readReg PSTATE).D &&& (Complement.complement (BitVec.join1 [(BitVec.access operand 3)]))))) }
      writeReg PSTATE { (← readReg PSTATE) with A := ← (do (pure ((← readReg PSTATE).A &&& (Complement.complement (BitVec.join1 [(BitVec.access operand 2)]))))) }
      writeReg PSTATE { (← readReg PSTATE) with I := ← (do (pure ((← readReg PSTATE).I &&& (Complement.complement (BitVec.join1 [(BitVec.access operand 1)]))))) }
      writeReg PSTATE { (← readReg PSTATE) with F := ← (do (pure ((← readReg PSTATE).F &&& (Complement.complement (BitVec.join1 [(BitVec.access operand 0)]))))) })
  | .PSTATEField_PAN => writeReg PSTATE { (← readReg PSTATE) with PAN := (BitVec.join1 [(BitVec.access operand 0)]) }
  | .PSTATEField_UAO => writeReg PSTATE { (← readReg PSTATE) with UAO := (BitVec.join1 [(BitVec.access operand 0)]) }
  | .PSTATEField_DIT => writeReg PSTATE { (← readReg PSTATE) with DIT := (BitVec.join1 [(BitVec.access operand 0)]) }
  | .PSTATEField_TCO => writeReg PSTATE { (← readReg PSTATE) with TCO := (BitVec.join1 [(BitVec.access operand 0)]) }
  | .PSTATEField_ALLINT =>
    (do
      if (((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (IsHCRXEL2Enabled ())) <&&> (do
             (pure ((_get_HCRX_EL2_Type_TALLINT (← readReg HCRX_EL2)) == 1#1))))) && ((BitVec.join1 [(BitVec.access operand 0)]) == 1#1)) : Bool)
      then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
      else (pure ())
      writeReg PSTATE { (← readReg PSTATE) with ALLINT := (BitVec.join1 [(BitVec.access operand 0)]) })
  | .PSTATEField_SVCRSM =>
    (do
      (CheckSMEAccess ())
      (SetPSTATE_SM (BitVec.join1 [(BitVec.access operand 0)])))
  | .PSTATEField_SVCRZA =>
    (do
      (CheckSMEAccess ())
      (SetPSTATE_ZA (BitVec.join1 [(BitVec.access operand 0)])))
  | .PSTATEField_SVCRSMZA =>
    (do
      (CheckSMEAccess ())
      (SetPSTATE_SM (BitVec.join1 [(BitVec.access operand 0)]))
      (SetPSTATE_ZA (BitVec.join1 [(BitVec.access operand 0)])))
  | .PSTATEField_PM => writeReg PSTATE { (← readReg PSTATE) with PM := (BitVec.join1 [(BitVec.access operand 0)]) }

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, k_poly : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (poly : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let product ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element2, product, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, product, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, product, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e esize)
        let element2 ← (Elem_read operand2 e esize)
        let product : (BitVec esize) :=
          if (poly : Bool)
          then (Sail.BitVec.extractLsb (PolynomialMult element1 element2) (esize -i 1) 0)
          else (integer_subrange ((BitVec.toNat element1) *i (BitVec.toNat element2)) (esize -i 1) 0)
        let result ← (Elem_set result e esize product)
        (pure (element1, element2, product, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem idxdsize [64, 128] ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_int (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m idxdsize) ) : SailM (BitVec idxdsize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let product ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← do (pure (BitVec.toNat (← (Elem_read operand2 index esize))))
  let (element1, product, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, product, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, product, result) := loop_vars
      loop_vars ← do
        let element1 ← (pure (BitVec.toNat (← (Elem_read operand1 e esize))))
        let product : (BitVec esize) := (integer_subrange (element1 *i element2) (esize -i 1) 0)
        let result ← (Elem_set result e esize product)
        (pure (element1, product, result))
    (pure loop_vars) ) : SailM (Int × (BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ esize = 8 ∧ List.elem elements [8, 16] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_not (d : Nat) (datasize : Nat) (elements : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e esize)
        let result ← (Elem_set result e esize (Complement.complement element))
        (pure (element, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_pacda_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  if (source_is_sp : Bool)
  then (X_set d 64 (← (AddPACDA (← (X_read d 64)) (← (SP_read ())))))
  else (X_set d 64 (← (AddPACDA (← (X_read d 64)) (← (X_read n 64)))))

/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_pacdb_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  if (source_is_sp : Bool)
  then (X_set d 64 (← (AddPACDB (← (X_read d 64)) (← (SP_read ())))))
  else (X_set d 64 (← (AddPACDB (← (X_read d 64)) (← (X_read n 64)))))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_pacga_dp_2src (d : Nat) (m : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  if (source_is_sp : Bool)
  then (X_set d 64 (← (AddPACGA (← (X_read n 64)) (← (SP_read ())))))
  else (X_set d 64 (← (AddPACGA (← (X_read n 64)) (← (X_read m 64)))))

/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_pacia_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  if ((← (HavePACExt ())) : Bool)
  then
    (do
      if (source_is_sp : Bool)
      then (X_set d 64 (← (AddPACIA (← (X_read d 64)) (← (SP_read ())))))
      else (X_set d 64 (← (AddPACIA (← (X_read d 64)) (← (X_read n 64))))))
  else (pure ())

/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_pacib_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  if ((← (HavePACExt ())) : Bool)
  then
    (do
      if (source_is_sp : Bool)
      then (X_set d 64 (← (AddPACIB (← (X_read d 64)) (← (SP_read ())))))
      else (X_set d 64 (← (AddPACIB (← (X_read d 64)) (← (X_read n 64))))))
  else (pure ())

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (Vpart_read n part datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (Vpart_read m part datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let element2 ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let element1 ← (Elem_read operand1 e esize)
        let element2 ← (Elem_read operand2 e esize)
        let result ← (Elem_set result e (2 *i esize) (PolynomialMult element1 element2))
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec (2 * datasize))) )
  (V_set d (2 *i datasize) result)

/-- Type quantifiers: datasize : Nat, k_is_signed : Bool, n : Nat, k_nontemporal : Bool, k_postindex : Bool, regsize : Nat, k_rt_unknown : Bool, t : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback : Bool, 0 ≤ t ∧ t ≤ 31 ∧ List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_single_general_immediate_unsigned (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (regsize : Nat) (rt_unknown : Bool) (is_signed : Bool) (t : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let privileged ← (( do (pure ((← readReg PSTATE).EL != EL0)) ) : SailM Bool )
  let accdesc ← (( do (CreateAccDescGPR memop nontemporal privileged tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        if ((bne memop MemOp_PREFETCH) : Bool)
        then (CheckSPAlignment ())
        else (pure ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      let data ← (( do
        if (rt_unknown : Bool)
        then (do (__UNKNOWN_bits datasize))
        else (do (X_read t datasize)) ) : SailM (BitVec datasize) )
      let _ : Unit :=
        if ((! wback) : Bool)
        then (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) false t (regsize == 64) false)
        else ()
      (Mem_set address (Int.ediv datasize 8) accdesc data))
  | .MemOp_LOAD =>
    (do
      let _ : Unit :=
        if ((! wback) : Bool)
        then (AArch64_SetLSInstructionSyndrome (Int.ediv datasize 8) is_signed t (regsize == 64) false)
        else ()
      let data ← (( do (Mem_read address (Int.ediv datasize 8) accdesc) ) : SailM (BitVec datasize) )
      if (is_signed : Bool)
      then
        (do
          sail_assert ((datasize >b 0) && (regsize ≥b datasize)) "src/instrs64.sail:39819.72-39819.73"
          (X_set t regsize (sign_extend data regsize)))
      else
        (do
          sail_assert ((datasize ≥b 0) && (regsize ≥b datasize)) "src/instrs64.sail:39822.73-39822.74"
          (X_set t regsize (Sail.BitVec.zeroExtend data regsize))))
  | .MemOp_PREFETCH => (Prefetch address (integer_subrange t 4 0))
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then (do (__UNKNOWN_bits 64))
        else
          (if (postindex : Bool)
          then (pure (address + offset))
          else (pure address)) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleGeneralPurposeLoadStore ())
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3_rax1 (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  (V_set d 128 (Vn ^^^ ((← (ROL (Sail.BitVec.extractLsb Vm 127 64) 1)) +++ (← (ROL (Sail.BitVec.extractLsb Vm 63 0) 1)))))

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ esize = 8 ∧ List.elem elements [8, 16] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_rbit (d : Nat) (datasize : Nat) (elements : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let rev ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element, result, rev) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result, rev)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result, rev) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e esize)
        let rev ← (( do
          let loop_i_lower := 0
          let loop_i_upper := (esize -i 1)
          let mut loop_vars_1 := rev
          for i in [loop_i_lower:loop_i_upper:1]i do
            let rev := loop_vars_1
            loop_vars_1 := (BitVec.update rev ((esize -i 1) -i i) (Bit (BitVec.join1 [(BitVec.access element i)])))
          (pure loop_vars_1) ) : SailM (BitVec esize) )
        let result ← (Elem_set result e esize rev)
        (pure (element, result, rev))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec datasize) × (BitVec esize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_rbit (d : Nat) (datasize : Nat) (n : Nat) : SailM Unit := do
  let operand ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (datasize -i 1)
    let mut loop_vars := result
    for i in [loop_i_lower:loop_i_upper:1]i do
      let result := loop_vars
      loop_vars := (BitVec.update result ((datasize -i 1) -i i) (Bit (BitVec.join1 [(BitVec.access operand i)])))
    (pure loop_vars) ) : SailM (BitVec datasize) )
  (X_set d datasize result)

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcw_cas (acquire : Bool) (n : Nat) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  if ((← (IsD128Enabled (← readReg PSTATE).EL)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let newdata ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let compdata ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW MemAtomicOp_CAS soft acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let (nzcv, readdata) ← (( do
    let (tup__0, tup__1) ← do (MemAtomicRCW address compdata newdata accdesc)
    let nzcv : (BitVec 4) := tup__0
    let readdata : (BitVec 64) := tup__1
    (pure (nzcv, readdata)) ) : SailM ((BitVec 4) × (BitVec 64)) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  (X_set s 64 readdata)

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcw_cas_128 (acquire : Bool) (n : Nat) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  if ((! (← (IsD128Enabled (← readReg PSTATE).EL))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let s1 ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let s2 ← (( do (X_read (s +i 1) 64) ) : SailM (BitVec 64) )
  let t1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let t2 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescRCW MemAtomicOp_CAS soft acquire release tagchecked) ) : SailM AccessDescriptor )
  let compdata ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (s1 +++ s2))
    else (pure (s2 +++ s1)) ) : SailM (BitVec 128) )
  let newdata ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (t1 +++ t2))
    else (pure (t2 +++ t1)) ) : SailM (BitVec 128) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let (nzcv, readdata) ← (( do
    let (tup__0, tup__1) ← do (MemAtomicRCW address compdata newdata accdesc)
    let nzcv : (BitVec 4) := tup__0
    let readdata : (BitVec 128) := tup__1
    (pure (nzcv, readdata)) ) : SailM ((BitVec 4) × (BitVec 128)) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  if ((← (BigEndian accdesc.acctype)) : Bool)
  then
    (do
      (X_set s 64 (Sail.BitVec.extractLsb readdata 127 64))
      (X_set (s +i 1) 64 (Sail.BitVec.extractLsb readdata 63 0)))
  else
    (do
      (X_set s 64 (Sail.BitVec.extractLsb readdata 63 0))
      (X_set (s +i 1) 64 (Sail.BitVec.extractLsb readdata 127 64)))

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcw_ld_rcwclr (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  if ((← (IsD128Enabled (← readReg PSTATE).EL)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let newdata ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW op soft acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let compdata ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  let (nzcv, readdata) ← (( do
    let (tup__0, tup__1) ← do (MemAtomicRCW address compdata newdata accdesc)
    let nzcv : (BitVec 4) := tup__0
    let readdata : (BitVec 64) := tup__1
    (pure (nzcv, readdata)) ) : SailM ((BitVec 4) × (BitVec 64)) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  (X_set t 64 readdata)

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, k_soft : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcw_ld_128_rcwclrp (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (soft : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  if ((! (← (IsD128Enabled (← readReg PSTATE).EL))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW op soft acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let value1_name ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value2_name ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let newdata ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (value1_name +++ value2_name))
    else (pure (value2_name +++ value1_name)) ) : SailM (BitVec 128) )
  let compdata ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
  let (nzcv, readdata) ← (( do
    let (tup__0, tup__1) ← do (MemAtomicRCW address compdata newdata accdesc)
    let nzcv : (BitVec 4) := tup__0
    let readdata : (BitVec 128) := tup__1
    (pure (nzcv, readdata)) ) : SailM ((BitVec 4) × (BitVec 128)) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  if ((← (BigEndian accdesc.acctype)) : Bool)
  then
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 127 64))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 63 0)))
  else
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 63 0))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 127 64)))

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcws_cas (acquire : Bool) (n : Nat) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  if ((← (IsD128Enabled (← readReg PSTATE).EL)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let newdata ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let compdata ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW MemAtomicOp_CAS soft acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let (nzcv, readdata) ← (( do
    let (tup__0, tup__1) ← do (MemAtomicRCW address compdata newdata accdesc)
    let nzcv : (BitVec 4) := tup__0
    let readdata : (BitVec 64) := tup__1
    (pure (nzcv, readdata)) ) : SailM ((BitVec 4) × (BitVec 64)) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  (X_set s 64 readdata)

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcws_cas_128 (acquire : Bool) (n : Nat) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  if ((! (← (IsD128Enabled (← readReg PSTATE).EL))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let s1 ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let s2 ← (( do (X_read (s +i 1) 64) ) : SailM (BitVec 64) )
  let t1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let t2 ← (( do (X_read (t +i 1) 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescRCW MemAtomicOp_CAS soft acquire release tagchecked) ) : SailM AccessDescriptor )
  let compdata ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (s1 +++ s2))
    else (pure (s2 +++ s1)) ) : SailM (BitVec 128) )
  let newdata ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (t1 +++ t2))
    else (pure (t2 +++ t1)) ) : SailM (BitVec 128) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let (nzcv, readdata) ← (( do
    let (tup__0, tup__1) ← do (MemAtomicRCW address compdata newdata accdesc)
    let nzcv : (BitVec 4) := tup__0
    let readdata : (BitVec 128) := tup__1
    (pure (nzcv, readdata)) ) : SailM ((BitVec 4) × (BitVec 128)) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  if ((← (BigEndian accdesc.acctype)) : Bool)
  then
    (do
      (X_set s 64 (Sail.BitVec.extractLsb readdata 127 64))
      (X_set (s +i 1) 64 (Sail.BitVec.extractLsb readdata 63 0)))
  else
    (do
      (X_set s 64 (Sail.BitVec.extractLsb readdata 63 0))
      (X_set (s +i 1) 64 (Sail.BitVec.extractLsb readdata 127 64)))

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcws_ld_rcwsclr (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  if ((← (IsD128Enabled (← readReg PSTATE).EL)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let newdata ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW op soft acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let compdata ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  let (nzcv, readdata) ← (( do
    let (tup__0, tup__1) ← do (MemAtomicRCW address compdata newdata accdesc)
    let nzcv : (BitVec 4) := tup__0
    let readdata : (BitVec 64) := tup__1
    (pure (nzcv, readdata)) ) : SailM ((BitVec 4) × (BitVec 64)) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  (X_set t 64 readdata)

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, k_soft : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcws_ld_128_rcwsclrp (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (soft : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  if ((! (← (IsD128Enabled (← readReg PSTATE).EL))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW op soft acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let value1_name ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value2_name ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let newdata ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (value1_name +++ value2_name))
    else (pure (value2_name +++ value1_name)) ) : SailM (BitVec 128) )
  let compdata ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
  let (nzcv, readdata) ← (( do
    let (tup__0, tup__1) ← do (MemAtomicRCW address compdata newdata accdesc)
    let nzcv : (BitVec 4) := tup__0
    let readdata : (BitVec 128) := tup__1
    (pure (nzcv, readdata)) ) : SailM ((BitVec 4) × (BitVec 128)) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  if ((← (BigEndian accdesc.acctype)) : Bool)
  then
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 127 64))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 63 0)))
  else
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 63 0))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 127 64)))

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcw_ld_rcwset (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  if ((← (IsD128Enabled (← readReg PSTATE).EL)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let newdata ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW op soft acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let compdata ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  let (nzcv, readdata) ← (( do
    let (tup__0, tup__1) ← do (MemAtomicRCW address compdata newdata accdesc)
    let nzcv : (BitVec 4) := tup__0
    let readdata : (BitVec 64) := tup__1
    (pure (nzcv, readdata)) ) : SailM ((BitVec 4) × (BitVec 64)) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  (X_set t 64 readdata)

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, k_soft : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcw_ld_128_rcwsetp (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (soft : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  if ((! (← (IsD128Enabled (← readReg PSTATE).EL))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW op soft acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let value1_name ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value2_name ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let newdata ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (value1_name +++ value2_name))
    else (pure (value2_name +++ value1_name)) ) : SailM (BitVec 128) )
  let compdata ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
  let (nzcv, readdata) ← (( do
    let (tup__0, tup__1) ← do (MemAtomicRCW address compdata newdata accdesc)
    let nzcv : (BitVec 4) := tup__0
    let readdata : (BitVec 128) := tup__1
    (pure (nzcv, readdata)) ) : SailM ((BitVec 4) × (BitVec 128)) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  if ((← (BigEndian accdesc.acctype)) : Bool)
  then
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 127 64))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 63 0)))
  else
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 63 0))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 127 64)))

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcws_ld_rcwsset (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  if ((← (IsD128Enabled (← readReg PSTATE).EL)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let newdata ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW op soft acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let compdata ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  let (nzcv, readdata) ← (( do
    let (tup__0, tup__1) ← do (MemAtomicRCW address compdata newdata accdesc)
    let nzcv : (BitVec 4) := tup__0
    let readdata : (BitVec 64) := tup__1
    (pure (nzcv, readdata)) ) : SailM ((BitVec 4) × (BitVec 64)) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  (X_set t 64 readdata)

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, k_soft : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcws_ld_128_rcwssetp (acquire : Bool) (n : Nat) (op : MemAtomicOp) (release : Bool) (soft : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  if ((! (← (IsD128Enabled (← readReg PSTATE).EL))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW op soft acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let value1_name ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value2_name ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let newdata ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (value1_name +++ value2_name))
    else (pure (value2_name +++ value1_name)) ) : SailM (BitVec 128) )
  let compdata ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
  let (nzcv, readdata) ← (( do
    let (tup__0, tup__1) ← do (MemAtomicRCW address compdata newdata accdesc)
    let nzcv : (BitVec 4) := tup__0
    let readdata : (BitVec 128) := tup__1
    (pure (nzcv, readdata)) ) : SailM ((BitVec 4) × (BitVec 128)) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  if ((← (BigEndian accdesc.acctype)) : Bool)
  then
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 127 64))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 63 0)))
  else
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 63 0))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 127 64)))

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcws_swp (acquire : Bool) (n : Nat) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  if ((← (IsD128Enabled (← readReg PSTATE).EL)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let newdata ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW MemAtomicOp_SWP soft acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let compdata ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  let (nzcv, readdata) ← (( do
    let (tup__0, tup__1) ← do (MemAtomicRCW address compdata newdata accdesc)
    let nzcv : (BitVec 4) := tup__0
    let readdata : (BitVec 64) := tup__1
    (pure (nzcv, readdata)) ) : SailM ((BitVec 4) × (BitVec 64)) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  (X_set t 64 readdata)

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, k_soft : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcws_swp_128 (acquire : Bool) (n : Nat) (release : Bool) (soft : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  if ((! (← (IsD128Enabled (← readReg PSTATE).EL))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW MemAtomicOp_SWP soft acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let value1_name ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value2_name ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let newdata ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (value1_name +++ value2_name))
    else (pure (value2_name +++ value1_name)) ) : SailM (BitVec 128) )
  let compdata ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
  let (nzcv, readdata) ← (( do
    let (tup__0, tup__1) ← do (MemAtomicRCW address compdata newdata accdesc)
    let nzcv : (BitVec 4) := tup__0
    let readdata : (BitVec 128) := tup__1
    (pure (nzcv, readdata)) ) : SailM ((BitVec 4) × (BitVec 128)) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  if ((← (BigEndian accdesc.acctype)) : Bool)
  then
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 127 64))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 63 0)))
  else
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 63 0))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 127 64)))

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, s : Nat, k_soft : Bool, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcw_swp (acquire : Bool) (n : Nat) (release : Bool) (s : Nat) (soft : Bool) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  if ((← (IsD128Enabled (← readReg PSTATE).EL)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let newdata ← (( do (X_read s 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW MemAtomicOp_SWP soft acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let compdata ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  let (nzcv, readdata) ← (( do
    let (tup__0, tup__1) ← do (MemAtomicRCW address compdata newdata accdesc)
    let nzcv : (BitVec 4) := tup__0
    let readdata : (BitVec 64) := tup__1
    (pure (nzcv, readdata)) ) : SailM ((BitVec 4) × (BitVec 64)) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  (X_set t 64 readdata)

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, k_soft : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_rcw_swp_128 (acquire : Bool) (n : Nat) (release : Bool) (soft : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  if ((! (← (IsD128Enabled (← readReg PSTATE).EL))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let readdata ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let accdesc ← (( do (CreateAccDescRCW MemAtomicOp_SWP soft acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let value1_name ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value2_name ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let newdata ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (value1_name +++ value2_name))
    else (pure (value2_name +++ value1_name)) ) : SailM (BitVec 128) )
  let compdata ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
  let (nzcv, readdata) ← (( do
    let (tup__0, tup__1) ← do (MemAtomicRCW address compdata newdata accdesc)
    let nzcv : (BitVec 4) := tup__0
    let readdata : (BitVec 128) := tup__1
    (pure (nzcv, readdata)) ) : SailM ((BitVec 4) × (BitVec 128)) )
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) }
  if ((← (BigEndian accdesc.acctype)) : Bool)
  then
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 127 64))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 63 0)))
  else
    (do
      (X_set t 64 (Sail.BitVec.extractLsb readdata 63 0))
      (X_set t2 64 (Sail.BitVec.extractLsb readdata 127 64)))

/-- Type quantifiers: container_size : Nat, d : Nat, datasize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem container_size [16, 32, 64] -/
def execute_aarch64_instrs_integer_arithmetic_rev (container_size : Nat) (d : Nat) (datasize : Nat) (n : Nat) : SailM Unit := do
  let operand ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let containers := (Int.ediv datasize container_size)
  let elements_per_container := (Int.ediv container_size 8)
  let index : Int := 0
  let rev_index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, result, rev_index) ← (( do
    let loop_c_lower := 0
    let loop_c_upper := (containers -i 1)
    let mut loop_vars := (index, result, rev_index)
    for c in [loop_c_lower:loop_c_upper:1]i do
      let (index, result, rev_index) := loop_vars
      loop_vars ← do
        let rev_index : Int := (index +i ((elements_per_container -i 1) *i 8))
        let (index, result, rev_index) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements_per_container -i 1)
          let mut loop_vars_1 := (index, result, rev_index)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (index, result, rev_index) := loop_vars_1
            loop_vars_1 ← do
              let result ← (( do
                let rev_index := rev_index
                let index := index
                sail_assert ((0 ≤b rev_index) && ((rev_index +i 7) <b datasize)) "src/instrs64.sail:41065.83-41065.84"
                sail_assert ((0 ≤b index) && ((index +i 7) <b datasize)) "src/instrs64.sail:41066.75-41066.76"
                (pure (Sail.BitVec.updateSubrange result (rev_index +i 7) rev_index (Sail.BitVec.extractLsb operand (index +i 7) index))) ) : SailM (BitVec datasize) )
              let index : Int := (index +i 8)
              let rev_index : Int := (rev_index -i 8)
              (pure (index, result, rev_index))
          (pure loop_vars_1) ) : SailM (Int × (BitVec datasize) × Int) )
        (pure (index, result, rev_index))
    (pure loop_vars) ) : SailM (Int × (BitVec datasize) × Int) )
  (X_set d datasize result)

/-- Type quantifiers: containers : Int, d : Nat, datasize : Nat, elements_per_container : Int, esize : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_rev (containers : Int) (d : Nat) (datasize : Nat) (elements_per_container : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element : Int := 0
  let rev_element ← (( do (undefined_int ()) ) : SailM Int )
  let (element, result, rev_element) ← (( do
    let loop_c_lower := 0
    let loop_c_upper := (containers -i 1)
    let mut loop_vars := (element, result, rev_element)
    for c in [loop_c_lower:loop_c_upper:1]i do
      let (element, result, rev_element) := loop_vars
      loop_vars ← do
        let rev_element : Int := ((element +i elements_per_container) -i 1)
        let (element, result, rev_element) ← (( do
          let loop_e_lower := 0
          let loop_e_upper := (elements_per_container -i 1)
          let mut loop_vars_1 := (element, result, rev_element)
          for e in [loop_e_lower:loop_e_upper:1]i do
            let (element, result, rev_element) := loop_vars_1
            loop_vars_1 ← do
              let result ← (( do
                let rev_element := rev_element
                let element := element
                (Elem_set result rev_element esize (← (Elem_read operand element esize))) ) : SailM (BitVec datasize) )
              let element : Int := (element +i 1)
              let rev_element : Int := (rev_element -i 1)
              (pure (element, result, rev_element))
          (pure loop_vars_1) ) : SailM (Int × (BitVec datasize) × Int) )
        (pure (element, result, rev_element))
    (pure loop_vars) ) : SailM (Int × (BitVec datasize) × Int) )
  (V_set d datasize result)

/-- Type quantifiers: lsb : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ lsb ∧ lsb ≤ 63 -/
def execute_aarch64_instrs_integer_flags_rmif (lsb : Nat) (mask : (BitVec 4)) (n : Nat) : SailM Unit := do
  let tmpreg ← (( do (X_read n 64) ) : SailM (BitVec 64) )
  let tmp : (BitVec 4) := (Sail.BitVec.extractLsb (tmpreg +++ tmpreg) (lsb +i 3) lsb)
  if (((BitVec.join1 [(BitVec.access mask 3)]) == 1#1) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access tmp 3)]) }
  else (pure ())
  if (((BitVec.join1 [(BitVec.access mask 2)]) == 1#1) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with Z := (BitVec.join1 [(BitVec.access tmp 2)]) }
  else (pure ())
  if (((BitVec.join1 [(BitVec.access mask 1)]) == 1#1) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with C := (BitVec.join1 [(BitVec.access tmp 1)]) }
  else (pure ())
  if (((BitVec.join1 [(BitVec.access mask 0)]) == 1#1) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with V := (BitVec.join1 [(BitVec.access tmp 0)]) }
  else (pure ())

/-- Type quantifiers: m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 -/
def execute_aarch64_instrs_memory_single_general_range (m : Nat) (n : Nat) (operation : (BitVec 6)) : SailM Unit := do
  let address ← (( do
    if ((n == 31) : Bool)
    then (SP_read ())
    else (X_read n 64) ) : SailM (BitVec 64) )
  let metadata ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let stride := (BitVec.toInt (Sail.BitVec.extractLsb metadata 59 38))
  let count := ((BitVec.toNat (Sail.BitVec.extractLsb metadata 37 22)) +i 1)
  let length := (BitVec.toInt (Sail.BitVec.extractLsb metadata 21 0))
  let reuse ← (( do (undefined_int ()) ) : SailM Int )
  let reuse : Int :=
    if (((Sail.BitVec.extractLsb metadata 63 60) == 0b0000#4) : Bool)
    then (Neg.neg 1)
    else (Int.shiftl 32768 (15 -i (BitVec.toNat (Sail.BitVec.extractLsb metadata 63 60))))
  let reuse := reuse
  (pure (Hint_RangePrefetch address length stride count reuse operation))

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, part : Nat, k_round : Bool, shift : Int, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [4, 8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_right_narrow_logical (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) (round : Bool) (shift : Int) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n (datasize *i 2)) ) : SailM (BitVec (datasize * 2)) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int ()) ) : SailM Int )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (RShr (BitVec.toNat (← (Elem_read operand e (2 *i esize)))) shift round)
        let result ← (Elem_set result e esize (integer_subrange element (esize -i 1) 0))
        (pure (element, result))
    (pure loop_vars) ) : SailM (Int × (BitVec datasize)) )
  (Vpart_set d part datasize result)

/-- Type quantifiers: k_accumulate : Bool, d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff (accumulate : Bool) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let absdiff ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let result ← (( do
    if (accumulate : Bool)
    then (V_read d datasize)
    else (pure (Zeros (n := datasize))) ) : SailM (BitVec datasize) )
  let (absdiff, element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (absdiff, element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (absdiff, element1, element2, result) := loop_vars
      loop_vars ← do
        let element1 ← (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let absdiff : (BitVec esize) := (integer_subrange (Int.natAbs (element1 -i element2)) (esize -i 1) 0)
        let result ← (Elem_set result e esize ((← (Elem_read result e esize)) + absdiff))
        (pure (absdiff, element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × Int × Int × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: k_accumulate : Bool, d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff (accumulate : Bool) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (Vpart_read n part datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (Vpart_read m part datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let absdiff ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  let result ← (( do
    if (accumulate : Bool)
    then (V_read d (2 *i datasize))
    else (pure (Zeros (n := (2 *i datasize)))) ) : SailM (BitVec (2 * datasize)) )
  let (absdiff, element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (absdiff, element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (absdiff, element1, element2, result) := loop_vars
      loop_vars ← do
        let element1 ← (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let absdiff : (BitVec (2 * esize)) := (integer_subrange (Int.natAbs (element1 -i element2)) ((2 *i esize) -i 1) 0)
        let result ← (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) + absdiff))
        (pure (absdiff, element1, element2, result))
    (pure loop_vars) ) : SailM ((BitVec (2 * esize)) × Int × Int × (BitVec (2 * datasize))) )
  (V_set d (2 *i datasize) result)

/-- Type quantifiers: k_acc : Bool, d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise (acc : Bool) (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let sum ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  let op1 ← (( do (undefined_int ()) ) : SailM Int )
  let op2 ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do
    if (acc : Bool)
    then (do (V_read d datasize))
    else (pure result) ) : SailM (BitVec datasize) )
  let (op1, op2, result, sum) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (op1, op2, result, sum)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (op1, op2, result, sum) := loop_vars
      loop_vars ← do
        let op1 ← (asl_Int (← (Elem_read operand ((2 *i e) +i 0) esize)) is_unsigned)
        let op2 ← (asl_Int (← (Elem_read operand ((2 *i e) +i 1) esize)) is_unsigned)
        let sum : (BitVec (2 * esize)) := (integer_subrange (op1 +i op2) ((2 *i esize) -i 1) 0)
        let result ← (( do
          if (acc : Bool)
          then (do (Elem_set result e (2 *i esize) ((← (Elem_read result e (2 *i esize))) + sum)))
          else (do (Elem_set result e (2 *i esize) sum)) ) : SailM (BitVec datasize) )
        (pure (op1, op2, result, sum))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec datasize) × (BitVec (2 * esize))) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, part : Nat, k_sub_op : Bool, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (Vpart_read n part datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (Vpart_read m part datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let sum ← (( do (undefined_int ()) ) : SailM Int )
  let (element1, element2, result, sum) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result, sum)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result, sum) := loop_vars
      loop_vars ← do
        let element1 ← (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let sum : Int :=
          if (sub_op : Bool)
          then (element1 -i element2)
          else (element1 +i element2)
        let result ← (Elem_set result e (2 *i esize) (integer_subrange sum ((2 *i esize) -i 1) 0))
        (pure (element1, element2, result, sum))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec (2 * datasize)) × Int) )
  (V_set d (2 *i datasize) result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_reduce_add_long (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let sum ← (( do (asl_Int (← (Elem_read operand 0 esize)) is_unsigned) ) : SailM Int )
  let sum ← (( do
    let loop_e_lower := 1
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := sum
    for e in [loop_e_lower:loop_e_upper:1]i do
      let sum := loop_vars
      loop_vars ← do (pure (sum +i (← (asl_Int (← (Elem_read operand e esize)) is_unsigned))))
    (pure loop_vars) ) : SailM Int )
  let sum := sum
  (V_set d (2 *i esize) (integer_subrange sum ((2 *i esize) -i 1) 0))

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, part : Nat, k_sub_op : Bool, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let operand2 ← (( do (Vpart_read m part datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let sum ← (( do (undefined_int ()) ) : SailM Int )
  let (element1, element2, result, sum) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result, sum)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result, sum) := loop_vars
      loop_vars ← do
        let element1 ← (asl_Int (← (Elem_read operand1 e (2 *i esize))) is_unsigned)
        let element2 ← (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let sum : Int :=
          if (sub_op : Bool)
          then (element1 -i element2)
          else (element1 +i element2)
        let result ← (Elem_set result e (2 *i esize) (integer_subrange sum ((2 *i esize) -i 1) 0))
        (pure (element1, element2, result, sum))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec (2 * datasize)) × Int) )
  (V_set d (2 *i datasize) result)

def execute_aarch64_instrs_system_barriers_sb (_ : Unit) : SailM Unit := do
  (SpeculationBarrier ())

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, fracbits : Int, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_conv_int_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (fracbits : Int) (n : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (pure (elements == 1)) <&&> (do (IsMerging fpcr)) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read d 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e esize)
        let result ← (Elem_set result e esize (← (FixedToFP element fracbits is_unsigned fpcr rounding esize)))
        (pure (element, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (pure (elements == 1)) <&&> (do (IsMerging fpcr)) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then (V_read d 128)
    else (pure (Zeros (n := 128))) ) : SailM (BitVec 128) )
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let element ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e esize)
        let result ← (Elem_set result e esize (← (FixedToFP element 0 is_unsigned fpcr rounding esize)))
        (pure (element, result))
    (pure loop_vars) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, datasize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_div (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (X_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do
    if ((IsZero operand2) : Bool)
    then (pure 0)
    else (do (pure (RoundTowardsZero (div_real (to_real (← (asl_Int operand1 is_unsigned))) (to_real (← (asl_Int operand2 is_unsigned))))))) ) : SailM Int )
  let result := result
  (X_set d datasize (integer_subrange result (datasize -i 1) 0))

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_signed : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (is_signed : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let res : Int := 0
        let element1 ← (( do (undefined_int ()) ) : SailM Int )
        let element2 ← (( do (undefined_int ()) ) : SailM Int )
        let (element1, element2, res) ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 3
          let mut loop_vars_1 := (element1, element2, res)
          for i in [loop_i_lower:loop_i_upper:1]i do
            let (element1, element2, res) := loop_vars_1
            loop_vars_1 ← do
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
          (pure loop_vars_1) ) : SailM (Int × Int × Int) )
        let res := res
        (Elem_set result e esize (BitVec.addInt (← (Elem_read result e esize)) res))
    (pure loop_vars) ) : SailM (BitVec datasize) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, index : Nat, k_is_signed : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_dotp (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (is_signed : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let result ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let res : Int := 0
        let element1 ← (( do (undefined_int ()) ) : SailM Int )
        let element2 ← (( do (undefined_int ()) ) : SailM Int )
        let (element1, element2, res) ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 3
          let mut loop_vars_1 := (element1, element2, res)
          for i in [loop_i_lower:loop_i_upper:1]i do
            let (element1, element2, res) := loop_vars_1
            loop_vars_1 ← do
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
          (pure loop_vars_1) ) : SailM (Int × Int × Int) )
        let res := res
        (Elem_set result e esize (BitVec.addInt (← (Elem_read result e esize)) res))
    (pure loop_vars) ) : SailM (BitVec datasize) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, n : Nat, s : Nat, 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_memory_mcpymset_set (d : Nat) (n : Nat) (options_name : (BitVec 2)) (s : Nat) (stage : MOPSStage) : SailM Unit := do
  let toaddress ← (( do (X_read d 64) ) : SailM (BitVec 64) )
  let setsize ← (( do (X_read n 64) ) : SailM (BitVec 64) )
  let data ← (( do (X_read s 8) ) : SailM (BitVec 8) )
  let nzcv ← (( do (pure ((← readReg PSTATE).N +++ ((← readReg PSTATE).Z +++ ((← readReg PSTATE).C +++ (← readReg PSTATE).V)))) ) : SailM (BitVec 4) )
  let stagesetsize ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let is_setg : Bool := false
  let B ← (( do (undefined_int ()) ) : SailM Int )
  let supports_option_a ← (( do (SETOptionA ()) ) : SailM Bool )
  let privileged ← (( do
    if (((BitVec.join1 [(BitVec.access options_name 0)]) == 1#1) : Bool)
    then (AArch64_IsUnprivAccessPriv ())
    else (pure ((← readReg PSTATE).EL != EL0)) ) : SailM Bool )
  let nontemporal : Bool := ((BitVec.join1 [(BitVec.access options_name 1)]) == 1#1)
  let accdesc ← (( do (CreateAccDescMOPS MemOp_STORE privileged nontemporal) ) : SailM AccessDescriptor )
  let (nzcv, setsize, stagesetsize, toaddress) ← (( do
    if ((BEq.beq stage MOPSStage_Prologue) : Bool)
    then
      (do
        let setsize : (BitVec 64) :=
          if (((BitVec.join1 [(BitVec.access setsize 63)]) == 1#1) : Bool)
          then 0x7FFFFFFFFFFFFFFF#64
          else setsize
        let (nzcv, setsize, toaddress) : ((BitVec 4) × (BitVec 64) × (BitVec 64)) :=
          if (supports_option_a : Bool)
          then
            (let nzcv : (BitVec 4) := 0b0000#4
            let toaddress : (BitVec 64) := (toaddress + setsize)
            let setsize : (BitVec 64) := ((Zeros (n := 64)) - setsize)
            (nzcv, setsize, toaddress))
          else
            (let nzcv : (BitVec 4) := 0b0010#4
            (nzcv, setsize, toaddress))
        let stagesetsize ← (SETPreSizeChoice toaddress setsize is_setg)
        sail_assert (((BitVec.join1 [(BitVec.access stagesetsize 63)]) == (BitVec.join1 [(BitVec.access setsize 63)])) || (stagesetsize == (Zeros (n := 64)))) "src/instrs64.sail:42994.78-42994.79"
        if (((BitVec.toInt setsize) >b 0) : Bool)
        then sail_assert ((BitVec.toInt stagesetsize) ≤b (BitVec.toInt setsize)) "src/instrs64.sail:42996.54-42996.55"
        else sail_assert ((BitVec.toInt stagesetsize) ≥b (BitVec.toInt setsize)) "src/instrs64.sail:42998.54-42998.55"
        (pure (nzcv, setsize, stagesetsize, toaddress)))
    else
      (do
        let postsize ← (( do (SETPostSizeChoice toaddress setsize is_setg) ) : SailM (BitVec 64) )
        sail_assert (((BitVec.join1 [(BitVec.access postsize 63)]) == (BitVec.join1 [(BitVec.access setsize 63)])) || (postsize == (Zeros (n := 64)))) "src/instrs64.sail:43002.70-43002.71"
        let zero_size_exceptions ← (( do (MemSetZeroSizeCheck ()) ) : SailM Bool )
        if ((zero_size_exceptions || (((BitVec.toInt setsize) != 0) : Bool)) : Bool)
        then
          (do
            if (supports_option_a : Bool)
            then
              (do
                if (((BitVec.join1 [(BitVec.access nzcv 1)]) == 1#1) : Bool)
                then
                  (do
                    let wrong_option : Bool := true
                    let from_epilogue : Bool := (BEq.beq stage MOPSStage_Epilogue)
                    (MismatchedMemSetException supports_option_a d s n wrong_option from_epilogue options_name is_setg))
                else (pure ()))
            else
              (do
                if (((BitVec.join1 [(BitVec.access nzcv 1)]) == 0#1) : Bool)
                then
                  (do
                    let wrong_option : Bool := true
                    let from_epilogue : Bool := (BEq.beq stage MOPSStage_Epilogue)
                    (MismatchedMemSetException supports_option_a d s n wrong_option from_epilogue options_name is_setg))
                else (pure ())))
        else (pure ())
        let stagesetsize ← (( do
          if ((BEq.beq stage MOPSStage_Main) : Bool)
          then
            (do
              let stagesetsize : (BitVec 64) := (setsize - postsize)
              if ((← (MemSetParametersIllformedM toaddress setsize is_setg)) : Bool)
              then
                (do
                  let wrong_option : Bool := false
                  let from_epilogue : Bool := false
                  (MismatchedMemSetException supports_option_a d s n wrong_option from_epilogue options_name is_setg))
              else (pure ())
              (pure stagesetsize))
          else
            (do
              let stagesetsize : (BitVec 64) := postsize
              if ((←((pure (setsize != postsize)) <||> (do
                   (MemSetParametersIllformedE toaddress setsize is_setg)))) : Bool)
              then
                (do
                  let wrong_option : Bool := false
                  let from_epilogue : Bool := true
                  (MismatchedMemSetException supports_option_a d s n wrong_option from_epilogue options_name is_setg))
              else (pure ())
              (pure stagesetsize)) ) : SailM (BitVec 64) )
        (pure (nzcv, setsize, stagesetsize, toaddress))) ) : SailM ((BitVec 4) × (BitVec 64) × (BitVec 64) × (BitVec 64)) )
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleMemSet ())
  else (pure ())
  let (setsize, toaddress) ← (( do
    if (supports_option_a : Bool)
    then
      (do
        let (B, setsize, stagesetsize) ← (( do
          let mut loop_vars_1 := (B, setsize, stagesetsize)
          while (λ (B, setsize, stagesetsize) => ((BitVec.toInt stagesetsize) <b 0)) loop_vars_1 do
            let (B, setsize, stagesetsize) := loop_vars_1
            loop_vars_1 ← do
              let B ← (SETSizeChoice toaddress setsize 1)
              sail_assert (B ≤b ((Neg.neg 1) *i (BitVec.toInt stagesetsize))) "src/instrs64.sail:43045.54-43045.55"
              let B := B
              sail_assert ((B *i 8) ≥b 0) "src/instrs64.sail:43048.48-43048.49"
              (Mem_set (toaddress + setsize) B accdesc (BitVec.replicateBits data B))
              let setsize : (BitVec 64) := (BitVec.addInt setsize B)
              let stagesetsize : (BitVec 64) := (BitVec.addInt stagesetsize B)
              if ((bne stage MOPSStage_Prologue) : Bool)
              then (X_set n 64 setsize)
              else (pure ())
              (pure (B, setsize, stagesetsize))
          (pure loop_vars_1) ) : SailM (Int × (BitVec 64) × (BitVec 64)) )
        (pure (setsize, toaddress)))
    else
      (do
        let (B, setsize, stagesetsize, toaddress) ← (( do
          let mut loop_vars := (B, setsize, stagesetsize, toaddress)
          while (λ (B, setsize, stagesetsize, toaddress) => ((BitVec.toNat stagesetsize) >b 0)) loop_vars do
            let (B, setsize, stagesetsize, toaddress) := loop_vars
            loop_vars ← do
              let B ← (SETSizeChoice toaddress setsize 1)
              sail_assert (B ≤b (BitVec.toNat stagesetsize)) "src/instrs64.sail:43061.42-43061.43"
              let B := B
              sail_assert ((B *i 8) ≥b 0) "src/instrs64.sail:43064.48-43064.49"
              (Mem_set toaddress B accdesc (BitVec.replicateBits data B))
              let toaddress : (BitVec 64) := (BitVec.addInt toaddress B)
              let setsize : (BitVec 64) := (BitVec.subInt setsize B)
              let stagesetsize : (BitVec 64) := (BitVec.subInt stagesetsize B)
              if ((bne stage MOPSStage_Prologue) : Bool)
              then
                (do
                  (X_set n 64 setsize)
                  (X_set d 64 toaddress))
              else (pure ())
              (pure (B, setsize, stagesetsize, toaddress))
          (pure loop_vars) ) : SailM (Int × (BitVec 64) × (BitVec 64) × (BitVec 64)) )
        (pure (setsize, toaddress))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  if ((BEq.beq stage MOPSStage_Prologue) : Bool)
  then
    (do
      (X_set n 64 setsize)
      (X_set d 64 toaddress)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure ())

/-- Type quantifiers: msb : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem msb [7, 15] -/
def execute_aarch64_instrs_integer_flags_setf (msb : Nat) (n : Nat) : SailM Unit := do
  let tmpreg ← (( do (X_read n 32) ) : SailM (BitVec 32) )
  writeReg PSTATE { (← readReg PSTATE) with N := (BitVec.join1 [(BitVec.access tmpreg msb)]) }
  writeReg PSTATE { (← readReg PSTATE) with Z := 
    if (((Sail.BitVec.extractLsb tmpreg msb 0) == (Zeros (n := (msb +i 1)))) : Bool)
    then 1#1
    else 0#1 }
  writeReg PSTATE { (← readReg PSTATE) with V := ((BitVec.join1 [(BitVec.access tmpreg (msb +i 1))]) ^^^ (BitVec.join1 [(BitVec.access tmpreg msb)])) }

/-- Type quantifiers: d : Nat, n : Nat, s : Nat, 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_memory_mcpymset_setg (d : Nat) (n : Nat) (options_name : (BitVec 2)) (s : Nat) (stage : MOPSStage) : SailM Unit := do
  let toaddress ← (( do (X_read d 64) ) : SailM (BitVec 64) )
  let setsize ← (( do (X_read n 64) ) : SailM (BitVec 64) )
  let data ← (( do (X_read s 8) ) : SailM (BitVec 8) )
  let nzcv ← (( do (pure ((← readReg PSTATE).N +++ ((← readReg PSTATE).Z +++ ((← readReg PSTATE).C +++ (← readReg PSTATE).V)))) ) : SailM (BitVec 4) )
  let stagesetsize ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let is_setg : Bool := true
  let B ← (( do (undefined_int ()) ) : SailM Int )
  let supports_option_a ← (( do (SETGOptionA ()) ) : SailM Bool )
  let privileged ← (( do
    if (((BitVec.join1 [(BitVec.access options_name 0)]) == 1#1) : Bool)
    then (AArch64_IsUnprivAccessPriv ())
    else (pure ((← readReg PSTATE).EL != EL0)) ) : SailM Bool )
  let nontemporal : Bool := ((BitVec.join1 [(BitVec.access options_name 1)]) == 1#1)
  let accdesc ← (( do (CreateAccDescSTGMOPS privileged nontemporal) ) : SailM AccessDescriptor )
  let (nzcv, setsize, stagesetsize, toaddress) ← (( do
    if ((BEq.beq stage MOPSStage_Prologue) : Bool)
    then
      (do
        let setsize : (BitVec 64) :=
          if (((BitVec.join1 [(BitVec.access setsize 63)]) == 1#1) : Bool)
          then 0x7FFFFFFFFFFFFFF0#64
          else setsize
        if (((setsize != (Zeros (n := 64))) && (! (IsAligned__1 toaddress TAG_GRANULE))) : Bool)
        then (AArch64_Abort toaddress (← (AlignmentFault accdesc)))
        else (pure ())
        if ((! (IsAligned__1 setsize TAG_GRANULE)) : Bool)
        then (AArch64_Abort toaddress (← (AlignmentFault accdesc)))
        else (pure ())
        let (nzcv, setsize, toaddress) : ((BitVec 4) × (BitVec 64) × (BitVec 64)) :=
          if (supports_option_a : Bool)
          then
            (let nzcv : (BitVec 4) := 0b0000#4
            let toaddress : (BitVec 64) := (toaddress + setsize)
            let setsize : (BitVec 64) := ((Zeros (n := 64)) - setsize)
            (nzcv, setsize, toaddress))
          else
            (let nzcv : (BitVec 4) := 0b0010#4
            (nzcv, setsize, toaddress))
        let stagesetsize ← (SETPreSizeChoice toaddress setsize is_setg)
        sail_assert (((BitVec.join1 [(BitVec.access stagesetsize 63)]) == (BitVec.join1 [(BitVec.access setsize 63)])) || (stagesetsize == (Zeros (n := 64)))) "src/instrs64.sail:43376.78-43376.79"
        sail_assert ((Sail.BitVec.extractLsb stagesetsize 3 0) == 0b0000#4) "src/instrs64.sail:43377.45-43377.46"
        if (((BitVec.toInt setsize) >b 0) : Bool)
        then sail_assert ((BitVec.toInt stagesetsize) ≤b (BitVec.toInt setsize)) "src/instrs64.sail:43379.54-43379.55"
        else sail_assert ((BitVec.toInt stagesetsize) ≥b (BitVec.toInt setsize)) "src/instrs64.sail:43381.54-43381.55"
        (pure (nzcv, setsize, stagesetsize, toaddress)))
    else
      (do
        let postsize ← (( do (SETPostSizeChoice toaddress setsize is_setg) ) : SailM (BitVec 64) )
        sail_assert (((BitVec.join1 [(BitVec.access postsize 63)]) == (BitVec.join1 [(BitVec.access setsize 63)])) || (postsize == (Zeros (n := 64)))) "src/instrs64.sail:43385.70-43385.71"
        sail_assert ((Sail.BitVec.extractLsb postsize 3 0) == 0b0000#4) "src/instrs64.sail:43386.41-43386.42"
        let zero_size_exceptions ← (( do (MemSetZeroSizeCheck ()) ) : SailM Bool )
        if ((zero_size_exceptions || (((BitVec.toInt setsize) != 0) : Bool)) : Bool)
        then
          (do
            if (supports_option_a : Bool)
            then
              (do
                if (((BitVec.join1 [(BitVec.access nzcv 1)]) == 1#1) : Bool)
                then
                  (do
                    let wrong_option : Bool := true
                    let from_epilogue : Bool := (BEq.beq stage MOPSStage_Epilogue)
                    (MismatchedMemSetException supports_option_a d s n wrong_option from_epilogue options_name is_setg))
                else (pure ()))
            else
              (do
                if (((BitVec.join1 [(BitVec.access nzcv 1)]) == 0#1) : Bool)
                then
                  (do
                    let wrong_option : Bool := true
                    let from_epilogue : Bool := (BEq.beq stage MOPSStage_Epilogue)
                    (MismatchedMemSetException supports_option_a d s n wrong_option from_epilogue options_name is_setg))
                else (pure ())))
        else (pure ())
        let stagesetsize ← (( do
          if ((BEq.beq stage MOPSStage_Main) : Bool)
          then
            (do
              let stagesetsize : (BitVec 64) := (setsize - postsize)
              if ((← (MemSetParametersIllformedM toaddress setsize is_setg)) : Bool)
              then
                (do
                  let wrong_option : Bool := false
                  let from_epilogue : Bool := false
                  (MismatchedMemSetException supports_option_a d s n wrong_option from_epilogue options_name is_setg))
              else (pure ())
              (pure stagesetsize))
          else
            (do
              let stagesetsize : (BitVec 64) := postsize
              if ((←((pure (setsize != postsize)) <||> (do
                   (MemSetParametersIllformedE toaddress setsize is_setg)))) : Bool)
              then
                (do
                  let wrong_option : Bool := false
                  let from_epilogue : Bool := true
                  (MismatchedMemSetException supports_option_a d s n wrong_option from_epilogue options_name is_setg))
              else (pure ())
              (pure stagesetsize)) ) : SailM (BitVec 64) )
        if (((setsize != (Zeros (n := 64))) && (! (IsAligned__1 toaddress TAG_GRANULE))) : Bool)
        then (AArch64_Abort toaddress (← (AlignmentFault accdesc)))
        else (pure ())
        if ((! (IsAligned__1 setsize TAG_GRANULE)) : Bool)
        then (AArch64_Abort toaddress (← (AlignmentFault accdesc)))
        else (pure ())
        (pure (nzcv, setsize, stagesetsize, toaddress))) ) : SailM ((BitVec 4) × (BitVec 64) × (BitVec 64) × (BitVec 64)) )
  let tagstep ← (( do (undefined_int ()) ) : SailM Int )
  let tag ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let tagaddr ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleMemSet ())
  else (pure ())
  let (setsize, toaddress) ← (( do
    if (supports_option_a : Bool)
    then
      (do
        let (B, setsize, stagesetsize, tag, tagaddr, tagstep) ← (( do
          let mut loop_vars_2 := (B, setsize, stagesetsize, tag, tagaddr, tagstep)
          while (λ (B, setsize, stagesetsize, tag, tagaddr, tagstep) => ((BitVec.toInt stagesetsize) <b 0)) loop_vars_2 do
            let (B, setsize, stagesetsize, tag, tagaddr, tagstep) := loop_vars_2
            loop_vars_2 ← do
              let B ← (SETSizeChoice toaddress setsize 16)
              sail_assert (B ≤b ((Neg.neg 1) *i (BitVec.toInt stagesetsize))) "src/instrs64.sail:43439.54-43439.55"
              sail_assert ((integer_subrange B 3 0) == 0b0000#4) "src/instrs64.sail:43440.38-43440.39"
              let B := B
              sail_assert ((B *i 8) ≥b 0) "src/instrs64.sail:43443.48-43443.49"
              (Mem_set (toaddress + setsize) B accdesc (BitVec.replicateBits data B))
              let tagstep : Int := (fdiv_int B 16)
              let tag : (BitVec 4) := (AArch64_AllocationTagFromAddress (toaddress + setsize))
              let (tagaddr, tagstep) ← (( do
                let mut loop_vars_3 := (tagaddr, tagstep)
                while (λ (tagaddr, tagstep) => (tagstep >b 0)) loop_vars_3 do
                  let (tagaddr, tagstep) := loop_vars_3
                  loop_vars_3 ← do
                    let tagaddr : (BitVec 64) := (BitVec.addInt (toaddress + setsize) ((tagstep -i 1) *i 16))
                    (AArch64_MemTag_set tagaddr accdesc tag)
                    let tagstep : Int := (tagstep -i 1)
                    (pure (tagaddr, tagstep))
                (pure loop_vars_3) ) : SailM ((BitVec 64) × Int) )
              let setsize : (BitVec 64) := (BitVec.addInt setsize B)
              let stagesetsize : (BitVec 64) := (BitVec.addInt stagesetsize B)
              if ((bne stage MOPSStage_Prologue) : Bool)
              then (X_set n 64 setsize)
              else (pure ())
              (pure (B, setsize, stagesetsize, tag, tagaddr, tagstep))
          (pure loop_vars_2) ) : SailM (Int × (BitVec 64) × (BitVec 64) × (BitVec 4) × (BitVec 64) × Int) )
        (pure (setsize, toaddress)))
    else
      (do
        let (B, setsize, stagesetsize, tag, tagaddr, tagstep, toaddress) ← (( do
          let mut loop_vars := (B, setsize, stagesetsize, tag, tagaddr, tagstep, toaddress)
          while (λ (B, setsize, stagesetsize, tag, tagaddr, tagstep, toaddress) => ((BitVec.toNat stagesetsize) >b 0)) loop_vars do
            let (B, setsize, stagesetsize, tag, tagaddr, tagstep, toaddress) := loop_vars
            loop_vars ← do
              let B ← (SETSizeChoice toaddress setsize 16)
              sail_assert (B ≤b (BitVec.toNat stagesetsize)) "src/instrs64.sail:43463.42-43463.43"
              sail_assert ((integer_subrange B 3 0) == 0b0000#4) "src/instrs64.sail:43464.38-43464.39"
              let B := B
              sail_assert ((B *i 8) ≥b 0) "src/instrs64.sail:43467.48-43467.49"
              (Mem_set toaddress B accdesc (BitVec.replicateBits data B))
              let tagstep : Int := (fdiv_int B 16)
              let tag : (BitVec 4) := (AArch64_AllocationTagFromAddress toaddress)
              let (tagaddr, tagstep) ← (( do
                let mut loop_vars_1 := (tagaddr, tagstep)
                while (λ (tagaddr, tagstep) => (tagstep >b 0)) loop_vars_1 do
                  let (tagaddr, tagstep) := loop_vars_1
                  loop_vars_1 ← do
                    let tagaddr : (BitVec 64) := (BitVec.addInt toaddress ((tagstep -i 1) *i 16))
                    (AArch64_MemTag_set tagaddr accdesc tag)
                    let tagstep : Int := (tagstep -i 1)
                    (pure (tagaddr, tagstep))
                (pure loop_vars_1) ) : SailM ((BitVec 64) × Int) )
              let toaddress : (BitVec 64) := (BitVec.addInt toaddress B)
              let setsize : (BitVec 64) := (BitVec.subInt setsize B)
              let stagesetsize : (BitVec 64) := (BitVec.subInt stagesetsize B)
              if ((bne stage MOPSStage_Prologue) : Bool)
              then
                (do
                  (X_set n 64 setsize)
                  (X_set d 64 toaddress))
              else (pure ())
              (pure (B, setsize, stagesetsize, tag, tagaddr, tagstep, toaddress))
          (pure loop_vars) ) : SailM (Int × (BitVec 64) × (BitVec 64) × (BitVec 4) × (BitVec 64) × Int × (BitVec 64)) )
        (pure (setsize, toaddress))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  if ((BEq.beq stage MOPSStage_Prologue) : Bool)
  then
    (do
      (X_set n 64 setsize)
      (X_set d 64 toaddress)
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure ())

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let x ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let y ← (( do (V_read n 32) ) : SailM (BitVec 32) )
  let w ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let t ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
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
  (V_set d 128 x)

/-- Type quantifiers: d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha2op_sha1_hash (d : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let operand ← (( do (V_read n 32) ) : SailM (BitVec 32) )
  (V_set d 32 (← (ROL operand 30)))

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let x ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let y ← (( do (V_read n 32) ) : SailM (BitVec 32) )
  let w ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let t ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
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
  (V_set d 128 x)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let x ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let y ← (( do (V_read n 32) ) : SailM (BitVec 32) )
  let w ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let t ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
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
  (V_set d 128 x)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let operand1 ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let operand2 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let operand3 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let result : (BitVec 128) := ((Sail.BitVec.extractLsb operand2 63 0) +++ (Sail.BitVec.extractLsb operand1 127 64))
  let result : (BitVec 128) := ((result ^^^ operand1) ^^^ operand3)
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 (d : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let operand1 ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let operand2 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let T : (BitVec 128) := (operand1 ^^^ (operand2 >>> 32))
  let result ← (pure (Sail.BitVec.updateSubrange result 31 0 (← (ROL (Sail.BitVec.extractLsb T 31 0) 1))))
  let result ← (pure (Sail.BitVec.updateSubrange result 63 32 (← (ROL (Sail.BitVec.extractLsb T 63 32) 1))))
  let result ← (pure (Sail.BitVec.updateSubrange result 95 64 (← (ROL (Sail.BitVec.extractLsb T 95 64) 1))))
  let result ← (pure (Sail.BitVec.updateSubrange result 127 96 ((← (ROL (Sail.BitVec.extractLsb T 127 96) 1)) ^^^ (← (ROL (Sail.BitVec.extractLsb T 31 0) 2)))))
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_part1 : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3op_sha256_hash (d : Nat) (m : Nat) (n : Nat) (part1 : Bool) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let result ← (( do
    if (part1 : Bool)
    then (do (SHA256hash (← (V_read d 128)) (← (V_read n 128)) (← (V_read m 128)) true))
    else (do (SHA256hash (← (V_read n 128)) (← (V_read d 128)) (← (V_read m 128)) false)) ) : SailM (BitVec 128) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 (d : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let operand1 ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let operand2 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let T : (BitVec 128) := ((Sail.BitVec.extractLsb operand2 31 0) +++ (Sail.BitVec.extractLsb operand1 127 32))
  let elt ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (elt, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := 3
    let mut loop_vars := (elt, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (elt, result) := loop_vars
      loop_vars ← do
        let elt ← (Elem_read T e 32)
        let elt : (BitVec 32) := (((ROR elt 7) ^^^ (ROR elt 18)) ^^^ (elt >>> 3))
        let result ← (Elem_set result e 32 (elt + (← (Elem_read operand1 e 32))))
        (pure (elt, result))
    (pure loop_vars) ) : SailM ((BitVec 32) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let operand1 ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let operand2 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let operand3 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let T0 : (BitVec 128) := ((Sail.BitVec.extractLsb operand3 31 0) +++ (Sail.BitVec.extractLsb operand2 127 32))
  let elt ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let T1 : (BitVec 64) := (Sail.BitVec.extractLsb operand3 127 64)
  let (elt, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := 1
    let mut loop_vars := (elt, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (elt, result) := loop_vars
      loop_vars ← do
        let elt ← (Elem_read T1 e 32)
        let elt : (BitVec 32) := (((ROR elt 17) ^^^ (ROR elt 19)) ^^^ (elt >>> 10))
        let elt ← (pure ((elt + (← (Elem_read operand1 e 32))) + (← (Elem_read T0 e 32))))
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
        let elt ← (pure ((elt + (← (Elem_read operand1 e 32))) + (← (Elem_read T0 e 32))))
        let result ← (Elem_set result e 32 elt)
        (pure (elt, result))
    (pure loop_vars_1) ) : SailM ((BitVec 32) × (BitVec 128)) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha512_sha512h (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vtmp ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let x ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let y ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let w ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let MSigma1 : (BitVec 64) := (((ROR (Sail.BitVec.extractLsb y 127 64) 14) ^^^ (ROR (Sail.BitVec.extractLsb y 127 64) 18)) ^^^ (ROR (Sail.BitVec.extractLsb y 127 64) 41))
  let Vtmp : (BitVec 128) := (Sail.BitVec.updateSubrange Vtmp 127 64 (((Sail.BitVec.extractLsb y 127 64) &&& (Sail.BitVec.extractLsb x 63 0)) ^^^ ((Complement.complement (Sail.BitVec.extractLsb y 127 64)) &&& (Sail.BitVec.extractLsb x 127 64))))
  let Vtmp : (BitVec 128) := (Sail.BitVec.updateSubrange Vtmp 127 64 (((Sail.BitVec.extractLsb Vtmp 127 64) + MSigma1) + (Sail.BitVec.extractLsb w 127 64)))
  let tmp : (BitVec 64) := ((Sail.BitVec.extractLsb Vtmp 127 64) + (Sail.BitVec.extractLsb y 63 0))
  let MSigma1 : (BitVec 64) := (((ROR tmp 14) ^^^ (ROR tmp 18)) ^^^ (ROR tmp 41))
  let Vtmp : (BitVec 128) := (Sail.BitVec.updateSubrange Vtmp 63 0 ((tmp &&& (Sail.BitVec.extractLsb y 127 64)) ^^^ ((Complement.complement tmp) &&& (Sail.BitVec.extractLsb x 63 0))))
  let Vtmp : (BitVec 128) := (Sail.BitVec.updateSubrange Vtmp 63 0 (((Sail.BitVec.extractLsb Vtmp 63 0) + MSigma1) + (Sail.BitVec.extractLsb w 63 0)))
  (V_set d 128 Vtmp)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha512_sha512h2 (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vtmp ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let x ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let y ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let w ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let NSigma0 : (BitVec 64) := (((ROR (Sail.BitVec.extractLsb y 63 0) 28) ^^^ (ROR (Sail.BitVec.extractLsb y 63 0) 34)) ^^^ (ROR (Sail.BitVec.extractLsb y 63 0) 39))
  let Vtmp : (BitVec 128) := (Sail.BitVec.updateSubrange Vtmp 127 64 ((((Sail.BitVec.extractLsb x 63 0) &&& (Sail.BitVec.extractLsb y 127 64)) ^^^ ((Sail.BitVec.extractLsb x 63 0) &&& (Sail.BitVec.extractLsb y 63 0))) ^^^ ((Sail.BitVec.extractLsb y 127 64) &&& (Sail.BitVec.extractLsb y 63 0))))
  let Vtmp : (BitVec 128) := (Sail.BitVec.updateSubrange Vtmp 127 64 (((Sail.BitVec.extractLsb Vtmp 127 64) + NSigma0) + (Sail.BitVec.extractLsb w 127 64)))
  let NSigma0 : (BitVec 64) := (((ROR (Sail.BitVec.extractLsb Vtmp 127 64) 28) ^^^ (ROR (Sail.BitVec.extractLsb Vtmp 127 64) 34)) ^^^ (ROR (Sail.BitVec.extractLsb Vtmp 127 64) 39))
  let Vtmp : (BitVec 128) := (Sail.BitVec.updateSubrange Vtmp 63 0 ((((Sail.BitVec.extractLsb Vtmp 127 64) &&& (Sail.BitVec.extractLsb y 63 0)) ^^^ ((Sail.BitVec.extractLsb Vtmp 127 64) &&& (Sail.BitVec.extractLsb y 127 64))) ^^^ ((Sail.BitVec.extractLsb y 127 64) &&& (Sail.BitVec.extractLsb y 63 0))))
  let Vtmp : (BitVec 128) := (Sail.BitVec.updateSubrange Vtmp 63 0 (((Sail.BitVec.extractLsb Vtmp 63 0) + NSigma0) + (Sail.BitVec.extractLsb w 63 0)))
  (V_set d 128 Vtmp)

/-- Type quantifiers: d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha512_sha512su0 (d : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vtmp ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let x ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let w ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let sig0 : (BitVec 64) := (((ROR (Sail.BitVec.extractLsb w 127 64) 1) ^^^ (ROR (Sail.BitVec.extractLsb w 127 64) 8)) ^^^ (0b0000000#7 +++ (Sail.BitVec.extractLsb w 127 71)))
  let Vtmp : (BitVec 128) := (Sail.BitVec.updateSubrange Vtmp 63 0 ((Sail.BitVec.extractLsb w 63 0) + sig0))
  let sig0 : (BitVec 64) := (((ROR (Sail.BitVec.extractLsb x 63 0) 1) ^^^ (ROR (Sail.BitVec.extractLsb x 63 0) 8)) ^^^ (0b0000000#7 +++ (Sail.BitVec.extractLsb x 63 7)))
  let Vtmp : (BitVec 128) := (Sail.BitVec.updateSubrange Vtmp 127 64 ((Sail.BitVec.extractLsb w 127 64) + sig0))
  (V_set d 128 Vtmp)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha512_sha512su1 (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vtmp ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let x ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let y ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let w ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let sig1 : (BitVec 64) := (((ROR (Sail.BitVec.extractLsb x 127 64) 19) ^^^ (ROR (Sail.BitVec.extractLsb x 127 64) 61)) ^^^ (0b000000#6 +++ (Sail.BitVec.extractLsb x 127 70)))
  let Vtmp : (BitVec 128) := (Sail.BitVec.updateSubrange Vtmp 127 64 (((Sail.BitVec.extractLsb w 127 64) + sig1) + (Sail.BitVec.extractLsb y 127 64)))
  let sig1 : (BitVec 64) := (((ROR (Sail.BitVec.extractLsb x 63 0) 19) ^^^ (ROR (Sail.BitVec.extractLsb x 63 0) 61)) ^^^ (0b000000#6 +++ (Sail.BitVec.extractLsb x 63 6)))
  let Vtmp : (BitVec 128) := (Sail.BitVec.updateSubrange Vtmp 63 0 (((Sail.BitVec.extractLsb w 63 0) + sig1) + (Sail.BitVec.extractLsb y 63 0)))
  (V_set d 128 Vtmp)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let sum ← (( do (undefined_int ()) ) : SailM Int )
  let (element1, element2, result, sum) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result, sum)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result, sum) := loop_vars
      loop_vars ← do
        let element1 ← (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let sum : Int := (Int.shiftr (element1 +i element2) 1)
        let result ← (Elem_set result e esize (integer_subrange sum (esize -i 1) 0))
        (pure (element1, element2, result, sum))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec datasize) × Int) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Int, elements : Int, esize : Int, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_left_sisd (d : Nat) (datasize : Int) (elements : Int) (esize : Int) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:44321.56-44321.57"
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        sail_assert (esize ≥b 0) "src/instrs64.sail:44325.38-44325.39"
        sail_assert (((e *i esize) ≤b (((e *i esize) +i esize) -i 1)) || ((! ((e ≥b 0) && (((e +i 1) *i esize) ≤b datasize))) || (! (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128))))) "src/instrs64.sail:44326.179-44326.180"
        (Elem_set result e esize ((← (Elem_read operand e esize)) <<< shift))
    (pure loop_vars) ) : SailM (BitVec datasize) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n : Nat, part : Nat, shift : Nat, List.elem shift [8, 16, 32, 64] ∧ List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_shift (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) (shift : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (Vpart_read n part datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let element ← (( do (undefined_int ()) ) : SailM Int )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (pure (Int.shiftl (← (asl_Int (← (Elem_read operand e esize)) is_unsigned)) shift))
        let result ← (Elem_set result e (2 *i esize) (integer_subrange element ((2 *i esize) -i 1) 0))
        (pure (element, result))
    (pure loop_vars) ) : SailM (Int × (BitVec (2 * datasize))) )
  (V_set d (2 *i datasize) result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let diff ← (( do (undefined_int ()) ) : SailM Int )
  let (diff, element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (diff, element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (diff, element1, element2, result) := loop_vars
      loop_vars ← do
        let element1 ← (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let diff : Int := (Int.shiftr (element1 -i element2) 1)
        let result ← (Elem_set result e esize (integer_subrange diff (esize -i 1) 0))
        (pure (diff, element1, element2, result))
    (pure loop_vars) ) : SailM (Int × Int × Int × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Int, elements : Int, esize : Int, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_left_insert_sisd (d : Nat) (datasize : Int) (elements : Int) (esize : Int) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:44507.56-44507.57"
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  sail_assert (esize ≥b 0) "src/instrs64.sail:44511.34-44511.35"
  let mask : (BitVec esize) := ((Ones (n := esize)) <<< shift)
  let shifted ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (result, shifted) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (result, shifted)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (result, shifted) := loop_vars
      loop_vars ← do
        sail_assert (((e *i esize) ≤b (((e *i esize) +i esize) -i 1)) || ((! ((e ≥b 0) && (((e +i 1) *i esize) ≤b datasize))) || ((! (esize ≥b 0)) || (! (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)))))) "src/instrs64.sail:44515.198-44515.199"
        let shifted ← (pure ((← (Elem_read operand e esize)) <<< shift))
        let result ← (Elem_set result e esize (((← (Elem_read operand2 e esize)) &&& (Complement.complement mask)) ||| shifted))
        (pure (result, shifted))
    (pure loop_vars) ) : SailM ((BitVec datasize) × (BitVec esize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm3_sm3partw1 (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Vd ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let result ← (pure (Sail.BitVec.updateSubrange result 95 0 ((Sail.BitVec.extractLsb (Vd ^^^ Vn) 95 0) ^^^ (((← (ROL (Sail.BitVec.extractLsb Vm 127 96) 15)) +++ (← (ROL (Sail.BitVec.extractLsb Vm 95 64) 15))) +++ (← (ROL (Sail.BitVec.extractLsb Vm 63 32) 15))))))
  let result ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 3
    let mut loop_vars := result
    for i in [loop_i_lower:loop_i_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (( do
          if ((i == 3) : Bool)
          then (do (pure (Sail.BitVec.updateSubrange result 127 96 ((Sail.BitVec.extractLsb (Vd ^^^ Vn) 127 96) ^^^ (← (ROL (Sail.BitVec.extractLsb result 31 0) 15))))))
          else (pure result) ) : SailM (BitVec 128) )
        (pure (Sail.BitVec.updateSubrange result ((32 *i i) +i 31) (32 *i i) (((Sail.BitVec.extractLsb result ((32 *i i) +i 31) (32 *i i)) ^^^ (← (ROL (Sail.BitVec.extractLsb result ((32 *i i) +i 31) (32 *i i)) 15))) ^^^ (← (ROL (Sail.BitVec.extractLsb result ((32 *i i) +i 31) (32 *i i)) 23)))))
    (pure loop_vars) ) : SailM (BitVec 128) )
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm3_sm3partw2 (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Vd ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let tmp ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let tmp ← (pure (Sail.BitVec.updateSubrange tmp 127 0 (Vn ^^^ ((((← (ROL (Sail.BitVec.extractLsb Vm 127 96) 7)) +++ (← (ROL (Sail.BitVec.extractLsb Vm 95 64) 7))) +++ (← (ROL (Sail.BitVec.extractLsb Vm 63 32) 7))) +++ (← (ROL (Sail.BitVec.extractLsb Vm 31 0) 7))))))
  let result : (BitVec 128) := (Sail.BitVec.updateSubrange result 127 0 ((Sail.BitVec.extractLsb Vd 127 0) ^^^ (Sail.BitVec.extractLsb tmp 127 0)))
  let tmp2 ← (( do (ROL (Sail.BitVec.extractLsb tmp 31 0) 15) ) : SailM (BitVec 32) )
  let tmp2 ← (( do (pure ((tmp2 ^^^ (← (ROL tmp2 15))) ^^^ (← (ROL tmp2 23)))) ) : SailM (BitVec 32) )
  let result : (BitVec 128) := (Sail.BitVec.updateSubrange result 127 96 ((Sail.BitVec.extractLsb result 127 96) ^^^ tmp2))
  (V_set d 128 result)

/-- Type quantifiers: a : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm3_sm3ss1 (a : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Va ← (( do (V_read a 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let result ← (pure (Sail.BitVec.updateSubrange result 127 96 (← (ROL (((← (ROL (Sail.BitVec.extractLsb Vn 127 96) 12)) + (Sail.BitVec.extractLsb Vm 127 96)) + (Sail.BitVec.extractLsb Va 127 96)) 7))))
  let result : (BitVec 128) := (Sail.BitVec.updateSubrange result 95 0 (Zeros (n := 96)))
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, i : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem i [0, 1, 2, 3] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm3_sm3tt1a (d : Nat) (i : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Vd ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let WjPrime ← (( do (Elem_read Vm i 32) ) : SailM (BitVec 32) )
  let SS2 ← (( do (pure ((Sail.BitVec.extractLsb Vn 127 96) ^^^ (← (ROL (Sail.BitVec.extractLsb Vd 127 96) 12)))) ) : SailM (BitVec 32) )
  let TT1 : (BitVec 32) := ((Sail.BitVec.extractLsb Vd 63 32) ^^^ ((Sail.BitVec.extractLsb Vd 127 96) ^^^ (Sail.BitVec.extractLsb Vd 95 64)))
  let TT1 : (BitVec 32) := (Sail.BitVec.extractLsb (((TT1 + (Sail.BitVec.extractLsb Vd 31 0)) + SS2) + WjPrime) 31 0)
  let result : (BitVec 128) := (Sail.BitVec.updateSubrange result 31 0 (Sail.BitVec.extractLsb Vd 63 32))
  let result ← (pure (Sail.BitVec.updateSubrange result 63 32 (← (ROL (Sail.BitVec.extractLsb Vd 95 64) 9))))
  let result : (BitVec 128) := (Sail.BitVec.updateSubrange result 95 64 (Sail.BitVec.extractLsb Vd 127 96))
  let result : (BitVec 128) := (Sail.BitVec.updateSubrange result 127 96 TT1)
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, i : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem i [0, 1, 2, 3] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm3_sm3tt1b (d : Nat) (i : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Vd ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let WjPrime ← (( do (Elem_read Vm i 32) ) : SailM (BitVec 32) )
  let SS2 ← (( do (pure ((Sail.BitVec.extractLsb Vn 127 96) ^^^ (← (ROL (Sail.BitVec.extractLsb Vd 127 96) 12)))) ) : SailM (BitVec 32) )
  let TT1 : (BitVec 32) := ((((Sail.BitVec.extractLsb Vd 127 96) &&& (Sail.BitVec.extractLsb Vd 63 32)) ||| ((Sail.BitVec.extractLsb Vd 127 96) &&& (Sail.BitVec.extractLsb Vd 95 64))) ||| ((Sail.BitVec.extractLsb Vd 63 32) &&& (Sail.BitVec.extractLsb Vd 95 64)))
  let TT1 : (BitVec 32) := (Sail.BitVec.extractLsb (((TT1 + (Sail.BitVec.extractLsb Vd 31 0)) + SS2) + WjPrime) 31 0)
  let result : (BitVec 128) := (Sail.BitVec.updateSubrange result 31 0 (Sail.BitVec.extractLsb Vd 63 32))
  let result ← (pure (Sail.BitVec.updateSubrange result 63 32 (← (ROL (Sail.BitVec.extractLsb Vd 95 64) 9))))
  let result : (BitVec 128) := (Sail.BitVec.updateSubrange result 95 64 (Sail.BitVec.extractLsb Vd 127 96))
  let result : (BitVec 128) := (Sail.BitVec.updateSubrange result 127 96 TT1)
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, i : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem i [0, 1, 2, 3] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm3_sm3tt2a (d : Nat) (i : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Vd ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let Wj ← (( do (Elem_read Vm i 32) ) : SailM (BitVec 32) )
  let TT2 : (BitVec 32) := ((Sail.BitVec.extractLsb Vd 63 32) ^^^ ((Sail.BitVec.extractLsb Vd 127 96) ^^^ (Sail.BitVec.extractLsb Vd 95 64)))
  let TT2 : (BitVec 32) := (Sail.BitVec.extractLsb (((TT2 + (Sail.BitVec.extractLsb Vd 31 0)) + (Sail.BitVec.extractLsb Vn 127 96)) + Wj) 31 0)
  let result : (BitVec 128) := (Sail.BitVec.updateSubrange result 31 0 (Sail.BitVec.extractLsb Vd 63 32))
  let result ← (pure (Sail.BitVec.updateSubrange result 63 32 (← (ROL (Sail.BitVec.extractLsb Vd 95 64) 19))))
  let result : (BitVec 128) := (Sail.BitVec.updateSubrange result 95 64 (Sail.BitVec.extractLsb Vd 127 96))
  let result ← (pure (Sail.BitVec.updateSubrange result 127 96 ((TT2 ^^^ (← (ROL TT2 9))) ^^^ (← (ROL TT2 17)))))
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, i : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem i [0, 1, 2, 3] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm3_sm3tt2b (d : Nat) (i : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let Vd ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let result ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let Wj ← (( do (Elem_read Vm i 32) ) : SailM (BitVec 32) )
  let TT2 : (BitVec 32) := (((Sail.BitVec.extractLsb Vd 127 96) &&& (Sail.BitVec.extractLsb Vd 95 64)) ||| ((Complement.complement (Sail.BitVec.extractLsb Vd 127 96)) &&& (Sail.BitVec.extractLsb Vd 63 32)))
  let TT2 : (BitVec 32) := (Sail.BitVec.extractLsb (((TT2 + (Sail.BitVec.extractLsb Vd 31 0)) + (Sail.BitVec.extractLsb Vn 127 96)) + Wj) 31 0)
  let result : (BitVec 128) := (Sail.BitVec.updateSubrange result 31 0 (Sail.BitVec.extractLsb Vd 63 32))
  let result ← (pure (Sail.BitVec.updateSubrange result 63 32 (← (ROL (Sail.BitVec.extractLsb Vd 95 64) 19))))
  let result : (BitVec 128) := (Sail.BitVec.updateSubrange result 95 64 (Sail.BitVec.extractLsb Vd 127 96))
  let result ← (pure (Sail.BitVec.updateSubrange result 127 96 ((TT2 ^^^ (← (ROL TT2 9))) ^^^ (← (ROL TT2 17)))))
  (V_set d 128 result)

/-- Type quantifiers: d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm4_sm4enc (d : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let intval ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let roundkey ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let roundresult ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  let (intval, roundkey, roundresult) ← (( do
    let loop_index_lower := 0
    let loop_index_upper := 3
    let mut loop_vars := (intval, roundkey, roundresult)
    for index in [loop_index_lower:loop_index_upper:1]i do
      let (intval, roundkey, roundresult) := loop_vars
      loop_vars ← do
        let roundkey ← (Elem_read Vn index 32)
        let intval : (BitVec 32) := ((((Sail.BitVec.extractLsb roundresult 127 96) ^^^ (Sail.BitVec.extractLsb roundresult 95 64)) ^^^ (Sail.BitVec.extractLsb roundresult 63 32)) ^^^ roundkey)
        let intval ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 3
          let mut loop_vars_1 := intval
          for i in [loop_i_lower:loop_i_upper:1]i do
            let intval := loop_vars_1
            loop_vars_1 ← do (Elem_set intval i 8 (Sbox (← (Elem_read intval i 8))))
          (pure loop_vars_1) ) : SailM (BitVec 32) )
        let intval ← (pure ((((intval ^^^ (← (ROL intval 2))) ^^^ (← (ROL intval 10))) ^^^ (← (ROL intval 18))) ^^^ (← (ROL intval 24))))
        let intval : (BitVec 32) := (intval ^^^ (Sail.BitVec.extractLsb roundresult 31 0))
        let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 31 0 (Sail.BitVec.extractLsb roundresult 63 32))
        let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 63 32 (Sail.BitVec.extractLsb roundresult 95 64))
        let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 95 64 (Sail.BitVec.extractLsb roundresult 127 96))
        let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 127 96 intval)
        (pure (intval, roundkey, roundresult))
    (pure loop_vars) ) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 128)) )
  (V_set d 128 roundresult)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sm4_sm4enckey (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let intval ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let const ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let roundresult ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let (const, intval, roundresult) ← (( do
    let loop_index_lower := 0
    let loop_index_upper := 3
    let mut loop_vars := (const, intval, roundresult)
    for index in [loop_index_lower:loop_index_upper:1]i do
      let (const, intval, roundresult) := loop_vars
      loop_vars ← do
        let const ← (Elem_read Vm index 32)
        let intval : (BitVec 32) := ((((Sail.BitVec.extractLsb roundresult 127 96) ^^^ (Sail.BitVec.extractLsb roundresult 95 64)) ^^^ (Sail.BitVec.extractLsb roundresult 63 32)) ^^^ const)
        let intval ← (( do
          let loop_i_lower := 0
          let loop_i_upper := 3
          let mut loop_vars_1 := intval
          for i in [loop_i_lower:loop_i_upper:1]i do
            let intval := loop_vars_1
            loop_vars_1 ← do (Elem_set intval i 8 (Sbox (← (Elem_read intval i 8))))
          (pure loop_vars_1) ) : SailM (BitVec 32) )
        let intval ← (pure ((intval ^^^ (← (ROL intval 13))) ^^^ (← (ROL intval 23))))
        let intval : (BitVec 32) := (intval ^^^ (Sail.BitVec.extractLsb roundresult 31 0))
        let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 31 0 (Sail.BitVec.extractLsb roundresult 63 32))
        let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 63 32 (Sail.BitVec.extractLsb roundresult 95 64))
        let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 95 64 (Sail.BitVec.extractLsb roundresult 127 96))
        let roundresult : (BitVec 128) := (Sail.BitVec.updateSubrange roundresult 127 96 intval)
        (pure (const, intval, roundresult))
    (pure loop_vars) ) : SailM ((BitVec 32) × (BitVec 32) × (BitVec 128)) )
  (V_set d 128 roundresult)

/-- Type quantifiers: a : Nat, d : Nat, datasize : Nat, destsize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ destsize = 64 ∧ datasize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (a : Nat) (d : Nat) (datasize : Nat) (destsize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (X_read m datasize) ) : SailM (BitVec datasize) )
  let operand3 ← (( do (X_read a destsize) ) : SailM (BitVec destsize) )
  let result ← (( do (undefined_int ()) ) : SailM Int )
  let result ← (( do
    if (sub_op : Bool)
    then (do (pure ((← (asl_Int operand3 is_unsigned)) -i ((← (asl_Int operand1 is_unsigned)) *i (← (asl_Int operand2 is_unsigned))))))
    else (do (pure ((← (asl_Int operand3 is_unsigned)) +i ((← (asl_Int operand1 is_unsigned)) *i (← (asl_Int operand2 is_unsigned)))))) ) : SailM Int )
  let result := result
  (X_set d 64 (integer_subrange result 63 0))

/-- Type quantifiers: d : Nat, datasize : Nat, imm : Int, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_max_min_smax_imm (d : Nat) (datasize : Nat) (imm : Int) (n : Nat) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let result := (Max.max (BitVec.toInt operand1) imm)
  (X_set d datasize (integer_subrange result (datasize -i 1) 0))

/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_max_min_smax_reg (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (X_read m datasize) ) : SailM (BitVec datasize) )
  let result := (Max.max (BitVec.toInt operand1) (BitVec.toInt operand2))
  (X_set d datasize (integer_subrange result (datasize -i 1) 0))

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, k_minimum : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (minimum : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let maxmin ← (( do (undefined_int ()) ) : SailM Int )
  let (element1, element2, maxmin, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, maxmin, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, maxmin, result) := loop_vars
      loop_vars ← do
        let element1 ← (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let maxmin : Int :=
          if (minimum : Bool)
          then (Min.min element1 element2)
          else (Max.max element1 element2)
        let result ← (Elem_set result e esize (integer_subrange maxmin (esize -i 1) 0))
        (pure (element1, element2, maxmin, result))
    (pure loop_vars) ) : SailM (Int × Int × Int × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, k_minimum : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (minimum : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let concat : (BitVec (2 * datasize)) := (operand2 +++ operand1)
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let maxmin ← (( do (undefined_int ()) ) : SailM Int )
  let (element1, element2, maxmin, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, maxmin, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, maxmin, result) := loop_vars
      loop_vars ← do
        let element1 ← (asl_Int (← (Elem_read concat (2 *i e) esize)) is_unsigned)
        let element2 ← (asl_Int (← (Elem_read concat ((2 *i e) +i 1) esize)) is_unsigned)
        let maxmin : Int :=
          if (minimum : Bool)
          then (Min.min element1 element2)
          else (Max.max element1 element2)
        let result ← (Elem_set result e esize (integer_subrange maxmin (esize -i 1) 0))
        (pure (element1, element2, maxmin, result))
    (pure loop_vars) ) : SailM (Int × Int × Int × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, k_min : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_reduce_int_max (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (min : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int ()) ) : SailM Int )
  let maxmin ← (( do (asl_Int (← (Elem_read operand 0 esize)) is_unsigned) ) : SailM Int )
  let (element, maxmin) ← (( do
    let loop_e_lower := 1
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, maxmin)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, maxmin) := loop_vars
      loop_vars ← do
        let element ← (asl_Int (← (Elem_read operand e esize)) is_unsigned)
        let maxmin : Int :=
          if (min : Bool)
          then (Min.min maxmin element)
          else (Max.max maxmin element)
        (pure (element, maxmin))
    (pure loop_vars) ) : SailM (Int × Int) )
  let maxmin := maxmin
  (V_set d esize (integer_subrange maxmin (esize -i 1) 0))

def execute_aarch64_instrs_system_exceptions_runtime_smc (imm : (BitVec 16)) : SailM Unit := do
  (AArch64_CheckForSMCUndefOrTrap imm)
  (AArch64_CallSecureMonitor imm)

/-- Type quantifiers: d : Nat, datasize : Nat, imm : Int, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_max_min_smin_imm (d : Nat) (datasize : Nat) (imm : Int) (n : Nat) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let result := (Min.min (BitVec.toInt operand1) imm)
  (X_set d datasize (integer_subrange result (datasize -i 1) 0))

/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_max_min_smin_reg (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (X_read m datasize) ) : SailM (BitVec datasize) )
  let result := (Min.min (BitVec.toInt operand1) (BitVec.toInt operand2))
  (X_set d datasize (integer_subrange result (datasize -i 1) 0))

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, part : Nat, k_sub_op : Bool, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (Vpart_read n part datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (Vpart_read m part datasize) ) : SailM (BitVec datasize) )
  let operand3 ← (( do (V_read d (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let result ← (( do (undefined_bitvector (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let product ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  let accum ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  let (accum, element1, element2, product, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (accum, element1, element2, product, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (accum, element1, element2, product, result) := loop_vars
      loop_vars ← do
        let element1 ← (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        let accum ← (( do
          if (sub_op : Bool)
          then (do (pure ((← (Elem_read operand3 e (2 *i esize))) - product)))
          else (do (pure ((← (Elem_read operand3 e (2 *i esize))) + product))) ) : SailM (BitVec (2 * esize)) )
        let result ← (Elem_set result e (2 *i esize) accum)
        (pure (accum, element1, element2, product, result))
    (pure loop_vars) ) : SailM ((BitVec (2 * esize)) × Int × Int × (BitVec (2 * esize)) × (BitVec (2 * datasize))) )
  (V_set d (2 *i datasize) result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, part : Nat, k_sub_op : Bool, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem idxdsize [64, 128] ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) (part : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (Vpart_read n part datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m idxdsize) ) : SailM (BitVec idxdsize) )
  let operand3 ← (( do (V_read d (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let result ← (( do (undefined_bitvector (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let product ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  let element2 ← do (asl_Int (← (Elem_read operand2 index esize)) is_unsigned)
  let (element1, product, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, product, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, product, result) := loop_vars
      loop_vars ← do
        let element1 ← (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        let result ← (( do
          if (sub_op : Bool)
          then (do (Elem_set result e (2 *i esize) ((← (Elem_read operand3 e (2 *i esize))) - product)))
          else (do (Elem_set result e (2 *i esize) ((← (Elem_read operand3 e (2 *i esize))) + product))) ) : SailM (BitVec (2 * datasize)) )
        (pure (element1, product, result))
    (pure loop_vars) ) : SailM (Int × (BitVec (2 * esize)) × (BitVec (2 * datasize))) )
  (V_set d (2 *i datasize) result)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla (d : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let operand2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let addend ← (( do (V_read d 128) ) : SailM (BitVec 128) )
  (V_set d 128 (← (MatMulAdd addend operand1 operand2 op1_unsigned op2_unsigned)))

/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, idxdsize : Nat, index : Int, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem idxdsize [64, 128] ∧ List.elem esize [8, 16, 32] ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_integer_move_signed (d : Nat) (datasize : Nat) (esize : Nat) (idxdsize : Nat) (index : Int) (n : Nat) : SailM Unit := do
  if ((index == 0) : Bool)
  then (CheckFPEnabled64 ())
  else (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n idxdsize) ) : SailM (BitVec idxdsize) )
  (X_set d datasize (sign_extend (← (Elem_read operand index esize)) datasize))

/-- Type quantifiers: d : Nat, datasize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (X_read m datasize) ) : SailM (BitVec datasize) )
  let result ← do (pure ((← (asl_Int operand1 is_unsigned)) *i (← (asl_Int operand2 is_unsigned))))
  (X_set d 64 (integer_subrange result 127 64))

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (Vpart_read n part datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (Vpart_read m part datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let (element1, element2, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result) := loop_vars
      loop_vars ← do
        let element1 ← (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let result ← (Elem_set result e (2 *i esize) (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0))
        (pure (element1, element2, result))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec (2 * datasize))) )
  (V_set d (2 *i datasize) result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem idxdsize [64, 128] ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_long (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) (part : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (Vpart_read n part datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m idxdsize) ) : SailM (BitVec idxdsize) )
  let result ← (( do (undefined_bitvector (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let product ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  let element2 ← do (asl_Int (← (Elem_read operand2 index esize)) is_unsigned)
  let (element1, product, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, product, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, product, result) := loop_vars
      loop_vars ← do
        let element1 ← (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let product : (BitVec (2 * esize)) := (integer_subrange (element1 *i element2) ((2 *i esize) -i 1) 0)
        let result ← (Elem_set result e (2 *i esize) product)
        (pure (element1, product, result))
    (pure loop_vars) ) : SailM (Int × (BitVec (2 * esize)) × (BitVec (2 * datasize))) )
  (V_set d (2 *i datasize) result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, k_neg : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (neg : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int ()) ) : SailM Int )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let (element, result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result, sat) := loop_vars
      loop_vars ← do
        let element ← (pure (BitVec.toInt (← (Elem_read operand e esize))))
        let element : Int :=
          if (neg : Bool)
          then (Neg.neg element)
          else (Int.natAbs element)
        let (result, sat) ← (( do
          let (__tup_0, __tup_1) ← do (SignedSatQ element esize)
          let result ← (Elem_set result e esize __tup_0)
          let sat : Bool := __tup_1
          (pure (result, sat)) ) : SailM ((BitVec datasize) × Bool) )
        if (sat : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (element, result, sat))
    (pure loop_vars) ) : SailM (Int × (BitVec datasize) × Bool) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let sum ← (( do (undefined_int ()) ) : SailM Int )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let (element1, element2, result, sat, sum) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result, sat, sum)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result, sat, sum) := loop_vars
      loop_vars ← do
        let element1 ← (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let sum : Int := (element1 +i element2)
        let (result, sat) ← (( do
          let (__tup_0, __tup_1) ← do (SatQ sum esize is_unsigned)
          let result ← (Elem_set result e esize __tup_0)
          let sat : Bool := __tup_1
          (pure (result, sat)) ) : SailM ((BitVec datasize) × Bool) )
        if (sat : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (element1, element2, result, sat, sum))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec datasize) × Bool × Int) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index : Nat, m : Nat, n : Nat, part : Nat, k_sub_op : Bool, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem idxdsize [64, 128] ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) (part : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (Vpart_read n part datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m idxdsize) ) : SailM (BitVec idxdsize) )
  let operand3 ← (( do (V_read d (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let result ← (( do (undefined_bitvector (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let product ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  let accum ← (( do (undefined_int ()) ) : SailM Int )
  let sat1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let sat2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 index esize))))
  let (accum, element1, product, result, sat1, sat2) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (accum, element1, product, result, sat1, sat2)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (accum, element1, product, result, sat1, sat2) := loop_vars
      loop_vars ← do
        let element1 ← (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let (product, sat1) ← (( do
          let (tup__0, tup__1) ← do (SignedSatQ ((2 *i element1) *i element2) (2 *i esize))
          let product : (BitVec (2 * esize)) := tup__0
          let sat1 : Bool := tup__1
          (pure (product, sat1)) ) : SailM ((BitVec (2 * esize)) × Bool) )
        let accum ← (( do
          if (sub_op : Bool)
          then (do (pure ((BitVec.toInt (← (Elem_read operand3 e (2 *i esize)))) -i (BitVec.toInt product))))
          else (do (pure ((BitVec.toInt (← (Elem_read operand3 e (2 *i esize)))) +i (BitVec.toInt product)))) ) : SailM Int )
        let (result, sat2) ← (( do
          let (__tup_0, __tup_1) ← do (SignedSatQ accum (2 *i esize))
          let result ← (Elem_set result e (2 *i esize) __tup_0)
          let sat2 : Bool := __tup_1
          (pure (result, sat2)) ) : SailM ((BitVec (2 * datasize)) × Bool) )
        if ((sat1 || sat2) : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (accum, element1, product, result, sat1, sat2))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec (2 * esize)) × (BitVec (2 * datasize)) × Bool × Bool) )
  (V_set d (2 *i datasize) result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, part : Nat, k_sub_op : Bool, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (Vpart_read n part datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (Vpart_read m part datasize) ) : SailM (BitVec datasize) )
  let operand3 ← (( do (V_read d (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let result ← (( do (undefined_bitvector (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let product ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  let accum ← (( do (undefined_int ()) ) : SailM Int )
  let sat1 ← (( do (undefined_bool ()) ) : SailM Bool )
  let sat2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let (accum, element1, element2, product, result, sat1, sat2) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (accum, element1, element2, product, result, sat1, sat2)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (accum, element1, element2, product, result, sat1, sat2) := loop_vars
      loop_vars ← do
        let element1 ← (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
        let (product, sat1) ← (( do
          let (tup__0, tup__1) ← do (SignedSatQ ((2 *i element1) *i element2) (2 *i esize))
          let product : (BitVec (2 * esize)) := tup__0
          let sat1 : Bool := tup__1
          (pure (product, sat1)) ) : SailM ((BitVec (2 * esize)) × Bool) )
        let accum ← (( do
          if (sub_op : Bool)
          then (do (pure ((BitVec.toInt (← (Elem_read operand3 e (2 *i esize)))) -i (BitVec.toInt product))))
          else (do (pure ((BitVec.toInt (← (Elem_read operand3 e (2 *i esize)))) +i (BitVec.toInt product)))) ) : SailM Int )
        let (result, sat2) ← (( do
          let (__tup_0, __tup_1) ← do (SignedSatQ accum (2 *i esize))
          let result ← (Elem_set result e (2 *i esize) __tup_0)
          let sat2 : Bool := __tup_1
          (pure (result, sat2)) ) : SailM ((BitVec (2 * datasize)) × Bool) )
        if ((sat1 || sat2) : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (accum, element1, element2, product, result, sat1, sat2))
    (pure loop_vars) ) : SailM (Int × Int × Int × (BitVec (2 * esize)) × (BitVec (2 * datasize)) × Bool × Bool) )
  (V_set d (2 *i datasize) result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, k_rounding : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (rounding : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let product ← (( do (undefined_int ()) ) : SailM Int )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let (element1, element2, product, result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, product, result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, product, result, sat) := loop_vars
      loop_vars ← do
        let element1 ← (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
        let product : Int := ((2 *i element1) *i element2)
        let product ← (RShr product esize rounding)
        let (result, sat) ← (( do
          let (__tup_0, __tup_1) ← do (SignedSatQ product esize)
          let result ← (Elem_set result e esize __tup_0)
          let sat : Bool := __tup_1
          (pure (result, sat)) ) : SailM ((BitVec datasize) × Bool) )
        if (sat : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (element1, element2, product, result, sat))
    (pure loop_vars) ) : SailM (Int × Int × Int × (BitVec datasize) × Bool) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index : Nat, m : Nat, n : Nat, k_round : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem idxdsize [64, 128] ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) (round : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m idxdsize) ) : SailM (BitVec idxdsize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let product ← (( do (undefined_int ()) ) : SailM Int )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 index esize))))
  let (element1, product, result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, product, result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, product, result, sat) := loop_vars
      loop_vars ← do
        let element1 ← (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let product : Int := ((2 *i element1) *i element2)
        let product ← (RShr product esize round)
        let (result, sat) ← (( do
          let (__tup_0, __tup_1) ← do (SignedSatQ product esize)
          let result ← (Elem_set result e esize __tup_0)
          let sat : Bool := __tup_1
          (pure (result, sat)) ) : SailM ((BitVec datasize) × Bool) )
        if (sat : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (element1, product, result, sat))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec datasize) × Bool) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (Vpart_read n part datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (Vpart_read m part datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let product ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let (element1, element2, product, result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, product, result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, product, result, sat) := loop_vars
      loop_vars ← do
        let element1 ← (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
        let (product, sat) ← (( do
          let (tup__0, tup__1) ← do (SignedSatQ ((2 *i element1) *i element2) (2 *i esize))
          let product : (BitVec (2 * esize)) := tup__0
          let sat : Bool := tup__1
          (pure (product, sat)) ) : SailM ((BitVec (2 * esize)) × Bool) )
        let result ← (Elem_set result e (2 *i esize) product)
        if (sat : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (element1, element2, product, result, sat))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec (2 * esize)) × (BitVec (2 * datasize)) × Bool) )
  (V_set d (2 *i datasize) result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index : Nat, m : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem idxdsize [64, 128] ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (Vpart_read n part datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m idxdsize) ) : SailM (BitVec idxdsize) )
  let result ← (( do (undefined_bitvector (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let product ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 index esize))))
  let (element1, product, result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, product, result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, product, result, sat) := loop_vars
      loop_vars ← do
        let element1 ← (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let (product, sat) ← (( do
          let (tup__0, tup__1) ← do (SignedSatQ ((2 *i element1) *i element2) (2 *i esize))
          let product : (BitVec (2 * esize)) := tup__0
          let sat : Bool := tup__1
          (pure (product, sat)) ) : SailM ((BitVec (2 * esize)) × Bool) )
        let result ← (Elem_set result e (2 *i esize) product)
        if (sat : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (element1, product, result, sat))
    (pure loop_vars) ) : SailM (Int × (BitVec (2 * esize)) × (BitVec (2 * datasize)) × Bool) )
  (V_set d (2 *i datasize) result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, k_rounding : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (rounding : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let operand3 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let element3 ← (( do (undefined_int ()) ) : SailM Int )
  let accum ← (( do (undefined_int ()) ) : SailM Int )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let (accum, element1, element2, element3, result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (accum, element1, element2, element3, result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (accum, element1, element2, element3, result, sat) := loop_vars
      loop_vars ← do
        let element1 ← (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element2 ← (pure (BitVec.toInt (← (Elem_read operand2 e esize))))
        let element3 ← (pure (BitVec.toInt (← (Elem_read operand3 e esize))))
        let accum : Int :=
          if (sub_op : Bool)
          then ((Int.shiftl element3 esize) -i (2 *i (element1 *i element2)))
          else ((Int.shiftl element3 esize) +i (2 *i (element1 *i element2)))
        let accum ← (RShr accum esize rounding)
        let (result, sat) ← (( do
          let (__tup_0, __tup_1) ← do (SignedSatQ accum esize)
          let result ← (Elem_set result e esize __tup_0)
          let sat : Bool := __tup_1
          (pure (result, sat)) ) : SailM ((BitVec datasize) × Bool) )
        if (sat : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (accum, element1, element2, element3, result, sat))
    (pure loop_vars) ) : SailM (Int × Int × Int × Int × (BitVec datasize) × Bool) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, idxdsize : Nat, index : Nat, m : Nat, n : Nat, k_rounding : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem idxdsize [64, 128] ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (idxdsize : Nat) (index : Nat) (m : Nat) (n : Nat) (rounding : Bool) (sub_op : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m idxdsize) ) : SailM (BitVec idxdsize) )
  let operand3 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element3 ← (( do (undefined_int ()) ) : SailM Int )
  let accum ← (( do (undefined_int ()) ) : SailM Int )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 index esize))))
  let (accum, element1, element3, result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (accum, element1, element3, result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (accum, element1, element3, result, sat) := loop_vars
      loop_vars ← do
        let element1 ← (pure (BitVec.toInt (← (Elem_read operand1 e esize))))
        let element3 ← (pure (BitVec.toInt (← (Elem_read operand3 e esize))))
        let accum : Int :=
          if (sub_op : Bool)
          then ((Int.shiftl element3 esize) -i (2 *i (element1 *i element2)))
          else ((Int.shiftl element3 esize) +i (2 *i (element1 *i element2)))
        let accum ← (RShr accum esize rounding)
        let (result, sat) ← (( do
          let (__tup_0, __tup_1) ← do (SignedSatQ accum esize)
          let result ← (Elem_set result e esize __tup_0)
          let sat : Bool := __tup_1
          (pure (result, sat)) ) : SailM ((BitVec datasize) × Bool) )
        if (sat : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (accum, element1, element3, result, sat))
    (pure loop_vars) ) : SailM (Int × Int × Int × (BitVec datasize) × Bool) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, k_rounding : Bool, k_saturating : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (rounding : Bool) (saturating : Bool) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let (result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (result, sat) := loop_vars
      loop_vars ← do
        let element ← (( do (asl_Int (← (Elem_read operand1 e esize)) is_unsigned) ) : SailM Int )
        let shift ← (( do (pure (BitVec.toInt (Sail.BitVec.extractLsb (← (Elem_read operand2 e esize)) 7 0))) ) : SailM Int )
        let element ← (( do
          if ((shift ≥b 0) : Bool)
          then (pure (_shl_int_general element shift))
          else
            (do
              let shift := (Neg.neg shift)
              (RShr element shift rounding)) ) : SailM Int )
        let element := element
        let (result, sat) ← (( do
          if (saturating : Bool)
          then
            (do
              let (result, sat) ← (( do
                let (__tup_0, __tup_1) ← do (SatQ element esize is_unsigned)
                let result ← (Elem_set result e esize __tup_0)
                let sat : Bool := __tup_1
                (pure (result, sat)) ) : SailM ((BitVec datasize) × Bool) )
              if (sat : Bool)
              then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
              else (pure ())
              (pure (result, sat)))
          else
            (do
              let result ← (Elem_set result e esize (integer_subrange element (esize -i 1) 0))
              (pure (result, sat))) ) : SailM ((BitVec datasize) × Bool) )
        (pure (result, sat))
    (pure loop_vars) ) : SailM ((BitVec datasize) × Bool) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n : Nat, part : Nat, k_round : Bool, shift : Int, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [4, 8, 16, 32, 64] ∧ List.elem datasize [4, 8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) (round : Bool) (shift : Int) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n (datasize *i 2)) ) : SailM (BitVec (datasize * 2)) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int ()) ) : SailM Int )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let (element, result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result, sat) := loop_vars
      loop_vars ← do
        let element ← (RShr (← (asl_Int (← (Elem_read operand e (2 *i esize))) is_unsigned)) shift round)
        let (result, sat) ← (( do
          let (__tup_0, __tup_1) ← do (SatQ element esize is_unsigned)
          let result ← (Elem_set result e esize __tup_0)
          let sat : Bool := __tup_1
          (pure (result, sat)) ) : SailM ((BitVec datasize) × Bool) )
        if (sat : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (element, result, sat))
    (pure loop_vars) ) : SailM (Int × (BitVec datasize) × Bool) )
  (Vpart_set d part datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, part : Nat, k_round : Bool, shift : Int, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [4, 8, 16, 32, 64] ∧ List.elem datasize [4, 8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) (round : Bool) (shift : Int) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n (datasize *i 2)) ) : SailM (BitVec (datasize * 2)) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int ()) ) : SailM Int )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let (element, result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result, sat) := loop_vars
      loop_vars ← do
        let element ← (RShr (BitVec.toInt (← (Elem_read operand e (2 *i esize)))) shift round)
        let (result, sat) ← (( do
          let (__tup_0, __tup_1) ← do (UnsignedSatQ element esize)
          let result ← (Elem_set result e esize __tup_0)
          let sat : Bool := __tup_1
          (pure (result, sat)) ) : SailM ((BitVec datasize) × Bool) )
        if (sat : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (element, result, sat))
    (pure loop_vars) ) : SailM (Int × (BitVec datasize) × Bool) )
  (Vpart_set d part datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, k_dst_unsigned : Bool, elements : Int, esize : Nat, n : Nat, shift : Int, k_src_unsigned : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [4, 8, 16, 32, 64] ∧ List.elem datasize [4, 8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_left_sat_sisd (d : Nat) (datasize : Nat) (dst_unsigned : Bool) (elements : Int) (esize : Nat) (n : Nat) (shift : Int) (src_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:48981.56-48981.57"
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int ()) ) : SailM Int )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let (element, result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result, sat) := loop_vars
      loop_vars ← do
        let element ← (pure (_shl_int_general (← (asl_Int (← (Elem_read operand e esize)) src_unsigned)) shift))
        let (result, sat) ← (( do
          let (__tup_0, __tup_1) ← do (SatQ element esize dst_unsigned)
          let result ← (Elem_set result e esize __tup_0)
          let sat : Bool := __tup_1
          (pure (result, sat)) ) : SailM ((BitVec datasize) × Bool) )
        if (sat : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (element, result, sat))
    (pure loop_vars) ) : SailM (Int × (BitVec datasize) × Bool) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let diff ← (( do (undefined_int ()) ) : SailM Int )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let (diff, element1, element2, result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (diff, element1, element2, result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (diff, element1, element2, result, sat) := loop_vars
      loop_vars ← do
        let element1 ← (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let diff : Int := (element1 -i element2)
        let (result, sat) ← (( do
          let (__tup_0, __tup_1) ← do (SatQ diff esize is_unsigned)
          let result ← (Elem_set result e esize __tup_0)
          let sat : Bool := __tup_1
          (pure (result, sat)) ) : SailM ((BitVec datasize) × Bool) )
        if (sat : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (diff, element1, element2, result, sat))
    (pure loop_vars) ) : SailM (Int × Int × Int × (BitVec datasize) × Bool) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n : Nat, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let (element, result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result, sat) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e (2 *i esize))
        let (result, sat) ← (( do
          let (__tup_0, __tup_1) ← do (SatQ (← (asl_Int element is_unsigned)) esize is_unsigned)
          let result ← (Elem_set result e esize __tup_0)
          let sat : Bool := __tup_1
          (pure (result, sat)) ) : SailM ((BitVec datasize) × Bool) )
        if (sat : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (element, result, sat))
    (pure loop_vars) ) : SailM ((BitVec (2 * esize)) × (BitVec datasize) × Bool) )
  (Vpart_set d part datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let (element, result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result, sat) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e (2 *i esize))
        let (result, sat) ← (( do
          let (__tup_0, __tup_1) ← do (UnsignedSatQ (BitVec.toInt element) esize)
          let result ← (Elem_set result e esize __tup_0)
          let sat : Bool := __tup_1
          (pure (result, sat)) ) : SailM ((BitVec datasize) × Bool) )
        if (sat : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (element, result, sat))
    (pure loop_vars) ) : SailM ((BitVec (2 * esize)) × (BitVec datasize) × Bool) )
  (Vpart_set d part datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element1 ← (( do (undefined_int ()) ) : SailM Int )
  let element2 ← (( do (undefined_int ()) ) : SailM Int )
  let sum ← (( do (undefined_int ()) ) : SailM Int )
  let (element1, element2, result, sum) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element1, element2, result, sum)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element1, element2, result, sum) := loop_vars
      loop_vars ← do
        let element1 ← (asl_Int (← (Elem_read operand1 e esize)) is_unsigned)
        let element2 ← (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let sum : Int := (Int.shiftr ((element1 +i element2) +i 1) 1)
        let result ← (Elem_set result e esize (integer_subrange sum (esize -i 1) 0))
        (pure (element1, element2, result, sum))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec datasize) × Int) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Int, elements : Int, esize : Int, n : Nat, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_right_insert_sisd (d : Nat) (datasize : Int) (elements : Int) (esize : Int) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:49719.56-49719.57"
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  sail_assert (esize ≥b 0) "src/instrs64.sail:49723.34-49723.35"
  let mask : (BitVec esize) := ((Ones (n := esize)) >>> shift)
  let shifted ← (( do (undefined_bitvector esize) ) : SailM (BitVec esize) )
  let (result, shifted) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (result, shifted)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (result, shifted) := loop_vars
      loop_vars ← do
        sail_assert (((e *i esize) ≤b (((e *i esize) +i esize) -i 1)) || ((! ((e ≥b 0) && (((e +i 1) *i esize) ≤b datasize))) || ((! (esize ≥b 0)) || (! (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)))))) "src/instrs64.sail:49727.198-49727.199"
        let shifted ← (pure ((← (Elem_read operand e esize)) >>> shift))
        let result ← (Elem_set result e esize (((← (Elem_read operand2 e esize)) &&& (Complement.complement mask)) ||| shifted))
        (pure (result, shifted))
    (pure loop_vars) ) : SailM ((BitVec datasize) × (BitVec esize)) )
  (V_set d datasize result)

/-- Type quantifiers: k_accumulate : Bool, d : Nat, datasize : Int, elements : Int, esize : Int, k_is_unsigned : Bool, n : Nat, k_round : Bool, shift : Int, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_right_sisd (accumulate : Bool) (d : Nat) (datasize : Int) (elements : Int) (esize : Int) (n : Nat) (round : Bool) (shift : Int) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  sail_assert (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) "src/instrs64.sail:49792.56-49792.57"
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_int ()) ) : SailM Int )
  let operand2 ← (( do
    if (accumulate : Bool)
    then (V_read d datasize)
    else (pure (Zeros (n := datasize))) ) : SailM (BitVec datasize) )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        sail_assert (esize ≥b 0) "src/instrs64.sail:49799.38-49799.39"
        sail_assert (((e *i esize) ≤b (((e *i esize) +i esize) -i 1)) || ((! ((e ≥b 0) && (((e +i 1) *i esize) ≤b datasize))) || (! (((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128))))) "src/instrs64.sail:49800.179-49800.180"
        let element ← (RShr (← (asl_Int (← (Elem_read operand e esize)) is_unsigned)) shift round)
        let result ← (Elem_set result e esize ((← (Elem_read operand2 e esize)) + (integer_subrange element (esize -i 1) 0)))
        (pure (element, result))
    (pure loop_vars) ) : SailM (Int × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n : Nat, part : Nat, shift : Int, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [4, 8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_left_long (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) (shift : Int) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (Vpart_read n part datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector (datasize *i 2)) ) : SailM (BitVec (datasize * 2)) )
  let element ← (( do (undefined_int ()) ) : SailM Int )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (pure (_shl_int_general (← (asl_Int (← (Elem_read operand e esize)) is_unsigned)) shift))
        let result ← (Elem_set result e (2 *i esize) (integer_subrange element ((2 *i esize) -i 1) 0))
        (pure (element, result))
    (pure loop_vars) ) : SailM (Int × (BitVec (datasize * 2))) )
  (V_set d (datasize *i 2) result)

/-- Type quantifiers: n : Nat, k_postindex : Bool, t : Nat, k_writeback : Bool, k_zero_data : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcsettagpairpost (n : Nat) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (writeback : Bool) (zero_data : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data ← (( do
    if ((t == 31) : Bool)
    then (SP_read ())
    else (X_read t 64) ) : SailM (BitVec 64) )
  let tag : (BitVec 4) := (AArch64_AllocationTagFromAddress data)
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_STORE) ) : SailM AccessDescriptor )
  if (zero_data : Bool)
  then
    (do
      if ((! (IsAligned__1 address TAG_GRANULE)) : Bool)
      then (AArch64_Abort address (← (AlignmentFault accdesc)))
      else (pure ())
      (Mem_set address TAG_GRANULE accdesc (Zeros (n := (TAG_GRANULE *i 8))))
      (Mem_set (BitVec.addInt address TAG_GRANULE) TAG_GRANULE accdesc (Zeros (n := (TAG_GRANULE *i 8)))))
  else (pure ())
  (AArch64_MemTag_set address accdesc tag)
  (AArch64_MemTag_set (BitVec.addInt address TAG_GRANULE) accdesc tag)
  if (writeback : Bool)
  then
    (do
      let address : (BitVec 64) :=
        if (postindex : Bool)
        then (address + offset)
        else address
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())

/-- Type quantifiers: n : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_atomicops_st_acc_st64b (lst : (BitVec 2)) (memop : MemOp) (n : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  (CheckLDST64BEnabled ())
  let data ← (( do (undefined_bitvector 512) ) : SailM (BitVec 512) )
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let value_name ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescLS64 memop tagchecked) ) : SailM AccessDescriptor )
  let (data, value_name) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 7
    let mut loop_vars := (data, value_name)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (data, value_name) := loop_vars
      loop_vars ← do
        let value_name ← (X_read (t +i i) 64)
        let value_name ← (( do
          if ((← (BigEndian accdesc.acctype)) : Bool)
          then (pure (reverse_endianness value_name))
          else (pure value_name) ) : SailM (BitVec 64) )
        let data : (BitVec 512) := (Sail.BitVec.updateSubrange data (63 +i (64 *i i)) (64 *i i) value_name)
        (pure (data, value_name))
    (pure loop_vars) ) : SailM ((BitVec 512) × (BitVec 64)) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let _ : Unit := (SetLoadStoreType lst)
  let _ : Unit := (AArch64_SetLSInstructionSyndrome 64 false t true false)
  (MemStore64B address data accdesc)
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleGeneralPurposeLoadStore ())
  else (pure ())

/-- Type quantifiers: n : Nat, s : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_atomicops_st_acc_st64bv (Rs : (BitVec 5)) (lst : (BitVec 2)) (memop : MemOp) (n : Nat) (s : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  (CheckST64BVEnabled ())
  let data ← (( do (undefined_bitvector 512) ) : SailM (BitVec 512) )
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let value_name ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescLS64 memop tagchecked) ) : SailM AccessDescriptor )
  let (data, value_name) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 7
    let mut loop_vars := (data, value_name)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (data, value_name) := loop_vars
      loop_vars ← do
        let value_name ← (X_read (t +i i) 64)
        let value_name ← (( do
          if ((← (BigEndian accdesc.acctype)) : Bool)
          then (pure (reverse_endianness value_name))
          else (pure value_name) ) : SailM (BitVec 64) )
        let data : (BitVec 512) := (Sail.BitVec.updateSubrange data (63 +i (64 *i i)) (64 *i i) value_name)
        (pure (data, value_name))
    (pure loop_vars) ) : SailM ((BitVec 512) × (BitVec 64)) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let _ : Unit := (SetLoadStoreType lst)
  let _ : Unit := (AArch64_SetLSInstructionSyndrome 64 false t true false)
  let _ : Unit := (SetIss2 Rs)
  let status ← (( do (MemStore64BWithRet address data accdesc) ) : SailM (BitVec 64) )
  if ((s != 31) : Bool)
  then (X_set s 64 status)
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleGeneralPurposeLoadStore ())
  else (pure ())

/-- Type quantifiers: n : Nat, s : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_atomicops_st_acc_st64bv0 (Rs : (BitVec 5)) (lst : (BitVec 2)) (memop : MemOp) (n : Nat) (s : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  (CheckST64BV0Enabled ())
  let data ← (( do (undefined_bitvector 512) ) : SailM (BitVec 512) )
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let value_name ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescLS64 memop tagchecked) ) : SailM AccessDescriptor )
  let Xt ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value_name ← (pure (Sail.BitVec.updateSubrange value_name 31 0 (Sail.BitVec.extractLsb (← readReg ACCDATA_EL1) 31 0)))
  let value_name : (BitVec 64) := (Sail.BitVec.updateSubrange value_name 63 32 (Sail.BitVec.extractLsb Xt 63 32))
  let value_name ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (reverse_endianness value_name))
    else (pure value_name) ) : SailM (BitVec 64) )
  let data : (BitVec 512) := (Sail.BitVec.updateSubrange data 63 0 value_name)
  let (data, value_name) ← (( do
    let loop_i_lower := 1
    let loop_i_upper := 7
    let mut loop_vars := (data, value_name)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (data, value_name) := loop_vars
      loop_vars ← do
        let value_name ← (X_read (t +i i) 64)
        let value_name ← (( do
          if ((← (BigEndian accdesc.acctype)) : Bool)
          then (pure (reverse_endianness value_name))
          else (pure value_name) ) : SailM (BitVec 64) )
        let data : (BitVec 512) := (Sail.BitVec.updateSubrange data (63 +i (64 *i i)) (64 *i i) value_name)
        (pure (data, value_name))
    (pure loop_vars) ) : SailM ((BitVec 512) × (BitVec 64)) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let _ : Unit := (SetLoadStoreType lst)
  let _ : Unit := (AArch64_SetLSInstructionSyndrome 64 false t true false)
  let _ : Unit := (SetIss2 Rs)
  let status ← (( do (MemStore64BWithRet address data accdesc) ) : SailM (BitVec 64) )
  if ((s != 31) : Bool)
  then (X_set s 64 status)
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleGeneralPurposeLoadStore ())
  else (pure ())

/-- Type quantifiers: n : Nat, k_postindex : Bool, t : Nat, k_writeback : Bool, k_zero_data : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcsettagpost (n : Nat) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (writeback : Bool) (zero_data : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_STORE) ) : SailM AccessDescriptor )
  if (zero_data : Bool)
  then
    (do
      if ((! (IsAligned__1 address TAG_GRANULE)) : Bool)
      then (AArch64_Abort address (← (AlignmentFault accdesc)))
      else (pure ())
      (Mem_set address TAG_GRANULE accdesc (Zeros (n := (TAG_GRANULE *i 8)))))
  else (pure ())
  let data ← (( do
    if ((t == 31) : Bool)
    then (SP_read ())
    else (X_read t 64) ) : SailM (BitVec 64) )
  let tag : (BitVec 4) := (AArch64_AllocationTagFromAddress data)
  (AArch64_MemTag_set address accdesc tag)
  if (writeback : Bool)
  then
    (do
      let address : (BitVec 64) :=
        if (postindex : Bool)
        then (address + offset)
        else address
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcsettagarray (n : Nat) (t : Nat) : SailM Unit := do
  if (((← readReg PSTATE).EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let data ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let size ← do (pure (4 *i (2 ^i (BitVec.toNat (_get_GMID_EL1_Type_BS (← readReg GMID_EL1))))))
  let address : (BitVec 64) := (Align_bits address size)
  let count := (Int.shiftr size LOG2_TAG_GRANULE)
  let index : Int := (BitVec.toNat (Sail.BitVec.extractLsb address (LOG2_TAG_GRANULE +i 3) LOG2_TAG_GRANULE))
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_STORE) ) : SailM AccessDescriptor )
  let (address, index) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (count -i 1)
    let mut loop_vars := (address, index)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (address, index) := loop_vars
      loop_vars ← do
        let tag ← (( do
          let index := index
          sail_assert ((0 ≤b (index *i 4)) && (((index *i 4) +i 3) <b 64)) "src/instrs64.sail:50826.72-50826.73"
          (pure (Sail.BitVec.extractLsb data ((index *i 4) +i 3) (index *i 4))) ) : SailM (BitVec 4) )
        (AArch64_MemTag_set address accdesc tag)
        let address : (BitVec 64) := (BitVec.addInt address TAG_GRANULE)
        let index : Int := (index +i 1)
        (pure (address, index))
    (pure loop_vars) ) : SailM ((BitVec 64) × Int) )
  (pure ())

/-- Type quantifiers: n : Nat, k_postindex : Bool, t : Nat, t2 : Nat, k_writeback : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcsettaganddatapairpost (n : Nat) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (t2 : Nat) (writeback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let data1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let data2 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_STORE) ) : SailM AccessDescriptor )
  if ((! (IsAligned__1 address TAG_GRANULE)) : Bool)
  then (AArch64_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  (Mem_set address 8 accdesc data1)
  (Mem_set (BitVec.addInt address 8) 8 accdesc data2)
  (AArch64_MemTag_set address accdesc (AArch64_AllocationTagFromAddress address))
  if (writeback : Bool)
  then
    (do
      let address : (BitVec 64) :=
        if (postindex : Bool)
        then (address + offset)
        else address
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())

/-- Type quantifiers: datasize : Nat, n : Nat, offset : Int, k_postindex : Bool, k_rt_unknown : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] -/
def execute_aarch64_instrs_memory_ordered_pair_stilp (datasize : Nat) (memop : MemOp) (n : Nat) (offset : Int) (postindex : Bool) (rt_unknown : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data1 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let data2 ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let dbytes := (Int.ediv datasize 8)
  let accdesc ← (( do (CreateAccDescAcqRel memop tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (BitVec.addInt address offset)
    else address
  match memop with
  | .MemOp_STORE =>
    (do
      let data1 ← (( do
        if ((rt_unknown && (t == n)) : Bool)
        then (do (__UNKNOWN_bits datasize))
        else (do (X_read t datasize)) ) : SailM (BitVec datasize) )
      let data2 ← (( do
        if ((rt_unknown && (t2 == n)) : Bool)
        then (do (__UNKNOWN_bits datasize))
        else (do (X_read t2 datasize)) ) : SailM (BitVec datasize) )
      if ((← (HaveLSE2Ext ())) : Bool)
      then
        (do
          let full_data ← (( do (undefined_bitvector (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
          let full_data ← (( do
            if ((← (BigEndian accdesc.acctype)) : Bool)
            then (pure (data1 +++ data2))
            else (pure (data2 +++ data1)) ) : SailM (BitVec (2 * datasize)) )
          let ispair : Bool := true
          let highestAddressfirst : Bool := ((! postindex) && (offset <b 0))
          (Mem_set__2 address (2 *i dbytes) accdesc ispair highestAddressfirst full_data))
      else
        (do
          if (((! postindex) && (offset <b 0)) : Bool)
          then
            (do
              (Mem_set (BitVec.addInt address dbytes) dbytes accdesc data2)
              (Mem_set (BitVec.addInt address 0) dbytes accdesc data1))
          else
            (do
              (Mem_set (BitVec.addInt address 0) dbytes accdesc data1)
              (Mem_set (BitVec.addInt address dbytes) dbytes accdesc data2))))
  | .MemOp_LOAD =>
    (do
      let (data1, data2) ← (( do
        if ((← (HaveLSE2Ext ())) : Bool)
        then
          (do
            let ispair : Bool := true
            let full_data ← (( do (Mem_read__1 address (2 *i dbytes) accdesc ispair) ) : SailM (BitVec (2 * datasize)) )
            let (data1, data2) ← (( do
              if ((← (BigEndian accdesc.acctype)) : Bool)
              then
                (let data2 : (BitVec datasize) := (Sail.BitVec.extractLsb full_data (datasize -i 1) 0)
                let data1 : (BitVec datasize) := (Sail.BitVec.extractLsb full_data ((2 *i datasize) -i 1) datasize)
                (pure (data1, data2)))
              else
                (let data1 : (BitVec datasize) := (Sail.BitVec.extractLsb full_data (datasize -i 1) 0)
                let data2 : (BitVec datasize) := (Sail.BitVec.extractLsb full_data ((2 *i datasize) -i 1) datasize)
                (pure (data1, data2))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
            (pure (data1, data2)))
        else
          (do
            let data1 ← (Mem_read (BitVec.addInt address 0) dbytes accdesc)
            let data2 ← (Mem_read (BitVec.addInt address dbytes) dbytes accdesc)
            (pure (data1, data2))) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      let (data1, data2) ← (( do
        if (rt_unknown : Bool)
        then
          (do
            let data1 ← (__UNKNOWN_bits datasize)
            let data2 ← (__UNKNOWN_bits datasize)
            (pure (data1, data2)))
        else (pure (data1, data2)) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
      (X_set t datasize data1)
      (X_set t2 datasize data2))
  | _ => (pure ())
  if (wback : Bool)
  then
    (do
      let address ← (( do
        if (wb_unknown : Bool)
        then (do (__UNKNOWN_bits 64))
        else
          (if (postindex : Bool)
          then (pure (BitVec.addInt address offset))
          else (pure address)) ) : SailM (BitVec 64) )
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then (SPESampleGeneralPurposeLoadStore ())
  else (pure ())

/-- Type quantifiers: n : Nat, k_postindex : Bool, t : Nat, k_writeback : Bool, k_zero_data : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcsettagpairandzerodatapost (n : Nat) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (writeback : Bool) (zero_data : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let data ← (( do
    if ((t == 31) : Bool)
    then (SP_read ())
    else (X_read t 64) ) : SailM (BitVec 64) )
  let tag : (BitVec 4) := (AArch64_AllocationTagFromAddress data)
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_STORE) ) : SailM AccessDescriptor )
  if (zero_data : Bool)
  then
    (do
      if ((! (IsAligned__1 address TAG_GRANULE)) : Bool)
      then (AArch64_Abort address (← (AlignmentFault accdesc)))
      else (pure ())
      (Mem_set address TAG_GRANULE accdesc (Zeros (n := (TAG_GRANULE *i 8))))
      (Mem_set (BitVec.addInt address TAG_GRANULE) TAG_GRANULE accdesc (Zeros (n := (TAG_GRANULE *i 8)))))
  else (pure ())
  (AArch64_MemTag_set address accdesc tag)
  (AArch64_MemTag_set (BitVec.addInt address TAG_GRANULE) accdesc tag)
  if (writeback : Bool)
  then
    (do
      let address : (BitVec 64) :=
        if (postindex : Bool)
        then (address + offset)
        else address
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())

/-- Type quantifiers: n : Nat, k_postindex : Bool, t : Nat, k_writeback : Bool, k_zero_data : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcsettagandzerodatapost (n : Nat) (offset : (BitVec 64)) (postindex : Bool) (t : Nat) (writeback : Bool) (zero_data : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    if ((! postindex) : Bool)
    then (address + offset)
    else address
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_STORE) ) : SailM AccessDescriptor )
  if (zero_data : Bool)
  then
    (do
      if ((! (IsAligned__1 address TAG_GRANULE)) : Bool)
      then (AArch64_Abort address (← (AlignmentFault accdesc)))
      else (pure ())
      (Mem_set address TAG_GRANULE accdesc (Zeros (n := (TAG_GRANULE *i 8)))))
  else (pure ())
  let data ← (( do
    if ((t == 31) : Bool)
    then (SP_read ())
    else (X_read t 64) ) : SailM (BitVec 64) )
  let tag : (BitVec 4) := (AArch64_AllocationTagFromAddress data)
  (AArch64_MemTag_set address accdesc tag)
  if (writeback : Bool)
  then
    (do
      let address : (BitVec 64) :=
        if (postindex : Bool)
        then (address + offset)
        else address
      if ((n == 31) : Bool)
      then (SP_set address)
      else (X_set n 64 address))
  else (pure ())

/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcsettagandzeroarray (n : Nat) (t : Nat) : SailM Unit := do
  if (((← readReg PSTATE).EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let data ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let tag : (BitVec 4) := (Sail.BitVec.extractLsb data 3 0)
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let size ← do (pure (4 *i (2 ^i (BitVec.toNat (_get_DCZID_EL0_Type_BS (← readReg DCZID_EL0))))))
  let address : (BitVec 64) := (Align_bits address size)
  let count := (Int.shiftr size LOG2_TAG_GRANULE)
  let accdesc ← (( do (CreateAccDescLDGSTG MemOp_STORE) ) : SailM AccessDescriptor )
  let address ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (count -i 1)
    let mut loop_vars := address
    for i in [loop_i_lower:loop_i_upper:1]i do
      let address := loop_vars
      loop_vars ← do
        (AArch64_MemTag_set address accdesc tag)
        (Mem_set address TAG_GRANULE accdesc (Zeros (n := (8 *i TAG_GRANULE))))
        (pure (BitVec.addInt address TAG_GRANULE))
    (pure loop_vars) ) : SailM (BitVec 64) )
  (pure ())

/-- Type quantifiers: k_ADD : Bool, d : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcsubtag (ADD : Bool) (d : Nat) (n : Nat) (offset : (BitVec 64)) (tag_offset : (BitVec 4)) : SailM Unit := do
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then (SP_read ())
    else (X_read n 64) ) : SailM (BitVec 64) )
  let start_tag : (BitVec 4) := (AArch64_AllocationTagFromAddress operand1)
  let exclude ← (( do (pure (_get_GCR_EL1_Type_Exclude (← readReg GCR_EL1))) ) : SailM (BitVec 16) )
  let result ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let rtag ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let rtag ← (( do
    if ((← (AArch64_AllocationTagAccessIsEnabled (← readReg PSTATE).EL)) : Bool)
    then (pure (AArch64_ChooseNonExcludedTag start_tag tag_offset exclude))
    else (pure 0b0000#4) ) : SailM (BitVec 4) )
  let result : (BitVec 64) :=
    if (ADD : Bool)
    then
      (let (__tup_0, _) := (AddWithCarry operand1 offset 0#1)
      __tup_0)
    else
      (let (__tup_0, _) := (AddWithCarry operand1 (Complement.complement offset) 1#1)
      __tup_0)
  let result ← (( do (AArch64_AddressWithAllocationTag result rtag) ) : SailM (BitVec 64) )
  if ((d == 31) : Bool)
  then (SP_set result)
  else (X_set d 64 result)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddress (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then (SP_read ())
    else (X_read n 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do
    if ((m == 31) : Bool)
    then (SP_read ())
    else (X_read m 64) ) : SailM (BitVec 64) )
  let operand1 : (BitVec 64) := (sign_extend (Sail.BitVec.extractLsb operand1 55 0) 64)
  let operand2 : (BitVec 64) := (sign_extend (Sail.BitVec.extractLsb operand2 55 0) 64)
  let result ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let operand2 : (BitVec 64) := (Complement.complement operand2)
  let (nzcv, result) : ((BitVec 4) × (BitVec 64)) :=
    let (tup__0, tup__1) := ((AddWithCarry operand1 operand2 1#1) : ((BitVec 64) × (BitVec 4)))
    let result : (BitVec 64) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (nzcv, result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure ())
  (X_set d 64 result)

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then (SP_read ())
    else (X_read n 64) ) : SailM (BitVec 64) )
  let operand2 ← (( do
    if ((m == 31) : Bool)
    then (SP_read ())
    else (X_read m 64) ) : SailM (BitVec 64) )
  let operand1 : (BitVec 64) := (sign_extend (Sail.BitVec.extractLsb operand1 55 0) 64)
  let operand2 : (BitVec 64) := (sign_extend (Sail.BitVec.extractLsb operand2 55 0) 64)
  let result ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let operand2 : (BitVec 64) := (Complement.complement operand2)
  let (nzcv, result) : ((BitVec 4) × (BitVec 64)) :=
    let (tup__0, tup__1) := ((AddWithCarry operand1 operand2 1#1) : ((BitVec 64) × (BitVec 4)))
    let result : (BitVec 64) := tup__0
    let nzcv : (BitVec 4) := tup__1
    (nzcv, result)
  if (setflags : Bool)
  then
    (do
      writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure ())
  (X_set d 64 result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, i : Nat, m : Nat, n : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem i [0, 1, 2, 3] ∧ List.elem elements [2, 4] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp (d : Nat) (datasize : Nat) (elements : Nat) (i : Nat) (m : Nat) (n : Nat) (op1_unsigned : Bool) (op2_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let operand3 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let res ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        let res ← (( do
          let loop_b_lower := 0
          let loop_b_upper := 3
          let mut loop_vars_1 := res
          for b in [loop_b_lower:loop_b_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let element1 ← do (asl_Int (← (Elem_read operand1 ((4 *i e) +i b) 8)) op1_unsigned)
              let element2 ← do (asl_Int (← (Elem_read operand2 ((4 *i i) +i b) 8)) op2_unsigned)
              (pure (BitVec.addInt res (element1 *i element2)))
          (pure loop_vars_1) ) : SailM (BitVec 32) )
        (Elem_set result e 32 res)
    (pure loop_vars) ) : SailM (BitVec datasize) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [8, 16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let op1 ← (( do (undefined_int ()) ) : SailM Int )
  let op2 ← (( do (undefined_int ()) ) : SailM Int )
  let sat ← (( do (undefined_bool ()) ) : SailM Bool )
  let (op1, op2, result, sat) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (op1, op2, result, sat)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (op1, op2, result, sat) := loop_vars
      loop_vars ← do
        let op1 ← (asl_Int (← (Elem_read operand e esize)) (! is_unsigned))
        let op2 ← (asl_Int (← (Elem_read operand2 e esize)) is_unsigned)
        let (result, sat) ← (( do
          let (__tup_0, __tup_1) ← do (SatQ (op1 +i op2) esize is_unsigned)
          let result ← (Elem_set result e esize __tup_0)
          let sat : Bool := __tup_1
          (pure (result, sat)) ) : SailM ((BitVec datasize) × Bool) )
        if (sat : Bool)
        then writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 27 27 1#1)
        else (pure ())
        (pure (op1, op2, result, sat))
    (pure loop_vars) ) : SailM (Int × Int × (BitVec datasize) × Bool) )
  (V_set d datasize result)

def execute_aarch64_instrs_system_exceptions_runtime_svc (imm : (BitVec 16)) : SailM Unit := do
  (AArch64_CheckForSVCTrap imm)
  (AArch64_CallSupervisor imm)

/-- Type quantifiers: k_acquire : Bool, datasize : Nat, n : Nat, regsize : Nat, k_release : Bool, s : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ s ∧ s ≤ 31 ∧ List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_atomicops_swp (acquire : Bool) (datasize : Nat) (n : Nat) (regsize : Nat) (release : Bool) (s : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescAtomicOp MemAtomicOp_SWP acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let store_value ← (( do (X_read s datasize) ) : SailM (BitVec datasize) )
  let comparevalue ← (( do (__UNKNOWN_bits datasize) ) : SailM (BitVec datasize) )
  let data ← (( do (MemAtomic address comparevalue store_value accdesc) ) : SailM (BitVec datasize) )
  sail_assert (regsize ≥b datasize) "src/instrs64.sail:51787.44-51787.45"
  (X_set t regsize (Sail.BitVec.zeroExtend data regsize))
  if ((← readReg SPESampleInFlight) : Bool)
  then
    (do
      let ar : (BitVec 1) :=
        if ((acquire || release) : Bool)
        then 1#1
        else 0#1
      let excl : (BitVec 1) := 0#1
      let at' : (BitVec 1) := 1#1
      let is_load : Bool := true
      (SPESampleExtendedLoadStore ar excl at' is_load))
  else (pure ())

/-- Type quantifiers: k_acquire : Bool, n : Nat, k_release : Bool, t : Nat, t2 : Nat, k_tagchecked : Bool, 0 ≤ t2 ∧ t2 ≤ 31 ∧ 0 ≤ t ∧ t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_atomicops_swp_128 (acquire : Bool) (n : Nat) (release : Bool) (t : Nat) (t2 : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let value1_name ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let value2_name ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescAtomicOp MemAtomicOp_SWP acquire release tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else (do (X_read n 64)) ) : SailM (BitVec 64) )
  let store_value ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (value1_name +++ value2_name))
    else (pure (value2_name +++ value1_name)) ) : SailM (BitVec 128) )
  let comparevalue ← (( do (__UNKNOWN_bits 128) ) : SailM (BitVec 128) )
  let data ← (( do (MemAtomic address comparevalue store_value accdesc) ) : SailM (BitVec 128) )
  if ((← (BigEndian accdesc.acctype)) : Bool)
  then
    (do
      (X_set t 64 (Sail.BitVec.extractLsb data 127 64))
      (X_set t2 64 (Sail.BitVec.extractLsb data 63 0)))
  else
    (do
      (X_set t 64 (Sail.BitVec.extractLsb data 63 0))
      (X_set t2 64 (Sail.BitVec.extractLsb data 127 64)))

/-- Type quantifiers: k_has_result : Bool, sys_crm : Nat, sys_crn : Nat, sys_op0 : Nat, sys_op1 : Nat, sys_op2 : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ List.elem sys_op2 [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem sys_op1 [0, 1, 2, 3, 4, 5, 6, 7] ∧ sys_op0 = 1 ∧ 0 ≤ sys_crn ∧ sys_crn ≤ 15 ∧ 0 ≤ sys_crm ∧ sys_crm ≤ 15 -/
def execute_aarch64_instrs_system_sysops (has_result : Bool) (sys_crm : Nat) (sys_crn : Nat) (sys_op0 : Nat) (sys_op1 : Nat) (sys_op2 : Nat) (t : Nat) : SailM Unit := do
  if (has_result : Bool)
  then (AArch64_SysInstrWithResult sys_op0 sys_op1 sys_crn sys_crm sys_op2 t)
  else (AArch64_SysInstr sys_op0 sys_op1 sys_crn sys_crm sys_op2 t)

/-- Type quantifiers: sys_crm : Nat, sys_crn : Nat, sys_op0 : Nat, sys_op1 : Nat, sys_op2 : Nat, t : Nat, t2 : Nat, 1 ≤ t2 ∧ t2 ≤ 32 ∧ 0 ≤ t ∧ t ≤ 31 ∧ List.elem sys_op2 [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem sys_op1 [0, 1, 2, 3, 4, 5, 6, 7] ∧ sys_op0 = 1 ∧ 0 ≤ sys_crn ∧ sys_crn ≤ 15 ∧ 0 ≤ sys_crm ∧ sys_crm ≤ 15 -/
def execute_aarch64_instrs_system_sysops_128 (sys_crm : Nat) (sys_crn : Nat) (sys_op0 : Nat) (sys_op1 : Nat) (sys_op2 : Nat) (t : Nat) (t2 : Nat) : SailM Unit := do
  (AArch64_SysInstr128 sys_op0 sys_op1 sys_crn sys_crm sys_op2 t t2)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, k_is_tbl : Bool, m : Nat, n__arg : Nat, regs : Nat, List.elem regs [1, 2, 3, 4] ∧ 0 ≤ n__arg ∧ n__arg ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem elements [8, 16] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_vector_table (d : Nat) (datasize : Nat) (elements : Nat) (is_tbl : Bool) (m : Nat) (n__arg : Nat) (regs : Nat) : SailM Unit := do
  let n : Int := n__arg
  (CheckFPAdvSIMDEnabled64 ())
  let indices ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let table : (BitVec (128 * regs)) := (Zeros (n := (128 *i regs)))
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (n, table) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (regs -i 1)
    let mut loop_vars := (n, table)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (n, table) := loop_vars
      loop_vars ← do
        let table ← (pure (Sail.BitVec.updateSubrange table ((128 *i i) +i 127) (128 *i i) (← (V_read n 128))))
        let n : Int := (fmod_int (n +i 1) 32)
        (pure (n, table))
    (pure loop_vars) ) : SailM (Int × (BitVec (128 * regs))) )
  let result ← (( do
    if (is_tbl : Bool)
    then (pure (Zeros (n := datasize)))
    else (V_read d datasize) ) : SailM (BitVec datasize) )
  let (index, result) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (elements -i 1)
    let mut loop_vars_1 := (index, result)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (index, result) := loop_vars_1
      loop_vars_1 ← do
        let index ← (pure (BitVec.toNat (← (Elem_read indices i 8))))
        let index := index
        let result ← (( do
          if ((index <b (16 *i regs)) : Bool)
          then (do (Elem_set result i 8 (← (Elem_read table index 8))))
          else (pure result) ) : SailM (BitVec datasize) )
        (pure (index, result))
    (pure loop_vars_1) ) : SailM (Int × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: bit_pos : Nat, datasize : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ bit_pos ∧ bit_pos ≤ 63 -/
def execute_aarch64_instrs_branch_conditional_test (bit_pos : Nat) (bit_val : (BitVec 1)) (datasize : Nat) (offset : (BitVec 64)) (t : Nat) : SailM Unit := do
  let operand ← (( do (X_read t datasize) ) : SailM (BitVec datasize) )
  let branch_conditional : Bool := true
  sail_assert (bit_pos <b datasize) "src/instrs64.sail:52130.43-52130.44"
  if (((BitVec.join1 [(BitVec.access operand bit_pos)]) == bit_val) : Bool)
  then (BranchTo ((← (PC_read ())) + offset) BranchType_DIR branch_conditional)
  else (BranchNotTaken BranchType_DIR branch_conditional)

/-- Type quantifiers: k_retry : Bool -/
def execute_aarch64_instrs_system_tme_tcancel (reason : (BitVec 15)) (retry : Bool) : SailM Unit := do
  if ((! (← (IsTMEEnabled ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((← readReg TSTATE).depth >b 0) : Bool)
  then (FailTransaction__1 TMFailure_CNCL retry false reason)
  else (pure ())

def execute_aarch64_instrs_system_tme_tcommit (_ : Unit) : SailM Unit := do
  if ((! (← (IsTMEEnabled ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((← readReg TSTATE).depth == 0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((← readReg TSTATE).depth == 1) : Bool)
  then
    (let _ : Unit := (CommitTransactionalWrites ())
    (pure (ClearExclusiveLocal (ProcessorID ()))))
  else (pure ())
  writeReg TSTATE { (← readReg TSTATE) with depth := ← (do (pure ((← readReg TSTATE).depth -i 1))) }

/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, m : Nat, n : Nat, pairs : Int, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_vector_permute_transpose (d : Nat) (datasize : Nat) (esize : Nat) (m : Nat) (n : Nat) (pairs : Int) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_p_lower := 0
    let loop_p_upper := (pairs -i 1)
    let mut loop_vars := result
    for p in [loop_p_lower:loop_p_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let result ← (Elem_set result ((2 *i p) +i 0) esize (← (Elem_read operand1 ((2 *i p) +i part) esize)))
        (Elem_set result ((2 *i p) +i 1) esize (← (Elem_read operand2 ((2 *i p) +i part) esize)))
    (pure loop_vars) ) : SailM (BitVec datasize) )
  (V_set d datasize result)

/-- Type quantifiers: VL : Nat, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ (is_VL VL) -/
def execute_aarch64_instrs_system_tme_tstart (VL : Nat) (t : Nat) : SailM Unit := do
  if ((! (← (IsTMEEnabled ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let IsEL1Regime ← (( do (undefined_bool ()) ) : SailM Bool )
  let tme ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let tmt ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (tme, tmt) ← (( do
    let questionMark ← do (pure (← readReg PSTATE).EL)
    let (tme, tmt) ← (( do
      if ((questionMark == EL0) : Bool)
      then
        (do
          let IsEL1Regime ← (( do (pure ((← (S1TranslationRegime__1 ())) == EL1)) ) : SailM Bool )
          let (tme, tmt) ← (( do
            if (IsEL1Regime : Bool)
            then
              (do
                let tme ← (pure (_get_SCTLR_EL1_Type_TME0 (← readReg SCTLR_EL1)))
                let tmt ← (pure (_get_SCTLR_EL1_Type_TMT0 (← readReg SCTLR_EL1)))
                (pure (tme, tmt)))
            else
              (do
                let tme ← (pure (_get_SCTLR_EL2_Type_TME0 (← readReg SCTLR_EL2)))
                let tmt ← (pure (_get_SCTLR_EL2_Type_TMT0 (← readReg SCTLR_EL2)))
                (pure (tme, tmt))) ) : SailM ((BitVec 1) × (BitVec 1)) )
          (pure (tme, tmt)))
      else
        (do
          let (tme, tmt) ← (( do
            if ((questionMark == EL1) : Bool)
            then
              (do
                let tme ← (pure (_get_SCTLR_EL1_Type_TME (← readReg SCTLR_EL1)))
                let tmt ← (pure (_get_SCTLR_EL1_Type_TMT (← readReg SCTLR_EL1)))
                (pure (tme, tmt)))
            else
              (do
                let (tme, tmt) ← (( do
                  if ((questionMark == EL2) : Bool)
                  then
                    (do
                      let tme ← (pure (_get_SCTLR_EL2_Type_TME (← readReg SCTLR_EL2)))
                      let tmt ← (pure (_get_SCTLR_EL2_Type_TMT (← readReg SCTLR_EL2)))
                      (pure (tme, tmt)))
                  else
                    (do
                      let (tme, tmt) ← (( do
                        if ((questionMark == EL3) : Bool)
                        then
                          (do
                            let tme ← (pure (_get_SCTLR_EL3_Type_TME (← readReg SCTLR_EL3)))
                            let tmt ← (pure (_get_SCTLR_EL3_Type_TMT (← readReg SCTLR_EL3)))
                            (pure (tme, tmt)))
                        else
                          (do
                            (Unreachable ())
                            (pure (tme, tmt))) ) : SailM ((BitVec 1) × (BitVec 1)) )
                      (pure (tme, tmt))) ) : SailM ((BitVec 1) × (BitVec 1)) )
                (pure (tme, tmt))) ) : SailM ((BitVec 1) × (BitVec 1)) )
          (pure (tme, tmt))) ) : SailM ((BitVec 1) × (BitVec 1)) )
    (pure (tme, tmt)) ) : SailM ((BitVec 1) × (BitVec 1)) )
  let enable : Bool := (tme == 1#1)
  let trivial : Bool := (tmt == 1#1)
  if ((! enable) : Bool)
  then (TransactionStartTrap t)
  else
    (do
      if (trivial : Bool)
      then
        (do
          writeReg TSTATE { (← readReg TSTATE) with nPC := ← (do (NextInstrAddr 64)) }
          writeReg TSTATE { (← readReg TSTATE) with Rt := t }
          (FailTransaction TMFailure_TRIVIAL false))
      else
        (do
          if ((←((HaveSME ()) <&&> (do
               (pure ((← readReg PSTATE).SM == 1#1))))) : Bool)
          then (FailTransaction TMFailure_ERR false)
          else
            (do
              if (((← readReg TSTATE).depth == 255) : Bool)
              then (FailTransaction TMFailure_NEST false)
              else
                (do
                  if (((← readReg TSTATE).depth == 0) : Bool)
                  then
                    (do
                      writeReg TSTATE { (← readReg TSTATE) with nPC := ← (do (NextInstrAddr 64)) }
                      writeReg TSTATE { (← readReg TSTATE) with Rt := t }
                      let _ : Unit := (ClearExclusiveLocal (ProcessorID ()))
                      (TakeTransactionCheckpoint VL (Int.ediv VL 8))
                      (pure (StartTrackingTransactionalReadsWrites ())))
                  else (pure ())))))
  writeReg TSTATE { (← readReg TSTATE) with depth := ← (do (pure ((← readReg TSTATE).depth +i 1))) }
  (X_set t 64 (Zeros (n := 64)))

/-- Type quantifiers: t : Nat, 0 ≤ t ∧ t ≤ 31 -/
def execute_aarch64_instrs_system_tme_ttest (t : Nat) : SailM Unit := do
  if ((! (← (IsTMEEnabled ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (X_set t 64 (integer_subrange (← readReg TSTATE).depth 63 0))

def execute_aarch64_instrs_udf (_ : Unit) : Unit :=
  ()

def decode_udf_perm_undef_aarch64_instrs_udf (imm16 : (BitVec 16)) : SailM Unit := do
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: d : Nat, datasize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ imm ∧ imm ≤ 255 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_max_min_umax_imm (d : Nat) (datasize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let result := (Max.max (BitVec.toNat operand1) imm)
  (X_set d datasize (integer_subrange result (datasize -i 1) 0))

/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_max_min_umax_reg (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (X_read m datasize) ) : SailM (BitVec datasize) )
  let result := (Max.max (BitVec.toNat operand1) (BitVec.toNat operand2))
  (X_set d datasize (integer_subrange result (datasize -i 1) 0))

/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_max_min_umin_reg (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (X_read m datasize) ) : SailM (BitVec datasize) )
  let result := (Min.min (BitVec.toNat operand1) (BitVec.toNat operand2))
  (X_set d datasize (integer_subrange result (datasize -i 1) 0))

/-- Type quantifiers: d : Nat, datasize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ imm ∧ imm ≤ 255 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_max_min_umin_imm (d : Nat) (datasize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let result := (Min.min (BitVec.toNat operand1) imm)
  (X_set d datasize (integer_subrange result (datasize -i 1) 0))

/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, idxdsize : Nat, index : Int, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem idxdsize [64, 128] ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_integer_move_unsigned (d : Nat) (datasize : Nat) (esize : Nat) (idxdsize : Nat) (index : Int) (n : Nat) : SailM Unit := do
  if ((index == 0) : Bool)
  then (CheckFPEnabled64 ())
  else (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n idxdsize) ) : SailM (BitVec idxdsize) )
  sail_assert (datasize ≥b esize) "src/instrs64.sail:52593.42-52593.43"
  (X_set d datasize (Sail.BitVec.zeroExtend (← (Elem_read operand index esize)) datasize))

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_special_recip_int (d : Nat) (datasize : Nat) (elements : Int) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e 32)
        let result ← (Elem_set result e 32 (← (UnsignedRecipEstimate element)))
        (pure (element, result))
    (pure loop_vars) ) : SailM ((BitVec 32) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int (d : Nat) (datasize : Nat) (elements : Int) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e 32)
        let result ← (Elem_set result e 32 (← (UnsignedRSqrtEstimate element)))
        (pure (element, result))
    (pure loop_vars) ) : SailM ((BitVec 32) × (BitVec datasize)) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem elements [2, 4] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_usdot (d : Nat) (datasize : Nat) (elements : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let operand3 ← (( do (V_read d datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do
        let res ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
        let res ← (( do
          let loop_b_lower := 0
          let loop_b_upper := 3
          let mut loop_vars_1 := res
          for b in [loop_b_lower:loop_b_upper:1]i do
            let res := loop_vars_1
            loop_vars_1 ← do
              let element1 ← do (pure (BitVec.toNat (← (Elem_read operand1 ((4 *i e) +i b) 8))))
              let element2 ← do (pure (BitVec.toInt (← (Elem_read operand2 ((4 *i e) +i b) 8))))
              (pure (BitVec.addInt res (element1 *i element2)))
          (pure loop_vars_1) ) : SailM (BitVec 32) )
        (Elem_set result e 32 res)
    (pure loop_vars) ) : SailM (BitVec datasize) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, m : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_vector_permute_unzip (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operandl ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operandh ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let zipped : (BitVec (datasize * 2)) := (operandh +++ operandl)
  let result ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := result
    for e in [loop_e_lower:loop_e_upper:1]i do
      let result := loop_vars
      loop_vars ← do (Elem_set result e esize (← (Elem_read zipped ((2 *i e) +i part) esize)))
    (pure loop_vars) ) : SailM (BitVec datasize) )
  (V_set d datasize result)

/-- Type quantifiers: d : Nat, 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_system_sysinstwithreg_wfet (d : Nat) : SailM Unit := do
  let localtimeout ← do (pure (BitVec.toNat (← (X_read d 64))))
  if ((←((Halted ()) <&&> (do
       (ConstrainUnpredictableBool Unpredictable_WFxTDEBUG)))) : Bool)
  then (EndOfInstruction ())
  else (pure ())
  (Hint_WFE localtimeout WFxType_WFET)

/-- Type quantifiers: d : Nat, 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_system_sysinstwithreg_wfit (d : Nat) : SailM Unit := do
  let localtimeout ← do (pure (BitVec.toNat (← (X_read d 64))))
  if ((←((Halted ()) <&&> (do
       (ConstrainUnpredictableBool Unpredictable_WFxTDEBUG)))) : Bool)
  then (EndOfInstruction ())
  else (pure ())
  (Hint_WFI localtimeout WFxType_WFIT)

def execute_aarch64_instrs_integer_flags_xaflag (_ : Unit) : SailM Unit := do
  let n ← (( do (pure ((Complement.complement (← readReg PSTATE).C) &&& (Complement.complement (← readReg PSTATE).Z))) ) : SailM (BitVec 1) )
  let z ← (( do (pure ((← readReg PSTATE).Z &&& (← readReg PSTATE).C)) ) : SailM (BitVec 1) )
  let c ← (( do (pure ((← readReg PSTATE).C ||| (← readReg PSTATE).Z)) ) : SailM (BitVec 1) )
  let v ← (( do (pure ((Complement.complement (← readReg PSTATE).C) &&& (← readReg PSTATE).Z)) ) : SailM (BitVec 1) )
  writeReg PSTATE { (← readReg PSTATE) with N := n }
  writeReg PSTATE { (← readReg PSTATE) with Z := z }
  writeReg PSTATE { (← readReg PSTATE) with C := c }
  writeReg PSTATE { (← readReg PSTATE) with V := v }

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_crypto_sha3_xar (d : Nat) (imm6 : (BitVec 6)) (m : Nat) (n : Nat) : SailM Unit := do
  (AArch64_CheckFPAdvSIMDEnabled ())
  let Vm ← (( do (V_read m 128) ) : SailM (BitVec 128) )
  let Vn ← (( do (V_read n 128) ) : SailM (BitVec 128) )
  let tmp : (BitVec 128) := (Vn ^^^ Vm)
  (V_set d 128 ((ROR (Sail.BitVec.extractLsb tmp 127 64) (BitVec.toNat imm6)) +++ (ROR (Sail.BitVec.extractLsb tmp 63 0) (BitVec.toNat imm6))))

/-- Type quantifiers: d : Nat, k_data : Bool, 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_strip_dp_1src (d : Nat) (data : Bool) : SailM Unit := do
  if ((← (HavePACExt ())) : Bool)
  then (X_set d 64 (← (Strip (← (X_read d 64)) data)))
  else (pure ())

/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_extract_nosat (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do (V_read n (2 *i datasize)) ) : SailM (BitVec (2 * datasize)) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let element ← (( do (undefined_bitvector (2 *i esize)) ) : SailM (BitVec (2 * esize)) )
  let (element, result) ← (( do
    let loop_e_lower := 0
    let loop_e_upper := (elements -i 1)
    let mut loop_vars := (element, result)
    for e in [loop_e_lower:loop_e_upper:1]i do
      let (element, result) := loop_vars
      loop_vars ← do
        let element ← (Elem_read operand e (2 *i esize))
        let result ← (Elem_set result e esize (Sail.BitVec.extractLsb element (esize -i 1) 0))
        (pure (element, result))
    (pure loop_vars) ) : SailM ((BitVec (2 * esize)) × (BitVec datasize)) )
  (Vpart_set d part datasize result)

/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, m : Nat, n : Nat, pairs : Int, part : Nat, List.elem part [0, 1] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_vector_permute_zip (d : Nat) (datasize : Nat) (esize : Nat) (m : Nat) (n : Nat) (pairs : Int) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do (V_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (V_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
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
    (pure loop_vars) ) : SailM (BitVec datasize) )
  (V_set d datasize result)

def decode_abs_aarch64_instrs_integer_arithmetic_unary_abs (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveCSSC ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let d := (BitVec.toNat Rd)
  (execute_aarch64_instrs_integer_arithmetic_unary_abs d datasize n)

def decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd d datasize elements esize n neg)

def decode_abs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b110#3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd d datasize elements esize n neg)

def decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd d datasize elements esize n neg)

def decode_neg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b110#3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_int_sisd d datasize elements esize n neg)

def decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_add_sub_carry d datasize m n setflags sub_op)

def decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_add_sub_carry d datasize m n setflags sub_op)

def decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_add_sub_carry d datasize m n setflags sub_op)

def decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_add_sub_carry d datasize m n setflags sub_op)

def decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let sub_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd d datasize elements esize m n sub_op)

def decode_add_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd d datasize elements esize m n sub_op)

def decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let sub_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd d datasize elements esize m n sub_op)

def decode_sub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_single_sisd d datasize elements esize m n sub_op)

def decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift := (BitVec.toNat imm3)
  if ((shift >b 4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg d datasize extend_type m n setflags shift sub_op)

def decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift := (BitVec.toNat imm3)
  if ((shift >b 4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg d datasize extend_type m n setflags shift sub_op)

def decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift := (BitVec.toNat imm3)
  if ((shift >b 4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg d datasize extend_type m n setflags shift sub_op)

def decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift := (BitVec.toNat imm3)
  if ((shift >b 4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg d datasize extend_type m n setflags shift sub_op)

def decode_addg_aarch64_instrs_integer_tags_mcaddtag (Xd : (BitVec 5)) (Xn : (BitVec 5)) (uimm4 : (BitVec 4)) (op3 : (BitVec 2)) (uimm6 : (BitVec 6)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Xd)
  let n := (BitVec.toNat Xn)
  let tag_offset : (BitVec 4) := uimm4
  let offset : (BitVec 64) := ((Sail.BitVec.zeroExtend uimm6 64) <<< LOG2_TAG_GRANULE)
  let ADD : Bool := true
  (execute_aarch64_instrs_integer_tags_mcaddtag ADD d n offset tag_offset)

def decode_addhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (o1 == 1#1)
  let round : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow d datasize elements esize m n part round sub_op)

def decode_raddhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (o1 == 1#1)
  let round : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow d datasize elements esize m n part round sub_op)

def decode_rsubhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (o1 == 1#1)
  let round : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow d datasize elements esize m n part round sub_op)

def decode_subhn_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (o1 == 1#1)
  let round : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_narrow d datasize elements esize m n part round sub_op)

def decode_addp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size +++ Q) == 0b110#3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_wrapping_pair d datasize elements esize m n)

def decode_addp_advsimd_pair_aarch64_instrs_vector_reduce_add_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := (esize *i 2)
  let elements := 2
  let op : ReduceOp := ReduceOp_ADD
  (execute_aarch64_instrs_vector_reduce_add_sisd d datasize esize n op)

def decode_addv_advsimd_aarch64_instrs_vector_reduce_add_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b100#3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let op : ReduceOp := ReduceOp_ADD
  (execute_aarch64_instrs_vector_reduce_add_simd d datasize esize n op)

def decode_adr_aarch64_instrs_integer_arithmetic_address_pc_rel (Rd : (BitVec 5)) (immhi : (BitVec 19)) (immlo : (BitVec 2)) (op : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let page : Bool := (op == 1#1)
  let imm ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let imm : (BitVec 64) :=
    if (page : Bool)
    then (sign_extend ((immhi +++ immlo) +++ (Zeros (n := 12))) 64)
    else (sign_extend (immhi +++ immlo) 64)
  (execute_aarch64_instrs_integer_arithmetic_address_pc_rel d imm page)

def decode_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel (Rd : (BitVec 5)) (immhi : (BitVec 19)) (immlo : (BitVec 2)) (op : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let page : Bool := (op == 1#1)
  let imm ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let imm : (BitVec 64) :=
    if (page : Bool)
    then (sign_extend ((immhi +++ immlo) +++ (Zeros (n := 12))) 64)
    else (sign_extend (immhi +++ immlo) 64)
  (execute_aarch64_instrs_integer_arithmetic_address_pc_rel d imm page)

def decode_aesd_advsimd_aarch64_instrs_vector_crypto_aes_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((! (← (HaveAESExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let decrypt : Bool := (D == 1#1)
  (execute_aarch64_instrs_vector_crypto_aes_round d decrypt n)

def decode_aese_advsimd_aarch64_instrs_vector_crypto_aes_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((! (← (HaveAESExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let decrypt : Bool := (D == 1#1)
  (execute_aarch64_instrs_vector_crypto_aes_round d decrypt n)

def decode_aesimc_advsimd_aarch64_instrs_vector_crypto_aes_mix (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((! (← (HaveAESExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let decrypt : Bool := (D == 1#1)
  (execute_aarch64_instrs_vector_crypto_aes_mix d decrypt n)

def decode_aesmc_advsimd_aarch64_instrs_vector_crypto_aes_mix (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((! (← (HaveAESExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let decrypt : Bool := (D == 1#1)
  (execute_aarch64_instrs_vector_crypto_aes_mix d decrypt n)

def decode_and_log_imm_aarch64_instrs_integer_logical_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match (opc : BitVec 2) with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  let imm ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  if (((sf == 0#1) && (N != 0#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let imm ← (( do
    let (__tup_0, _) ← do (DecodeBitMasks N imms immr true datasize)
    (pure __tup_0) ) : SailM (BitVec datasize) )
  (execute_aarch64_instrs_integer_logical_immediate d datasize imm n op setflags)

def decode_ands_log_imm_aarch64_instrs_integer_logical_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match (opc : BitVec 2) with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  let imm ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  if (((sf == 0#1) && (N != 0#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let imm ← (( do
    let (__tup_0, _) ← do (DecodeBitMasks N imms immr true datasize)
    (pure __tup_0) ) : SailM (BitVec datasize) )
  (execute_aarch64_instrs_integer_logical_immediate d datasize imm n op setflags)

def decode_eor_log_imm_aarch64_instrs_integer_logical_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match (opc : BitVec 2) with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  let imm ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  if (((sf == 0#1) && (N != 0#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let imm ← (( do
    let (__tup_0, _) ← do (DecodeBitMasks N imms immr true datasize)
    (pure __tup_0) ) : SailM (BitVec datasize) )
  (execute_aarch64_instrs_integer_logical_immediate d datasize imm n op setflags)

def decode_orr_log_imm_aarch64_instrs_integer_logical_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match (opc : BitVec 2) with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  let imm ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  if (((sf == 0#1) && (N != 0#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let imm ← (( do
    let (__tup_0, _) ← do (DecodeBitMasks N imms immr true datasize)
    (pure __tup_0) ) : SailM (BitVec datasize) )
  (execute_aarch64_instrs_integer_logical_immediate d datasize imm n op setflags)

def decode_and_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 8
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let invert : Bool := ((BitVec.join1 [(BitVec.access size 0)]) == 1#1)
  let op : LogicalOp :=
    if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
    then LogicalOp_ORR
    else LogicalOp_AND
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr d datasize invert m n op)

def decode_bic_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 8
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let invert : Bool := ((BitVec.join1 [(BitVec.access size 0)]) == 1#1)
  let op : LogicalOp :=
    if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
    then LogicalOp_ORR
    else LogicalOp_AND
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr d datasize invert m n op)

def decode_orn_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 8
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let invert : Bool := ((BitVec.join1 [(BitVec.access size 0)]) == 1#1)
  let op : LogicalOp :=
    if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
    then LogicalOp_ORR
    else LogicalOp_AND
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr d datasize invert m n op)

def decode_orr_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 8
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let invert : Bool := ((BitVec.join1 [(BitVec.access size 0)]) == 1#1)
  let op : LogicalOp :=
    if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
    then LogicalOp_ORR
    else LogicalOp_AND
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_and_orr d datasize invert m n op)

def decode_autda_aarch64_instrs_integer_pac_autda_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((! (← (HavePACExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let source_is_sp ← (( do
    if ((Z == 0#1) : Bool)
    then
      (if ((n == 31) : Bool)
      then (pure true)
      else (pure source_is_sp))
    else
      (do
        if ((n != 31) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure source_is_sp)) ) : SailM Bool )
  (execute_aarch64_instrs_integer_pac_autda_dp_1src d n source_is_sp)

def decode_autdb_aarch64_instrs_integer_pac_autdb_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((! (← (HavePACExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let source_is_sp ← (( do
    if ((Z == 0#1) : Bool)
    then
      (if ((n == 31) : Bool)
      then (pure true)
      else (pure source_is_sp))
    else
      (do
        if ((n != 31) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure source_is_sp)) ) : SailM Bool )
  (execute_aarch64_instrs_integer_pac_autdb_dp_1src d n source_is_sp)

def decode_autia_aarch64_instrs_integer_pac_autia_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((! (← (HavePACExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let source_is_sp ← (( do
    if ((Z == 0#1) : Bool)
    then
      (if ((n == 31) : Bool)
      then (pure true)
      else (pure source_is_sp))
    else
      (do
        if ((n != 31) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure source_is_sp)) ) : SailM Bool )
  (execute_aarch64_instrs_integer_pac_autia_dp_1src d n source_is_sp)

def decode_autia_aarch64_instrs_integer_pac_autia_hint (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let d : Nat := 17
  let n ← (( do (undefined_int ()) ) : SailM Int )
  let source_is_sp : Bool := false
  let (d, n, source_is_sp) ← (( do
    let b__0 := (CRm +++ op2)
    let (d, n, source_is_sp) ← (( do
      if ((b__0 == (0b0011100#7 : (BitVec 7))) : Bool)
      then
        (let d : Nat := 30
        let n : Int := 31
        (pure (d, n, source_is_sp)))
      else
        (do
          let (d, n, source_is_sp) ← (( do
            if ((b__0 == (0b0011101#7 : (BitVec 7))) : Bool)
            then
              (let d : Nat := 30
              let source_is_sp : Bool := true
              (pure (d, n, source_is_sp)))
            else
              (do
                let (d, n) ← (( do
                  if ((b__0 == (0b0001100#7 : (BitVec 7))) : Bool)
                  then
                    (let d : Nat := 17
                    let n : Int := 16
                    (pure (d, n)))
                  else
                    (do
                      if ((b__0 == (0b0001000#7 : (BitVec 7))) : Bool)
                      then (sailThrow ((Error_See "PACIA")) : SailM Unit)
                      else
                        (do
                          if ((b__0 == (0b0001010#7 : (BitVec 7))) : Bool)
                          then (sailThrow ((Error_See "PACIB")) : SailM Unit)
                          else
                            (do
                              if ((b__0 == (0b0001110#7 : (BitVec 7))) : Bool)
                              then (sailThrow ((Error_See "AUTIB")) : SailM Unit)
                              else
                                (do
                                  if (((Sail.BitVec.extractLsb b__0 6 1) == (0b001100#6 : (BitVec 6))) : Bool)
                                  then (sailThrow ((Error_See "PACIA")) : SailM Unit)
                                  else
                                    (do
                                      if (((Sail.BitVec.extractLsb b__0 6 1) == (0b001101#6 : (BitVec 6))) : Bool)
                                      then (sailThrow ((Error_See "PACIB")) : SailM Unit)
                                      else
                                        (do
                                          if (((Sail.BitVec.extractLsb b__0 6 1) == (0b001111#6 : (BitVec 6))) : Bool)
                                          then (sailThrow ((Error_See "AUTIB")) : SailM Unit)
                                          else
                                            (do
                                              if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                              then (sailThrow ((Error_See "XPACLRI")) : SailM Unit)
                                              else (sailThrow ((Error_See "HINT")) : SailM Unit)))))))
                      (pure (d, n))) ) : SailM (Int × Int) )
                (pure (d, n, source_is_sp))) ) : SailM (Int × Int × Bool) )
          (pure (d, n, source_is_sp))) ) : SailM (Int × Int × Bool) )
    (pure (d, n, source_is_sp)) ) : SailM (Int × Int × Bool) )
  let n := n
  let d := d
  sail_assert ((0 ≤b n) && (n ≤b 31)) "src/instrs64.sail:2471.43-2471.44"
  (execute_aarch64_instrs_integer_pac_autia_dp_1src d n source_is_sp)

def decode_autib_aarch64_instrs_integer_pac_autib_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((! (← (HavePACExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let source_is_sp ← (( do
    if ((Z == 0#1) : Bool)
    then
      (if ((n == 31) : Bool)
      then (pure true)
      else (pure source_is_sp))
    else
      (do
        if ((n != 31) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure source_is_sp)) ) : SailM Bool )
  (execute_aarch64_instrs_integer_pac_autib_dp_1src d n source_is_sp)


