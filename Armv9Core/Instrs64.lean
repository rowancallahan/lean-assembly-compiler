import Armv9.Armv9
import Armv9.Flow
import Armv9.Arith
import Armv9.Vector
import Armv9.ReverseEndianness
import Armv9.Prelude
import Armv9.Builtins
import Armv9.Impdefs
import Armv9Core.Interrupts
import Armv9Core.V8Base

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

/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_amount : Nat, k_sub_op : Bool, 0 ≤ shift_amount ∧ shift_amount ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_amount : Nat) (shift_type : ShiftType) (sub_op : Bool) : SailM Unit := do
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (ShiftReg m shift_type shift_amount datasize) ) : SailM (BitVec datasize) )
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
  (X_set d datasize result)

def decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
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

def decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
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

def decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
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

/-- Type quantifiers: d : Nat, datasize : Nat, n : Nat, k_setflags : Bool, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_add_sub_immediate (d : Nat) (datasize : Nat) (imm : (BitVec datasize)) (n : Nat) (setflags : Bool) (sub_op : Bool) : SailM Unit := do
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then (pure (Sail.BitVec.extractLsb (← (SP_read ())) (datasize -i 1) 0))
    else (X_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 : (BitVec datasize) := imm
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

def decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (sh : (BitVec 1)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
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

def decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (sh : (BitVec 1)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
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

def decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (sh : (BitVec 1)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
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

/-- Type quantifiers: d : Nat, datasize : Nat, k_invert : Bool, m : Nat, n : Nat, k_setflags : Bool, shift_amount : Nat, 0 ≤ shift_amount ∧ shift_amount ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_logical_shiftedreg (d : Nat) (datasize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : LogicalOp) (setflags : Bool) (shift_amount : Nat) (shift_type : ShiftType) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (ShiftReg m shift_type shift_amount datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let operand2 : (BitVec datasize) :=
    if (invert : Bool)
    then (Complement.complement operand2)
    else operand2
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
  (X_set d datasize result)

def decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
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

def decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
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

def decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
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

/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_shift_variable (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) (shift_type : ShiftType) : SailM Unit := do
  let operand2 ← (( do (X_read m datasize) ) : SailM (BitVec datasize) )
  let result ← (( do (ShiftReg n shift_type (Nat.mod (BitVec.toNat operand2) datasize) datasize) ) : SailM (BitVec datasize) )
  (X_set d datasize result)

def decode_asrv_aarch64_instrs_integer_shift_variable (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let shift_type ← (( do (DecodeShift op2) ) : SailM ShiftType )
  (execute_aarch64_instrs_integer_shift_variable d datasize m n shift_type)

def decode_lslv_aarch64_instrs_integer_shift_variable (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let shift_type ← (( do (DecodeShift op2) ) : SailM ShiftType )
  (execute_aarch64_instrs_integer_shift_variable d datasize m n shift_type)

def decode_lsrv_aarch64_instrs_integer_shift_variable (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let shift_type ← (( do (DecodeShift op2) ) : SailM ShiftType )
  (execute_aarch64_instrs_integer_shift_variable d datasize m n shift_type)

def execute_aarch64_instrs_branch_unconditional_immediate (branch_type : BranchType) (offset : (BitVec 64)) : SailM Unit := do
  if ((BEq.beq branch_type BranchType_DIRCALL) : Bool)
  then
    (do
      if ((←((HaveGCS ()) <&&> (do
           (GCSPCREnabled (← readReg PSTATE).EL)))) : Bool)
      then (AddGCSRecord (BitVec.addInt (← (PC_read ())) 4))
      else (pure ())
      (X_set 30 64 (BitVec.addInt (← (PC_read ())) 4)))
  else (pure ())
  let branch_conditional : Bool := false
  (BranchTo ((← (PC_read ())) + offset) branch_type branch_conditional)

def decode_b_uncond_aarch64_instrs_branch_unconditional_immediate (imm26 : (BitVec 26)) (op : (BitVec 1)) : SailM Unit := do
  let branch_type : BranchType :=
    if ((op == 1#1) : Bool)
    then BranchType_DIRCALL
    else BranchType_DIR
  let offset : (BitVec 64) := (sign_extend (imm26 +++ 0b00#2) 64)
  (execute_aarch64_instrs_branch_unconditional_immediate branch_type offset)

def decode_bl_aarch64_instrs_branch_unconditional_immediate (imm26 : (BitVec 26)) (op : (BitVec 1)) : SailM Unit := do
  let branch_type : BranchType :=
    if ((op == 1#1) : Bool)
    then BranchType_DIRCALL
    else BranchType_DIR
  let offset : (BitVec 64) := (sign_extend (imm26 +++ 0b00#2) 64)
  (execute_aarch64_instrs_branch_unconditional_immediate branch_type offset)

def execute_aarch64_instrs_branch_conditional_cond (condition : (BitVec 4)) (offset : (BitVec 64)) : SailM Unit := do
  let branch_conditional : Bool := true
  if ((← (ConditionHolds condition)) : Bool)
  then (BranchTo ((← (PC_read ())) + offset) BranchType_DIR branch_conditional)
  else (BranchNotTaken BranchType_DIR branch_conditional)

def decode_b_cond_aarch64_instrs_branch_conditional_cond (cond : (BitVec 4)) (imm19 : (BitVec 19)) : SailM Unit := do
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  let condition : (BitVec 4) := cond
  (execute_aarch64_instrs_branch_conditional_cond condition offset)

/-- Type quantifiers: m : Nat, n : Nat, k_pac : Bool, k_source_is_sp : Bool, k_use_key_a : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 -/
def execute_aarch64_instrs_branch_unconditional_register (branch_type : BranchType) (m : Nat) (n : Nat) (pac : Bool) (source_is_sp : Bool) (use_key_a : Bool) : SailM Unit := do
  let inst_type ← (( do (undefined_GCSInstruction ()) ) : SailM GCSInstruction )
  let target ← (( do (X_read n 64) ) : SailM (BitVec 64) )
  let auth_then_branch : Bool := true
  let target ← (( do
    if (pac : Bool)
    then
      (do
        let modifier ← (( do
          if (source_is_sp : Bool)
          then (SP_read ())
          else (X_read m 64) ) : SailM (BitVec 64) )
        if (use_key_a : Bool)
        then (do (AuthIA target modifier auth_then_branch))
        else (do (AuthIB target modifier auth_then_branch)))
    else (pure target) ) : SailM (BitVec 64) )
  let target ← (( do
    if ((←((pure (BEq.beq branch_type BranchType_RET)) <&&> (do
         (HaveGCS ())) <&&> (do
         (GCSPCREnabled (← readReg PSTATE).EL)))) : Bool)
    then
      (do
        let inst_type : GCSInstruction :=
          if ((! pac) : Bool)
          then GCSInstType_PRET
          else
            (if (use_key_a : Bool)
            then GCSInstType_PRETAA
            else GCSInstType_PRETAB)
        let target ← (LoadCheckGCSRecord target inst_type)
        (SetCurrentGCSPointer (BitVec.addInt (← (GetCurrentGCSPointer ())) 8))
        (pure target))
    else (pure target) ) : SailM (BitVec 64) )
  if ((BEq.beq branch_type BranchType_INDCALL) : Bool)
  then
    (do
      if ((←((HaveGCS ()) <&&> (do
           (GCSPCREnabled (← readReg PSTATE).EL)))) : Bool)
      then (AddGCSRecord (BitVec.addInt (← (PC_read ())) 4))
      else (pure ())
      (X_set 30 64 (BitVec.addInt (← (PC_read ())) 4)))
  else (pure ())
  match branch_type with
  | .BranchType_INDIR =>
    (do
      if ((← readReg InGuardedPage) : Bool)
      then
        (do
          if (((n == 16) || (n == 17)) : Bool)
          then writeReg BTypeNext 0b01#2
          else writeReg BTypeNext 0b11#2)
      else writeReg BTypeNext 0b01#2)
  | .BranchType_INDCALL => writeReg BTypeNext 0b10#2
  | .BranchType_RET => writeReg BTypeNext 0b00#2
  | _ => (pure ())
  let branch_conditional : Bool := false
  (BranchTo target branch_type branch_conditional)

def decode_blr_aarch64_instrs_branch_unconditional_register (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) : SailM Unit := do
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

def decode_br_aarch64_instrs_branch_unconditional_register (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) : SailM Unit := do
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

def decode_ret_aarch64_instrs_branch_unconditional_register (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) : SailM Unit := do
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

/-- Type quantifiers: datasize : Nat, k_iszero : Bool, t : Nat, 0 ≤ t ∧ t ≤ 31 ∧ List.elem datasize [32, 64] -/
def execute_aarch64_instrs_branch_conditional_compare (datasize : Nat) (iszero : Bool) (offset : (BitVec 64)) (t : Nat) : SailM Unit := do
  let operand1 ← (( do (X_read t datasize) ) : SailM (BitVec datasize) )
  let branch_conditional : Bool := true
  if (((IsZero operand1) == iszero) : Bool)
  then (BranchTo ((← (PC_read ())) + offset) BranchType_DIR branch_conditional)
  else (BranchNotTaken BranchType_DIR branch_conditional)

def decode_cbnz_aarch64_instrs_branch_conditional_compare (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let iszero : Bool := (op == 0#1)
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  (execute_aarch64_instrs_branch_conditional_compare datasize iszero offset t)

def decode_cbz_aarch64_instrs_branch_conditional_compare (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let iszero : Bool := (op == 0#1)
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  (execute_aarch64_instrs_branch_conditional_compare datasize iszero offset t)

/-- Type quantifiers: d : Nat, datasize : Nat, k_else_inc : Bool, k_else_inv : Bool, m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_conditional_select (condition : (BitVec 4)) (d : Nat) (datasize : Nat) (else_inc : Bool) (else_inv : Bool) (m : Nat) (n : Nat) : SailM Unit := do
  let taken : Bool := false
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let (result, taken) ← (( do
    if ((← (ConditionHolds condition)) : Bool)
    then
      (do
        let result ← (X_read n datasize)
        let taken : Bool := true
        (pure (result, taken)))
    else
      (do
        let result ← (X_read m datasize)
        let result : (BitVec datasize) :=
          if (else_inv : Bool)
          then (Complement.complement result)
          else result
        let result : (BitVec datasize) :=
          if (else_inc : Bool)
          then (BitVec.addInt result 1)
          else result
        (pure (result, taken))) ) : SailM ((BitVec datasize) × Bool) )
  (X_set d datasize result)
  if ((← readReg SPESampleInFlight) : Bool)
  then
    (do
      let conditional : Bool := true
      (SPESampleAddOpOther conditional taken))
  else (pure ())

def decode_csel_aarch64_instrs_integer_conditional_select (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
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

def decode_csinc_aarch64_instrs_integer_conditional_select (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
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

/-- Type quantifiers: datasize : Nat, k_is_signed : Bool, n : Nat, k_nontemporal : Bool, k_postindex : Bool, regsize : Nat, k_rt_unknown : Bool, t : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback : Bool, 0 ≤ t ∧ t ≤ 31 ∧ List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_single_general_immediate_signed_post_idx (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (regsize : Nat) (rt_unknown : Bool) (is_signed : Bool) (t : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
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
          sail_assert ((datasize >b 0) && (regsize ≥b datasize)) "src/instrs64.sail:32855.72-32855.73"
          (X_set t regsize (sign_extend data regsize)))
      else
        (do
          sail_assert ((datasize ≥b 0) && (regsize ≥b datasize)) "src/instrs64.sail:32858.73-32858.74"
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

def decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:32921.113-32921.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:32940.107-32940.108"
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

def decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33007.113-33007.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33026.107-33026.108"
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

def decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33093.113-33093.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33112.107-33112.108"
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

def decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33179.113-33179.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33198.107-33198.108"
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

def decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33265.113-33265.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33284.107-33284.108"
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

def decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33351.113-33351.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:33370.107-33370.108"
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

def decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34469.113-34469.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34488.107-34488.108"
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

def decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34555.113-34555.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34574.107-34574.108"
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

def decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34641.113-34641.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34660.107-34660.108"
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

def decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34727.113-34727.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34746.107-34746.108"
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

def decode_strb_imm_aarch64_instrs_memory_single_general_immediate_signed_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34813.113-34813.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34832.107-34832.108"
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

def decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34899.113-34899.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:34918.107-34918.108"
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

/-- Type quantifiers: datasize : Nat, k_is_signed : Bool, n : Nat, k_nontemporal : Bool, k_postindex : Bool, regsize : Nat, k_rt_unknown : Bool, t : Nat, k_tagchecked : Bool, k_wb_unknown : Bool, k_wback : Bool, 0 ≤ t ∧ t ≤ 31 ∧ List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (datasize : Nat) (memop : MemOp) (n : Nat) (nontemporal : Bool) (offset : (BitVec 64)) (postindex : Bool) (regsize : Nat) (rt_unknown : Bool) (is_signed : Bool) (t : Nat) (tagchecked : Bool) (wb_unknown : Bool) (wback : Bool) : SailM Unit := do
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
          sail_assert ((datasize >b 0) && (regsize ≥b datasize)) "src/instrs64.sail:37529.72-37529.73"
          (X_set t regsize (sign_extend data regsize)))
      else
        (do
          sail_assert ((datasize ≥b 0) && (regsize ≥b datasize)) "src/instrs64.sail:37532.73-37532.74"
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

def decode_ldur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37599.113-37599.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37618.107-37618.108"
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

def decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:38229.113-38229.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:38248.107-38248.108"
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

/-- Type quantifiers: a : Nat, d : Nat, datasize : Nat, destsize : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem destsize [32, 64] ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (a : Nat) (d : Nat) (datasize : Nat) (destsize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  let operand1 ← (( do (X_read n datasize) ) : SailM (BitVec datasize) )
  let operand2 ← (( do (X_read m datasize) ) : SailM (BitVec datasize) )
  let operand3 ← (( do (X_read a destsize) ) : SailM (BitVec destsize) )
  let result ← (( do (undefined_int ()) ) : SailM Int )
  let result : Int :=
    if (sub_op : Bool)
    then ((BitVec.toNat operand3) -i ((BitVec.toNat operand1) *i (BitVec.toNat operand2)))
    else ((BitVec.toNat operand3) +i ((BitVec.toNat operand1) *i (BitVec.toNat operand2)))
  let result := result
  (X_set d destsize (integer_subrange result (destsize -i 1) 0))

def decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
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

/-- Type quantifiers: d : Nat, datasize : Nat, pos : Nat, 0 ≤ pos ∧ pos ≤ 63 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_ins_ext_insert_movewide (d : Nat) (datasize : Nat) (imm : (BitVec 16)) (opcode : MoveWideOp) (pos : Nat) : SailM Unit := do
  let result ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let result ← (( do
    if ((BEq.beq opcode MoveWideOp_K) : Bool)
    then (do (X_read d datasize))
    else (pure (Zeros (n := datasize))) ) : SailM (BitVec datasize) )
  sail_assert ((pos +i 15) <b datasize) "src/instrs64.sail:38730.44-38730.45"
  let result : (BitVec datasize) := (Sail.BitVec.updateSubrange result (pos +i 15) pos imm)
  let result : (BitVec datasize) :=
    if ((BEq.beq opcode MoveWideOp_N) : Bool)
    then (Complement.complement result)
    else result
  let result := result
  (X_set d datasize result)

def decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide (Rd : (BitVec 5)) (imm16 : (BitVec 16)) (hw : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
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

def decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide (Rd : (BitVec 5)) (imm16 : (BitVec 16)) (hw : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
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


