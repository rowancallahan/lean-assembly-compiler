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
import Armv9.Instrs64.P00

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

def decode_uhsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int d datasize elements esize m n is_unsigned)

def decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((BitVec.join1 [(BitVec.access immh 3)]) != 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 3)
  let datasize := esize
  let elements := 1
  let shift := ((BitVec.toNat (immh +++ immb)) -i esize)
  (execute_aarch64_instrs_vector_shift_left_insert_sisd d datasize elements esize n shift)

def decode_sli_advsimd_aarch64_instrs_vector_shift_left_insert_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access immh 3)]) +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (fdiv_int datasize esize)
  let shift := ((BitVec.toNat (immh +++ immb)) -i esize)
  (execute_aarch64_instrs_vector_shift_left_insert_sisd d datasize elements esize n shift)

def decode_sm3partw1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw1 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSM3Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  (execute_aarch64_instrs_vector_crypto_sm3_sm3partw1 d m n)

def decode_sm3partw2_advsimd_aarch64_instrs_vector_crypto_sm3_sm3partw2 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSM3Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  (execute_aarch64_instrs_vector_crypto_sm3_sm3partw2 d m n)

def decode_sm3ss1_advsimd_aarch64_instrs_vector_crypto_sm3_sm3ss1 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSM3Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let a := (BitVec.toNat Ra)
  (execute_aarch64_instrs_vector_crypto_sm3_sm3ss1 a d m n)

def decode_sm3tt1a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1a (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSM3Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let i := (BitVec.toNat imm2)
  (execute_aarch64_instrs_vector_crypto_sm3_sm3tt1a d i m n)

def decode_sm3tt1b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt1b (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSM3Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let i := (BitVec.toNat imm2)
  (execute_aarch64_instrs_vector_crypto_sm3_sm3tt1b d i m n)

def decode_sm3tt2a_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2a (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSM3Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let i := (BitVec.toNat imm2)
  (execute_aarch64_instrs_vector_crypto_sm3_sm3tt2a d i m n)

def decode_sm3tt2b_advsimd_aarch64_instrs_vector_crypto_sm3_sm3tt2b (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm2 : (BitVec 2)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSM3Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let i := (BitVec.toNat imm2)
  (execute_aarch64_instrs_vector_crypto_sm3_sm3tt2b d i m n)

def decode_sm4e_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enc (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSM4Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  (execute_aarch64_instrs_vector_crypto_sm4_sm4enc d n)

def decode_sm4ekey_advsimd_aarch64_instrs_vector_crypto_sm4_sm4enckey (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSM4Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  (execute_aarch64_instrs_vector_crypto_sm4_sm4enckey d m n)

def decode_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let a := (BitVec.toNat Ra)
  let destsize := 64
  let datasize := 32
  let sub_op : Bool := (o0 == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64 a d datasize destsize m n sub_op is_unsigned)

def decode_smsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let a := (BitVec.toNat Ra)
  let destsize := 64
  let datasize := 32
  let sub_op : Bool := (o0 == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64 a d datasize destsize m n sub_op is_unsigned)

def decode_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let a := (BitVec.toNat Ra)
  let destsize := 64
  let datasize := 32
  let sub_op : Bool := (o0 == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64 a d datasize destsize m n sub_op is_unsigned)

def decode_umsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let a := (BitVec.toNat Ra)
  let destsize := 64
  let datasize := 32
  let sub_op : Bool := (o0 == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64 a d datasize destsize m n sub_op is_unsigned)

def decode_smax_imm_aarch64_instrs_integer_arithmetic_max_min_smax_imm (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm8 : (BitVec 8)) (sf : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveCSSC ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let d := (BitVec.toNat Rd)
  let imm := (BitVec.toInt imm8)
  (execute_aarch64_instrs_integer_arithmetic_max_min_smax_imm d datasize imm n)

def decode_smax_reg_aarch64_instrs_integer_arithmetic_max_min_smax_reg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveCSSC ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  (execute_aarch64_instrs_integer_arithmetic_max_min_smax_reg d datasize m n)

def decode_smax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single d datasize elements esize m minimum n is_unsigned)

def decode_smin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single d datasize elements esize m minimum n is_unsigned)

def decode_umax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single d datasize elements esize m minimum n is_unsigned)

def decode_umin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_single d datasize elements esize m minimum n is_unsigned)

def decode_smaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair d datasize elements esize m minimum n is_unsigned)

def decode_sminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair d datasize elements esize m minimum n is_unsigned)

def decode_umaxp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair d datasize elements esize m minimum n is_unsigned)

def decode_uminp_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_pair d datasize elements esize m minimum n is_unsigned)

def decode_smaxv_advsimd_aarch64_instrs_vector_reduce_int_max (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  let min : Bool := (op == 1#1)
  (execute_aarch64_instrs_vector_reduce_int_max d datasize elements esize min n is_unsigned)

def decode_sminv_advsimd_aarch64_instrs_vector_reduce_int_max (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  let min : Bool := (op == 1#1)
  (execute_aarch64_instrs_vector_reduce_int_max d datasize elements esize min n is_unsigned)

def decode_umaxv_advsimd_aarch64_instrs_vector_reduce_int_max (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  let min : Bool := (op == 1#1)
  (execute_aarch64_instrs_vector_reduce_int_max d datasize elements esize min n is_unsigned)

def decode_uminv_advsimd_aarch64_instrs_vector_reduce_int_max (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  let min : Bool := (op == 1#1)
  (execute_aarch64_instrs_vector_reduce_int_max d datasize elements esize min n is_unsigned)

def decode_smc_aarch64_instrs_system_exceptions_runtime_smc (imm16 : (BitVec 16)) : SailM Unit := do
  let imm : (BitVec 16) := imm16
  (execute_aarch64_instrs_system_exceptions_runtime_smc imm)

def decode_smin_imm_aarch64_instrs_integer_arithmetic_max_min_smin_imm (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm8 : (BitVec 8)) (sf : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveCSSC ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let d := (BitVec.toNat Rd)
  let imm := (BitVec.toInt imm8)
  (execute_aarch64_instrs_integer_arithmetic_max_min_smin_imm d datasize imm n)

def decode_smin_reg_aarch64_instrs_integer_arithmetic_max_min_smin_reg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveCSSC ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  (execute_aarch64_instrs_integer_arithmetic_max_min_smin_reg d datasize m n)

def decode_smlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum d datasize elements esize m n part sub_op is_unsigned)

def decode_smlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum d datasize elements esize m n part sub_op is_unsigned)

def decode_umlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum d datasize elements esize m n part sub_op is_unsigned)

def decode_umlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_accum d datasize elements esize m n part sub_op is_unsigned)

def decode_smlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long d datasize elements esize idxdsize index m n part sub_op is_unsigned)

def decode_smlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long d datasize elements esize idxdsize index m n part sub_op is_unsigned)

def decode_umlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long d datasize elements esize idxdsize index m n part sub_op is_unsigned)

def decode_umlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_long d datasize elements esize idxdsize index m n part sub_op is_unsigned)

def decode_smmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla (Rd : (BitVec 5)) (Rn : (BitVec 5)) (B : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveInt8MatMulExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let op1_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let op2_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let (op1_unsigned, op2_unsigned) ← (( do
    match ((B +++ U) : BitVec 2) with
    | 0b00 =>
      (let op1_unsigned : Bool := false
      let op2_unsigned : Bool := false
      (pure (op1_unsigned, op2_unsigned)))
    | 0b01 =>
      (let op1_unsigned : Bool := true
      let op2_unsigned : Bool := true
      (pure (op1_unsigned, op2_unsigned)))
    | 0b10 =>
      (let op1_unsigned : Bool := true
      let op2_unsigned : Bool := false
      (pure (op1_unsigned, op2_unsigned)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × Bool) )
  let op2_unsigned := op2_unsigned
  let op1_unsigned := op1_unsigned
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla d m n op1_unsigned op2_unsigned)

def decode_ummla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla (Rd : (BitVec 5)) (Rn : (BitVec 5)) (B : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveInt8MatMulExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let op1_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let op2_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let (op1_unsigned, op2_unsigned) ← (( do
    match ((B +++ U) : BitVec 2) with
    | 0b00 =>
      (let op1_unsigned : Bool := false
      let op2_unsigned : Bool := false
      (pure (op1_unsigned, op2_unsigned)))
    | 0b01 =>
      (let op1_unsigned : Bool := true
      let op2_unsigned : Bool := true
      (pure (op1_unsigned, op2_unsigned)))
    | 0b10 =>
      (let op1_unsigned : Bool := true
      let op2_unsigned : Bool := false
      (pure (op1_unsigned, op2_unsigned)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × Bool) )
  let op2_unsigned := op2_unsigned
  let op1_unsigned := op1_unsigned
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla d m n op1_unsigned op2_unsigned)

def decode_usmmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla (Rd : (BitVec 5)) (Rn : (BitVec 5)) (B : (BitVec 1)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveInt8MatMulExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let op1_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let op2_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let (op1_unsigned, op2_unsigned) ← (( do
    match ((B +++ U) : BitVec 2) with
    | 0b00 =>
      (let op1_unsigned : Bool := false
      let op2_unsigned : Bool := false
      (pure (op1_unsigned, op2_unsigned)))
    | 0b01 =>
      (let op1_unsigned : Bool := true
      let op2_unsigned : Bool := true
      (pure (op1_unsigned, op2_unsigned)))
    | 0b10 =>
      (let op1_unsigned : Bool := true
      let op2_unsigned : Bool := false
      (pure (op1_unsigned, op2_unsigned)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × Bool) )
  let op2_unsigned := op2_unsigned
  let op1_unsigned := op1_unsigned
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_mla d m n op1_unsigned op2_unsigned)

def decode_smov_advsimd_aarch64_instrs_vector_transfer_integer_move_signed (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let size : Nat := 0
  let size ← (( do
    let b__0 := (Q +++ imm5)
    if (((Sail.BitVec.extractLsb b__0 0 0) == (1#1 : (BitVec 1))) : Bool)
    then (pure 0)
    else
      (do
        if (((Sail.BitVec.extractLsb b__0 1 0) == (0b10#2 : (BitVec 2))) : Bool)
        then (pure 1)
        else
          (do
            if ((((Sail.BitVec.extractLsb b__0 5 5) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 2 0) == (0b100#3 : (BitVec 3)))) : Bool)
            then (pure 2)
            else sailThrow ((Error_Undefined ())))) ) : SailM Int )
  let size := size
  let idxdsize :=
    if (((BitVec.join1 [(BitVec.access imm5 4)]) == 1#1) : Bool)
    then 128
    else 64
  let index := (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 (size +i 1)))
  let esize := (Int.shiftl 8 size)
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 64
    else 32
  sail_assert (((esize == 8) || (esize == 16)) || (esize == 32)) "src/instrs64.sail:46177.44-46177.45"
  (execute_aarch64_instrs_vector_transfer_integer_move_signed d datasize esize idxdsize index n)

def decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let a := (BitVec.toNat Ra)
  let destsize := 64
  let datasize := destsize
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi d datasize m n is_unsigned)

def decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let a := (BitVec.toNat Ra)
  let destsize := 64
  let datasize := destsize
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi d datasize m n is_unsigned)

def decode_smull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product d datasize elements esize m n part is_unsigned)

def decode_umull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_product d datasize elements esize m n part is_unsigned)

def decode_smull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_long d datasize elements esize idxdsize index m n part is_unsigned)

def decode_umull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_long d datasize elements esize idxdsize index m n part is_unsigned)

def decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd d datasize elements esize n neg)

def decode_sqabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd d datasize elements esize n neg)

def decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd d datasize elements esize n neg)

def decode_sqneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_sat_sisd d datasize elements esize n neg)

def decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd d datasize elements esize m n is_unsigned)

def decode_sqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd d datasize elements esize m n is_unsigned)

def decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd d datasize elements esize m n is_unsigned)

def decode_uqadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_saturating_sisd d datasize elements esize m n is_unsigned)

def decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let part := 0
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd d datasize elements esize idxdsize index m n part sub_op)

def decode_sqdmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd d datasize elements esize idxdsize index m n part sub_op)

def decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let part := 0
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd d datasize elements esize idxdsize index m n part sub_op)

def decode_sqdmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_double_sisd d datasize elements esize idxdsize index m n part sub_op)

def decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let part := 0
  let sub_op : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd d datasize elements esize m n part sub_op)

def decode_sqdmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd d datasize elements esize m n part sub_op)

def decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let part := 0
  let sub_op : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd d datasize elements esize m n part sub_op)

def decode_sqdmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_dmacc_sisd d datasize elements esize m n part sub_op)

def decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size == 0b11#2) || (size == 0b00#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let rounding : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd d datasize elements esize m n rounding)

def decode_sqdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size == 0b11#2) || (size == 0b00#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let rounding : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd d datasize elements esize m n rounding)

def decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size == 0b11#2) || (size == 0b00#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let rounding : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd d datasize elements esize m n rounding)

def decode_sqrdmulh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size == 0b11#2) || (size == 0b00#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let rounding : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_sisd d datasize elements esize m n rounding)

def decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (op : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let round : Bool := (op == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd d datasize elements esize idxdsize index m n round)

def decode_sqdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (op : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let round : Bool := (op == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd d datasize elements esize idxdsize index m n round)

def decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (op : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let round : Bool := (op == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd d datasize elements esize idxdsize index m n round)

def decode_sqrdmulh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_high_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (op : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let round : Bool := (op == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_high_sisd d datasize elements esize idxdsize index m n round)

def decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let part := 0
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd d datasize elements esize m n part)

def decode_sqdmull_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_double_sisd d datasize elements esize m n part)

def decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let part := 0
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd d datasize elements esize idxdsize index m n part)

def decode_sqdmull_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_double_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_double_sisd d datasize elements esize idxdsize index m n part)

def decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveQRDMLAHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size == 0b11#2) || (size == 0b00#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let rounding : Bool := true
  let sub_op : Bool := (S == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd d datasize elements esize m n rounding sub_op)

def decode_sqrdmlah_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveQRDMLAHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size == 0b11#2) || (size == 0b00#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let rounding : Bool := true
  let sub_op : Bool := (S == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd d datasize elements esize m n rounding sub_op)

def decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveQRDMLAHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size == 0b11#2) || (size == 0b00#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let rounding : Bool := true
  let sub_op : Bool := (S == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd d datasize elements esize m n rounding sub_op)

def decode_sqrdmlsh_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveQRDMLAHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size == 0b11#2) || (size == 0b00#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let rounding : Bool := true
  let sub_op : Bool := (S == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd d datasize elements esize m n rounding sub_op)

def decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveQRDMLAHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let rounding : Bool := true
  let sub_op : Bool := (S == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd d datasize elements esize idxdsize index m n rounding sub_op)

def decode_sqrdmlah_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveQRDMLAHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let rounding : Bool := true
  let sub_op : Bool := (S == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd d datasize elements esize idxdsize index m n rounding sub_op)

def decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveQRDMLAHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let rounding : Bool := true
  let sub_op : Bool := (S == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd d datasize elements esize idxdsize index m n rounding sub_op)

def decode_sqrdmlsh_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveQRDMLAHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 7) ) : SailM Nat )
  let Rmhi ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (Rmhi, index) ← (( do
    match (size : BitVec 2) with
    | 0b01 =>
      (let index : Nat := (BitVec.toNat ((H +++ L) +++ M))
      let Rmhi : (BitVec 1) := 0#1
      (pure (Rmhi, index)))
    | 0b10 =>
      (let index : Nat := (BitVec.toNat (H +++ L))
      let Rmhi : (BitVec 1) := M
      (pure (Rmhi, index)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM ((BitVec 1) × Nat) )
  let Rmhi := Rmhi
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let rounding : Bool := true
  let sub_op : Bool := (S == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_high_sisd d datasize elements esize idxdsize index m n rounding sub_op)

def decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  if (((S == 0#1) && (size != 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d datasize elements esize m n rounding saturating is_unsigned)

def decode_sqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d datasize elements esize m n rounding saturating is_unsigned)

def decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  if (((S == 0#1) && (size != 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d datasize elements esize m n rounding saturating is_unsigned)

def decode_sqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d datasize elements esize m n rounding saturating is_unsigned)

def decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  if (((S == 0#1) && (size != 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d datasize elements esize m n rounding saturating is_unsigned)

def decode_srshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d datasize elements esize m n rounding saturating is_unsigned)

def decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  if (((S == 0#1) && (size != 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d datasize elements esize m n rounding saturating is_unsigned)

def decode_sshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d datasize elements esize m n rounding saturating is_unsigned)

def decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  if (((S == 0#1) && (size != 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d datasize elements esize m n rounding saturating is_unsigned)

def decode_uqrshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d datasize elements esize m n rounding saturating is_unsigned)

def decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  if (((S == 0#1) && (size != 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d datasize elements esize m n rounding saturating is_unsigned)

def decode_uqshl_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d datasize elements esize m n rounding saturating is_unsigned)

def decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  if (((S == 0#1) && (size != 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d datasize elements esize m n rounding saturating is_unsigned)

def decode_urshl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d datasize elements esize m n rounding saturating is_unsigned)

def decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  if (((S == 0#1) && (size != 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d datasize elements esize m n rounding saturating is_unsigned)

def decode_ushl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_shift_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  let rounding : Bool := (R == 1#1)
  let saturating : Bool := (S == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_shift_sisd d datasize elements esize m n rounding saturating is_unsigned)

def decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access immh 3)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := esize
  let elements := 1
  let part := 0
  let shift := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  sail_assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && (((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64))) "src/instrs64.sail:48572.87-48572.88"
  (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd d datasize elements esize n part round shift is_unsigned)

def decode_sqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access immh 3)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (fdiv_int datasize esize)
  let shift := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  sail_assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:48605.51-48605.52"
  (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd d datasize elements esize n part round shift is_unsigned)

def decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access immh 3)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := esize
  let elements := 1
  let part := 0
  let shift := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  sail_assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && (((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64))) "src/instrs64.sail:48639.87-48639.88"
  (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd d datasize elements esize n part round shift is_unsigned)

def decode_sqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access immh 3)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (fdiv_int datasize esize)
  let shift := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  sail_assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:48672.51-48672.52"
  (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd d datasize elements esize n part round shift is_unsigned)

def decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access immh 3)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := esize
  let elements := 1
  let part := 0
  let shift := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  sail_assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && (((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64))) "src/instrs64.sail:48706.87-48706.88"
  (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd d datasize elements esize n part round shift is_unsigned)

def decode_uqrshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access immh 3)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (fdiv_int datasize esize)
  let shift := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  sail_assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:48739.51-48739.52"
  (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd d datasize elements esize n part round shift is_unsigned)

def decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access immh 3)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := esize
  let elements := 1
  let part := 0
  let shift := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  sail_assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && (((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64))) "src/instrs64.sail:48773.87-48773.88"
  (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd d datasize elements esize n part round shift is_unsigned)

def decode_uqshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_uniform_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access immh 3)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (fdiv_int datasize esize)
  let shift := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  sail_assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:48806.51-48806.52"
  (execute_aarch64_instrs_vector_shift_right_narrow_uniform_sisd d datasize elements esize n part round shift is_unsigned)

def decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access immh 3)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := esize
  let elements := 1
  let part := 0
  let shift := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  sail_assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && (((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64))) "src/instrs64.sail:48866.87-48866.88"
  (execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd d datasize elements esize n part round shift)

def decode_sqrshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access immh 3)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (fdiv_int datasize esize)
  let shift := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  sail_assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:48897.51-48897.52"
  (execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd d datasize elements esize n part round shift)

def decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access immh 3)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := esize
  let elements := 1
  let part := 0
  let shift := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  sail_assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && (((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64))) "src/instrs64.sail:48929.87-48929.88"
  (execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd d datasize elements esize n part round shift)

def decode_sqshrun_advsimd_aarch64_instrs_vector_shift_right_narrow_nonuniform_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access immh 3)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (fdiv_int datasize esize)
  let shift := ((2 *i esize) -i (BitVec.toNat (immh +++ immb)))
  let round : Bool := (op == 1#1)
  sail_assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:48960.51-48960.52"
  (execute_aarch64_instrs_vector_shift_right_narrow_nonuniform_sisd d datasize elements esize n part round shift)

def decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := esize
  let elements := 1
  let shift := ((BitVec.toNat (immh +++ immb)) -i esize)
  let src_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let dst_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let (dst_unsigned, src_unsigned) ← (( do
    match ((op +++ U) : BitVec 2) with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := true
      (pure (dst_unsigned, src_unsigned)))
    | 0b10 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := false
      (pure (dst_unsigned, src_unsigned)))
    | _ =>
      (let src_unsigned : Bool := true
      let dst_unsigned : Bool := true
      (pure (dst_unsigned, src_unsigned))) ) : SailM (Bool × Bool) )
  let dst_unsigned := dst_unsigned
  let src_unsigned := src_unsigned
  sail_assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128))) "src/instrs64.sail:49036.92-49036.93"
  (execute_aarch64_instrs_vector_shift_left_sat_sisd d datasize dst_unsigned elements esize n shift src_unsigned)

def decode_sqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access immh 3)]) +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (fdiv_int datasize esize)
  let shift := ((BitVec.toNat (immh +++ immb)) -i esize)
  let src_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let dst_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let (dst_unsigned, src_unsigned) ← (( do
    match ((op +++ U) : BitVec 2) with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := true
      (pure (dst_unsigned, src_unsigned)))
    | 0b10 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := false
      (pure (dst_unsigned, src_unsigned)))
    | _ =>
      (let src_unsigned : Bool := true
      let dst_unsigned : Bool := true
      (pure (dst_unsigned, src_unsigned))) ) : SailM (Bool × Bool) )
  let dst_unsigned := dst_unsigned
  let src_unsigned := src_unsigned
  sail_assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:49087.51-49087.52"
  (execute_aarch64_instrs_vector_shift_left_sat_sisd d datasize dst_unsigned elements esize n shift src_unsigned)

def decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := esize
  let elements := 1
  let shift := ((BitVec.toNat (immh +++ immb)) -i esize)
  let src_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let dst_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let (dst_unsigned, src_unsigned) ← (( do
    match ((op +++ U) : BitVec 2) with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := true
      (pure (dst_unsigned, src_unsigned)))
    | 0b10 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := false
      (pure (dst_unsigned, src_unsigned)))
    | _ =>
      (let src_unsigned : Bool := true
      let dst_unsigned : Bool := true
      (pure (dst_unsigned, src_unsigned))) ) : SailM (Bool × Bool) )
  let dst_unsigned := dst_unsigned
  let src_unsigned := src_unsigned
  sail_assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128))) "src/instrs64.sail:49136.92-49136.93"
  (execute_aarch64_instrs_vector_shift_left_sat_sisd d datasize dst_unsigned elements esize n shift src_unsigned)

def decode_sqshlu_advsimd_aarch64_instrs_vector_shift_left_sat_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access immh 3)]) +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (fdiv_int datasize esize)
  let shift := ((BitVec.toNat (immh +++ immb)) -i esize)
  let src_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let dst_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let (dst_unsigned, src_unsigned) ← (( do
    match ((op +++ U) : BitVec 2) with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := true
      (pure (dst_unsigned, src_unsigned)))
    | 0b10 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := false
      (pure (dst_unsigned, src_unsigned)))
    | _ =>
      (let src_unsigned : Bool := true
      let dst_unsigned : Bool := true
      (pure (dst_unsigned, src_unsigned))) ) : SailM (Bool × Bool) )
  let dst_unsigned := dst_unsigned
  let src_unsigned := src_unsigned
  sail_assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:49187.51-49187.52"
  (execute_aarch64_instrs_vector_shift_left_sat_sisd d datasize dst_unsigned elements esize n shift src_unsigned)

def decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := esize
  let elements := 1
  let shift := ((BitVec.toNat (immh +++ immb)) -i esize)
  let src_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let dst_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let (dst_unsigned, src_unsigned) ← (( do
    match ((op +++ U) : BitVec 2) with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := true
      (pure (dst_unsigned, src_unsigned)))
    | 0b10 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := false
      (pure (dst_unsigned, src_unsigned)))
    | _ =>
      (let src_unsigned : Bool := true
      let dst_unsigned : Bool := true
      (pure (dst_unsigned, src_unsigned))) ) : SailM (Bool × Bool) )
  let dst_unsigned := dst_unsigned
  let src_unsigned := src_unsigned
  sail_assert ((((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((((((datasize == 4) || (datasize == 8)) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128))) "src/instrs64.sail:49236.92-49236.93"
  (execute_aarch64_instrs_vector_shift_left_sat_sisd d datasize dst_unsigned elements esize n shift src_unsigned)

def decode_uqshl_advsimd_imm_aarch64_instrs_vector_shift_left_sat_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access immh 3)]) +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (fdiv_int datasize esize)
  let shift := ((BitVec.toNat (immh +++ immb)) -i esize)
  let src_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let dst_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let (dst_unsigned, src_unsigned) ← (( do
    match ((op +++ U) : BitVec 2) with
    | 0b00 => sailThrow ((Error_Undefined ()))
    | 0b01 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := true
      (pure (dst_unsigned, src_unsigned)))
    | 0b10 =>
      (let src_unsigned : Bool := false
      let dst_unsigned : Bool := false
      (pure (dst_unsigned, src_unsigned)))
    | _ =>
      (let src_unsigned : Bool := true
      let dst_unsigned : Bool := true
      (pure (dst_unsigned, src_unsigned))) ) : SailM (Bool × Bool) )
  let dst_unsigned := dst_unsigned
  let src_unsigned := src_unsigned
  sail_assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:49287.51-49287.52"
  (execute_aarch64_instrs_vector_shift_left_sat_sisd d datasize dst_unsigned elements esize n shift src_unsigned)

def decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd d datasize elements esize m n is_unsigned)

def decode_sqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd d datasize elements esize m n is_unsigned)

def decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd d datasize elements esize m n is_unsigned)

def decode_uqsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_saturating_sisd d datasize elements esize m n is_unsigned)

def decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let part := 0
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd d datasize elements esize n part is_unsigned)

def decode_sqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd d datasize elements esize n part is_unsigned)

def decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let part := 0
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd d datasize elements esize n part is_unsigned)

def decode_uqxtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sat_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_extract_sat_sisd d datasize elements esize n part is_unsigned)

def decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let part := 0
  let elements := 1
  (execute_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd d datasize elements esize n part)

def decode_sqxtun_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_unary_extract_sqxtun_sisd d datasize elements esize n part)

def decode_srhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding d datasize elements esize m n is_unsigned)

def decode_urhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_rounding d datasize elements esize m n is_unsigned)

def decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((BitVec.join1 [(BitVec.access immh 3)]) != 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 3)
  let datasize := esize
  let elements := 1
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  (execute_aarch64_instrs_vector_shift_right_insert_sisd d datasize elements esize n shift)

def decode_sri_advsimd_aarch64_instrs_vector_shift_right_insert_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access immh 3)]) +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (fdiv_int datasize esize)
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  (execute_aarch64_instrs_vector_shift_right_insert_sisd d datasize elements esize n shift)

def decode_srshr_advsimd_aarch64_instrs_vector_shift_right_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((BitVec.join1 [(BitVec.access immh 3)]) != 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 3)
  let datasize := esize
  let elements := 1
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate d datasize elements esize n round shift is_unsigned)

def decode_srshr_advsimd_aarch64_instrs_vector_shift_right_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access immh 3)]) +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (fdiv_int datasize esize)
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate d datasize elements esize n round shift is_unsigned)

def decode_srsra_advsimd_aarch64_instrs_vector_shift_right_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((BitVec.join1 [(BitVec.access immh 3)]) != 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 3)
  let datasize := esize
  let elements := 1
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate d datasize elements esize n round shift is_unsigned)

def decode_srsra_advsimd_aarch64_instrs_vector_shift_right_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access immh 3)]) +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (fdiv_int datasize esize)
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate d datasize elements esize n round shift is_unsigned)

def decode_sshr_advsimd_aarch64_instrs_vector_shift_right_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((BitVec.join1 [(BitVec.access immh 3)]) != 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 3)
  let datasize := esize
  let elements := 1
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate d datasize elements esize n round shift is_unsigned)

def decode_sshr_advsimd_aarch64_instrs_vector_shift_right_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access immh 3)]) +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (fdiv_int datasize esize)
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate d datasize elements esize n round shift is_unsigned)

def decode_ssra_advsimd_aarch64_instrs_vector_shift_right_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((BitVec.join1 [(BitVec.access immh 3)]) != 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 3)
  let datasize := esize
  let elements := 1
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate d datasize elements esize n round shift is_unsigned)

def decode_ssra_advsimd_aarch64_instrs_vector_shift_right_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access immh 3)]) +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (fdiv_int datasize esize)
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate d datasize elements esize n round shift is_unsigned)

def decode_urshr_advsimd_aarch64_instrs_vector_shift_right_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((BitVec.join1 [(BitVec.access immh 3)]) != 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 3)
  let datasize := esize
  let elements := 1
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate d datasize elements esize n round shift is_unsigned)

def decode_urshr_advsimd_aarch64_instrs_vector_shift_right_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access immh 3)]) +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (fdiv_int datasize esize)
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate d datasize elements esize n round shift is_unsigned)

def decode_ursra_advsimd_aarch64_instrs_vector_shift_right_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((BitVec.join1 [(BitVec.access immh 3)]) != 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 3)
  let datasize := esize
  let elements := 1
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate d datasize elements esize n round shift is_unsigned)

def decode_ursra_advsimd_aarch64_instrs_vector_shift_right_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access immh 3)]) +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (fdiv_int datasize esize)
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate d datasize elements esize n round shift is_unsigned)

def decode_ushr_advsimd_aarch64_instrs_vector_shift_right_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((BitVec.join1 [(BitVec.access immh 3)]) != 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 3)
  let datasize := esize
  let elements := 1
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate d datasize elements esize n round shift is_unsigned)

def decode_ushr_advsimd_aarch64_instrs_vector_shift_right_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access immh 3)]) +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (fdiv_int datasize esize)
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate d datasize elements esize n round shift is_unsigned)

def decode_usra_advsimd_aarch64_instrs_vector_shift_right_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((BitVec.join1 [(BitVec.access immh 3)]) != 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 3)
  let datasize := esize
  let elements := 1
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate d datasize elements esize n round shift is_unsigned)

def decode_usra_advsimd_aarch64_instrs_vector_shift_right_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (o1 : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access immh 3)]) +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (fdiv_int datasize esize)
  let shift := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let round : Bool := (o1 == 1#1)
  let accumulate : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_vector_shift_right_sisd accumulate d datasize elements esize n round shift is_unsigned)

def decode_sshll_advsimd_aarch64_instrs_vector_shift_left_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access immh 3)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (fdiv_int datasize esize)
  let shift := ((BitVec.toNat (immh +++ immb)) -i esize)
  let is_unsigned : Bool := (U == 1#1)
  sail_assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:50352.51-50352.52"
  (execute_aarch64_instrs_vector_shift_left_long d datasize elements esize n part shift is_unsigned)

def decode_ushll_advsimd_aarch64_instrs_vector_shift_left_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access immh 3)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 (HighestSetBit immh))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (fdiv_int datasize esize)
  let shift := ((BitVec.toNat (immh +++ immb)) -i esize)
  let is_unsigned : Bool := (U == 1#1)
  sail_assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:50384.51-50384.52"
  (execute_aarch64_instrs_vector_shift_left_long d datasize elements esize n part shift is_unsigned)

def decode_st2g_aarch64_instrs_integer_tags_mcsettagpairpost (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Xn)
  let t := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := true
  let zero_data : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsettagpairpost n offset postindex t writeback zero_data)

def decode_st2g_aarch64_instrs_integer_tags_mcsettagpairpre (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Xn)
  let t := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := false
  let zero_data : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsettagpairpost n offset postindex t writeback zero_data)

def decode_st2g_aarch64_instrs_integer_tags_mcsettagpair (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Xn)
  let t := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := false
  let postindex : Bool := false
  let zero_data : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsettagpairpost n offset postindex t writeback zero_data)

def decode_st64b_aarch64_instrs_memory_atomicops_st_acc_st64b (Rt : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveFeatLS64 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((Sail.BitVec.extractLsb Rt 4 3) == 0b11#2) || ((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let memop : MemOp := MemOp_STORE
  let tagchecked : Bool := (n != 31)
  let lst : (BitVec 2) := lst_64b
  (execute_aarch64_instrs_memory_atomicops_st_acc_st64b lst memop n t tagchecked)

def decode_st64bv_aarch64_instrs_memory_atomicops_st_acc_st64bv (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveFeatLS64_V ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((Sail.BitVec.extractLsb Rt 4 3) == 0b11#2) || ((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let memop : MemOp := MemOp_STORE
  let s := (BitVec.toNat Rs)
  let tagchecked : Bool := (n != 31)
  let lst : (BitVec 2) := lst_64bv
  (execute_aarch64_instrs_memory_atomicops_st_acc_st64bv Rs lst memop n s t tagchecked)

def decode_st64bv0_aarch64_instrs_memory_atomicops_st_acc_st64bv0 (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveFeatLS64_ACCDATA ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((Sail.BitVec.extractLsb Rt 4 3) == 0b11#2) || ((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let memop : MemOp := MemOp_STORE
  let s := (BitVec.toNat Rs)
  let tagchecked : Bool := (n != 31)
  let lst : (BitVec 2) := lst_64bv0
  (execute_aarch64_instrs_memory_atomicops_st_acc_st64bv0 Rs lst memop n s t tagchecked)

def decode_stg_aarch64_instrs_integer_tags_mcsettagpost (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Xn)
  let t := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := true
  let zero_data : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsettagpost n offset postindex t writeback zero_data)

def decode_stg_aarch64_instrs_integer_tags_mcsettagpre (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Xn)
  let t := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := false
  let zero_data : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsettagpost n offset postindex t writeback zero_data)

def decode_stg_aarch64_instrs_integer_tags_mcsettag (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Xn)
  let t := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := false
  let postindex : Bool := false
  let zero_data : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsettagpost n offset postindex t writeback zero_data)

def decode_stgm_aarch64_instrs_integer_tags_mcsettagarray (Xt : (BitVec 5)) (Xn : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveMTE2Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Xt)
  let n := (BitVec.toNat Xn)
  (execute_aarch64_instrs_integer_tags_mcsettagarray n t)

def decode_stgp_aarch64_instrs_integer_tags_mcsettaganddatapairpost (Xt : (BitVec 5)) (Xn : (BitVec 5)) (Xt2 : (BitVec 5)) (simm7 : (BitVec 7)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Xn)
  let t := (BitVec.toNat Xt)
  let t2 := (BitVec.toNat Xt2)
  let offset : (BitVec 64) := ((sign_extend simm7 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := true
  (execute_aarch64_instrs_integer_tags_mcsettaganddatapairpost n offset postindex t t2 writeback)

def decode_stgp_aarch64_instrs_integer_tags_mcsettaganddatapairpre (Xt : (BitVec 5)) (Xn : (BitVec 5)) (Xt2 : (BitVec 5)) (simm7 : (BitVec 7)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Xn)
  let t := (BitVec.toNat Xt)
  let t2 := (BitVec.toNat Xt2)
  let offset : (BitVec 64) := ((sign_extend simm7 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsettaganddatapairpost n offset postindex t t2 writeback)

def decode_stgp_aarch64_instrs_integer_tags_mcsettaganddatapair (Xt : (BitVec 5)) (Xn : (BitVec 5)) (Xt2 : (BitVec 5)) (simm7 : (BitVec 7)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Xn)
  let t := (BitVec.toNat Xt)
  let t2 := (BitVec.toNat Xt2)
  let offset : (BitVec 64) := ((sign_extend simm7 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := false
  let postindex : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsettaganddatapairpost n offset postindex t t2 writeback)

def decode_stilp_aarch64_instrs_memory_ordered_pair_stilp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc2 : (BitVec 4)) (Rt2 : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let postindex : Bool := false
  let wback : Bool := ((BitVec.join1 [(BitVec.access opc2 0)]) == 0#1)
  let offset ← (( do (undefined_int ()) ) : SailM Int )
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let scale := (2 +i (BitVec.toNat (BitVec.join1 [(BitVec.access size 0)])))
  let datasize := (Int.shiftl 8 scale)
  let memop ← (( do (undefined_MemOp ()) ) : SailM MemOp )
  let (memop, offset) : (MemOp × Int) :=
    if ((L == 1#1) : Bool)
    then
      (let memop : MemOp := MemOp_LOAD
      let offset : Int :=
        if (((BitVec.join1 [(BitVec.access opc2 0)]) == 0#1) : Bool)
        then (Int.shiftl 2 scale)
        else 0
      (memop, offset))
    else
      (let memop : MemOp := MemOp_STORE
      let offset : Int :=
        if (((BitVec.join1 [(BitVec.access opc2 0)]) == 0#1) : Bool)
        then ((Neg.neg 1) *i (Int.shiftl 2 scale))
        else 0
      (memop, offset))
  let offset := offset
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:51080.113-51080.114"
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
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:51099.107-51099.108"
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
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:51118.84-51118.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((datasize == 32) || (datasize == 64)) "src/instrs64.sail:51132.44-51132.45"
  (execute_aarch64_instrs_memory_ordered_pair_stilp datasize memop n offset postindex rt_unknown t t2 tagchecked wb_unknown wback)

def decode_stz2g_aarch64_instrs_integer_tags_mcsettagpairandzerodatapost (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Xn)
  let t := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := true
  let zero_data : Bool := true
  (execute_aarch64_instrs_integer_tags_mcsettagpairandzerodatapost n offset postindex t writeback zero_data)

def decode_stz2g_aarch64_instrs_integer_tags_mcsettagpairandzerodatapre (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Xn)
  let t := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := false
  let zero_data : Bool := true
  (execute_aarch64_instrs_integer_tags_mcsettagpairandzerodatapost n offset postindex t writeback zero_data)

def decode_stz2g_aarch64_instrs_integer_tags_mcsettagpairandzerodata (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Xn)
  let t := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := false
  let postindex : Bool := false
  let zero_data : Bool := true
  (execute_aarch64_instrs_integer_tags_mcsettagpairandzerodatapost n offset postindex t writeback zero_data)

def decode_stzg_aarch64_instrs_integer_tags_mcsettagandzerodatapost (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Xn)
  let t := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := true
  let zero_data : Bool := true
  (execute_aarch64_instrs_integer_tags_mcsettagandzerodatapost n offset postindex t writeback zero_data)

def decode_stzg_aarch64_instrs_integer_tags_mcsettagandzerodatapre (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Xn)
  let t := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := true
  let postindex : Bool := false
  let zero_data : Bool := true
  (execute_aarch64_instrs_integer_tags_mcsettagandzerodatapost n offset postindex t writeback zero_data)

def decode_stzg_aarch64_instrs_integer_tags_mcsettagandzerodata (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Xn)
  let t := (BitVec.toNat Xt)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  let writeback : Bool := false
  let postindex : Bool := false
  let zero_data : Bool := true
  (execute_aarch64_instrs_integer_tags_mcsettagandzerodatapost n offset postindex t writeback zero_data)

def decode_stzgm_aarch64_instrs_integer_tags_mcsettagandzeroarray (Xt : (BitVec 5)) (Xn : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveMTE2Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Xt)
  let n := (BitVec.toNat Xn)
  (execute_aarch64_instrs_integer_tags_mcsettagandzeroarray n t)

def decode_subg_aarch64_instrs_integer_tags_mcsubtag (Xd : (BitVec 5)) (Xn : (BitVec 5)) (uimm4 : (BitVec 4)) (op3 : (BitVec 2)) (uimm6 : (BitVec 6)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Xd)
  let n := (BitVec.toNat Xn)
  let tag_offset : (BitVec 4) := uimm4
  let offset : (BitVec 64) := ((Sail.BitVec.zeroExtend uimm6 64) <<< LOG2_TAG_GRANULE)
  let ADD : Bool := false
  (execute_aarch64_instrs_integer_tags_mcsubtag ADD d n offset tag_offset)

def decode_subp_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddress (Xd : (BitVec 5)) (Xn : (BitVec 5)) (Xm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Xd)
  let n := (BitVec.toNat Xn)
  let m := (BitVec.toNat Xm)
  let setflags : Bool := false
  (execute_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddress d m n setflags)

def decode_subps_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags (Xd : (BitVec 5)) (Xn : (BitVec 5)) (Xm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Xd)
  let n := (BitVec.toNat Xn)
  let m := (BitVec.toNat Xm)
  let setflags : Bool := true
  (execute_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags d m n setflags)

def decode_sudot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (US : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveInt8MatMulExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let op1_unsigned : Bool := (US == 1#1)
  let op2_unsigned : Bool := (US == 0#1)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (M +++ Rm))
  let d := (BitVec.toNat Rd)
  let i := (BitVec.toNat (H +++ L))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize 32)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp d datasize elements i m n op1_unsigned op2_unsigned)

def decode_usdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (US : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveInt8MatMulExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let op1_unsigned : Bool := (US == 1#1)
  let op2_unsigned : Bool := (US == 0#1)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (M +++ Rm))
  let d := (BitVec.toNat Rd)
  let i := (BitVec.toNat (H +++ L))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize 32)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mat_mul_int_dotp d datasize elements i m n op1_unsigned op2_unsigned)

def decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd d datasize elements esize n is_unsigned)

def decode_suqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd d datasize elements esize n is_unsigned)

def decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd d datasize elements esize n is_unsigned)

def decode_usqadd_advsimd_aarch64_instrs_vector_arithmetic_unary_add_saturating_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_add_saturating_sisd d datasize elements esize n is_unsigned)

def decode_svc_aarch64_instrs_system_exceptions_runtime_svc (imm16 : (BitVec 16)) : SailM Unit := do
  let imm : (BitVec 16) := imm16
  (execute_aarch64_instrs_system_exceptions_runtime_svc imm)

def decode_swp_aarch64_instrs_memory_atomicops_swp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveAtomicExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let s := (BitVec.toNat Rs)
  let datasize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_swp acquire datasize n regsize release s t tagchecked)

def decode_swpb_aarch64_instrs_memory_atomicops_swp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveAtomicExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let s := (BitVec.toNat Rs)
  let datasize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_swp acquire datasize n regsize release s t tagchecked)

def decode_swph_aarch64_instrs_memory_atomicops_swp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveAtomicExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let s := (BitVec.toNat Rs)
  let datasize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_swp acquire datasize n regsize release s t tagchecked)

def decode_swpp_aarch64_instrs_memory_atomicops_swp_128 (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveLSE128 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rt == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rt2 == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let n := (BitVec.toNat Rn)
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_swp_128 acquire n release t t2 tagchecked)

def decode_sys_aarch64_instrs_system_sysops (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (L : (BitVec 1)) : SailM Unit := do
  (AArch64_CheckSystemAccess 0b01#2 op1 CRn CRm op2 Rt L)
  let t := (BitVec.toNat Rt)
  let sys_op0 := 1
  let sys_op1 := (BitVec.toNat op1)
  let sys_op2 := (BitVec.toNat op2)
  let sys_crn := (BitVec.toNat CRn)
  let sys_crm := (BitVec.toNat CRm)
  let has_result : Bool := (L == 1#1)
  (execute_aarch64_instrs_system_sysops has_result sys_crm sys_crn sys_op0 sys_op1 sys_op2 t)

def decode_sysl_aarch64_instrs_system_sysops (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (L : (BitVec 1)) : SailM Unit := do
  (AArch64_CheckSystemAccess 0b01#2 op1 CRn CRm op2 Rt L)
  let t := (BitVec.toNat Rt)
  let sys_op0 := 1
  let sys_op1 := (BitVec.toNat op1)
  let sys_op2 := (BitVec.toNat op2)
  let sys_crn := (BitVec.toNat CRn)
  let sys_crm := (BitVec.toNat CRm)
  let has_result : Bool := (L == 1#1)
  (execute_aarch64_instrs_system_sysops has_result sys_crm sys_crn sys_op0 sys_op1 sys_op2 t)

def decode_sysp_aarch64_instrs_system_sysops_128 (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (L : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveSysInstr128 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1) && (Rt != 0b11111#5)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (AArch64_CheckSystemAccess 0b01#2 op1 CRn CRm op2 Rt L)
  let t := (BitVec.toNat Rt)
  let t2 :=
    if ((t == 31) : Bool)
    then 31
    else (t +i 1)
  let sys_op0 := 1
  let sys_op1 := (BitVec.toNat op1)
  let sys_op2 := (BitVec.toNat op2)
  let sys_crn := (BitVec.toNat CRn)
  let sys_crm := (BitVec.toNat CRm)
  (execute_aarch64_instrs_system_sysops_128 sys_crm sys_crn sys_op0 sys_op1 sys_op2 t t2)

def decode_tbl_advsimd_aarch64_instrs_vector_transfer_vector_table (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (len : (BitVec 2)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize 8)
  let regs := ((BitVec.toNat len) +i 1)
  let is_tbl : Bool := (op == 0#1)
  (execute_aarch64_instrs_vector_transfer_vector_table d datasize elements is_tbl m n regs)

def decode_tbx_advsimd_aarch64_instrs_vector_transfer_vector_table (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (len : (BitVec 2)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize 8)
  let regs := ((BitVec.toNat len) +i 1)
  let is_tbl : Bool := (op == 0#1)
  (execute_aarch64_instrs_vector_transfer_vector_table d datasize elements is_tbl m n regs)

def decode_tbnz_aarch64_instrs_branch_conditional_test (Rt : (BitVec 5)) (imm14 : (BitVec 14)) (b40 : (BitVec 5)) (op : (BitVec 1)) (b5 : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let datasize :=
    if ((b5 == 1#1) : Bool)
    then 64
    else 32
  let bit_pos := (BitVec.toNat (b5 +++ b40))
  let bit_val : (BitVec 1) := op
  let offset : (BitVec 64) := (sign_extend (imm14 +++ 0b00#2) 64)
  (execute_aarch64_instrs_branch_conditional_test bit_pos bit_val datasize offset t)

def decode_tbz_aarch64_instrs_branch_conditional_test (Rt : (BitVec 5)) (imm14 : (BitVec 14)) (b40 : (BitVec 5)) (op : (BitVec 1)) (b5 : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let datasize :=
    if ((b5 == 1#1) : Bool)
    then 64
    else 32
  let bit_pos := (BitVec.toNat (b5 +++ b40))
  let bit_val : (BitVec 1) := op
  let offset : (BitVec 64) := (sign_extend (imm14 +++ 0b00#2) 64)
  (execute_aarch64_instrs_branch_conditional_test bit_pos bit_val datasize offset t)

def decode_tcancel_aarch64_instrs_system_tme_tcancel (imm16 : (BitVec 16)) : SailM Unit := do
  if ((! (← (HaveTME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let retry : Bool := ((BitVec.join1 [(BitVec.access imm16 15)]) == 1#1)
  let reason : (BitVec 15) := (Sail.BitVec.extractLsb imm16 14 0)
  (execute_aarch64_instrs_system_tme_tcancel reason retry)

def decode_tcommit_aarch64_instrs_system_tme_tcommit (_ : Unit) : SailM Unit := do
  if ((! (← (HaveTME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_system_tme_tcommit ())

def decode_trn1_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
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
  let part := (BitVec.toNat op)
  let pairs := (Int.ediv elements 2)
  (execute_aarch64_instrs_vector_transfer_vector_permute_transpose d datasize esize m n pairs part)

def decode_trn2_advsimd_aarch64_instrs_vector_transfer_vector_permute_transpose (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
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
  let part := (BitVec.toNat op)
  let pairs := (Int.ediv elements 2)
  (execute_aarch64_instrs_vector_transfer_vector_permute_transpose d datasize esize m n pairs part)

def decode_tstart_aarch64_instrs_system_tme_tstart (Rt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveTME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  match VL with
  | 128 => (execute_aarch64_instrs_system_tme_tstart 128 t)
  | 256 => (execute_aarch64_instrs_system_tme_tstart 256 t)
  | 512 => (execute_aarch64_instrs_system_tme_tstart 512 t)
  | 1024 => (execute_aarch64_instrs_system_tme_tstart 1024 t)
  | 2048 => (execute_aarch64_instrs_system_tme_tstart 2048 t)
  | _ => (pure ())

def decode_ttest_aarch64_instrs_system_tme_ttest (Rt : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveTME ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  (execute_aarch64_instrs_system_tme_ttest t)

def decode_umax_imm_aarch64_instrs_integer_arithmetic_max_min_umax_imm (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm8 : (BitVec 8)) (sf : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveCSSC ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let d := (BitVec.toNat Rd)
  let imm := (BitVec.toNat imm8)
  (execute_aarch64_instrs_integer_arithmetic_max_min_umax_imm d datasize imm n)

def decode_umax_reg_aarch64_instrs_integer_arithmetic_max_min_umax_reg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveCSSC ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  (execute_aarch64_instrs_integer_arithmetic_max_min_umax_reg d datasize m n)

def decode_umin_reg_aarch64_instrs_integer_arithmetic_max_min_umin_reg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveCSSC ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  (execute_aarch64_instrs_integer_arithmetic_max_min_umin_reg d datasize m n)

def decode_umin_imm_aarch64_instrs_integer_arithmetic_max_min_umin_imm (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm8 : (BitVec 8)) (sf : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveCSSC ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let d := (BitVec.toNat Rd)
  let imm := (BitVec.toNat imm8)
  (execute_aarch64_instrs_integer_arithmetic_max_min_umin_imm d datasize imm n)

def decode_umov_advsimd_aarch64_instrs_vector_transfer_integer_move_unsigned (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let size : Nat := 0
  let size ← (( do
    let b__0 := (Q +++ imm5)
    if ((((Sail.BitVec.extractLsb b__0 5 5) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 0 0) == (1#1 : (BitVec 1)))) : Bool)
    then (pure 0)
    else
      (do
        if ((((Sail.BitVec.extractLsb b__0 5 5) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b10#2 : (BitVec 2)))) : Bool)
        then (pure 1)
        else
          (do
            if ((((Sail.BitVec.extractLsb b__0 5 5) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 2 0) == (0b100#3 : (BitVec 3)))) : Bool)
            then (pure 2)
            else
              (do
                if ((((Sail.BitVec.extractLsb b__0 5 5) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 3 0) == (0x8#4 : (BitVec 4)))) : Bool)
                then (pure 3)
                else sailThrow ((Error_Undefined ()))))) ) : SailM Int )
  let size := size
  let idxdsize :=
    if (((BitVec.join1 [(BitVec.access imm5 4)]) == 1#1) : Bool)
    then 128
    else 64
  let index := (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 (size +i 1)))
  let esize := (Int.shiftl 8 size)
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 64
    else 32
  (execute_aarch64_instrs_vector_transfer_integer_move_unsigned d datasize esize idxdsize index n)

def decode_urecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((sz == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_unary_special_recip_int d datasize elements n)

def decode_ursqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((sz == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_int d datasize elements n)

def decode_usdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_usdot (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveInt8MatMulExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize 32)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mat_mul_int_usdot d datasize elements m n)

def decode_uzp1_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
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
  let part := (BitVec.toNat op)
  (execute_aarch64_instrs_vector_transfer_vector_permute_unzip d datasize elements esize m n part)

def decode_uzp2_advsimd_aarch64_instrs_vector_transfer_vector_permute_unzip (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
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
  let part := (BitVec.toNat op)
  (execute_aarch64_instrs_vector_transfer_vector_permute_unzip d datasize elements esize m n part)

def decode_wfet_aarch64_instrs_system_sysinstwithreg_wfet (Rd : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveFeatWFxT ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  (execute_aarch64_instrs_system_sysinstwithreg_wfet d)

def decode_wfit_aarch64_instrs_system_sysinstwithreg_wfit (Rd : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveFeatWFxT ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  (execute_aarch64_instrs_system_sysinstwithreg_wfit d)

def decode_xaflag_aarch64_instrs_integer_flags_xaflag (CRm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveFlagFormatExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_integer_flags_xaflag ())

def decode_xar_advsimd_aarch64_instrs_vector_crypto_sha3_xar (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSHA3Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  (execute_aarch64_instrs_vector_crypto_sha3_xar d imm6 m n)

def decode_xpac_aarch64_instrs_integer_pac_strip_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) : SailM Unit := do
  let data : Bool := (D == 1#1)
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((! (← (HavePACExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((n != 31) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_integer_pac_strip_dp_1src d data)

def decode_xpac_aarch64_instrs_integer_pac_strip_hint (_ : Unit) : SailM Unit := do
  let d := 30
  let data : Bool := false
  (execute_aarch64_instrs_integer_pac_strip_dp_1src d data)

def decode_xtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_nosat (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_unary_extract_nosat d datasize elements esize n part)

def decode_zip1_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
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
  let part := (BitVec.toNat op)
  let pairs := (Int.ediv elements 2)
  (execute_aarch64_instrs_vector_transfer_vector_permute_zip d datasize esize m n pairs part)

def decode_zip2_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
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
  let part := (BitVec.toNat op)
  let pairs := (Int.ediv elements 2)
  (execute_aarch64_instrs_vector_transfer_vector_permute_zip d datasize esize m n pairs part)

