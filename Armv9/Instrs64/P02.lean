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

def decode_frintx_float_aarch64_instrs_float_arithmetic_round_frint (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize : Nat := 16
  let esize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let esize := esize
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let (exact, rounding) ← (( do
    let b__0 := rmode
    let (exact, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding (Sail.BitVec.extractLsb rmode 1 0))
          (pure (exact, rounding)))
      else
        (do
          let (exact, rounding) ← (( do
            if ((b__0 == (0b100#3 : (BitVec 3))) : Bool)
            then
              (let rounding : FPRounding := FPRounding_TIEAWAY
              (pure (exact, rounding)))
            else
              (do
                let (exact, rounding) ← (( do
                  if ((b__0 == (0b101#3 : (BitVec 3))) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let (exact, rounding) ← (( do
                        if ((b__0 == (0b110#3 : (BitVec 3))) : Bool)
                        then
                          (do
                            let rounding ← (FPRoundingMode (← (FPCR_read ())))
                            let exact : Bool := true
                            (pure (exact, rounding)))
                        else
                          (do
                            let rounding ← (FPRoundingMode (← (FPCR_read ())))
                            (pure (exact, rounding))) ) : SailM (Bool × FPRounding) )
                      (pure (exact, rounding))) ) : SailM (Bool × FPRounding) )
                (pure (exact, rounding))) ) : SailM (Bool × FPRounding) )
          (pure (exact, rounding))) ) : SailM (Bool × FPRounding) )
    (pure (exact, rounding)) ) : SailM (Bool × FPRounding) )
  let rounding := rounding
  (execute_aarch64_instrs_float_arithmetic_round_frint d esize exact n rounding)

def decode_frintz_float_aarch64_instrs_float_arithmetic_round_frint (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize : Nat := 16
  let esize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let esize := esize
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let (exact, rounding) ← (( do
    let b__0 := rmode
    let (exact, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding (Sail.BitVec.extractLsb rmode 1 0))
          (pure (exact, rounding)))
      else
        (do
          let (exact, rounding) ← (( do
            if ((b__0 == (0b100#3 : (BitVec 3))) : Bool)
            then
              (let rounding : FPRounding := FPRounding_TIEAWAY
              (pure (exact, rounding)))
            else
              (do
                let (exact, rounding) ← (( do
                  if ((b__0 == (0b101#3 : (BitVec 3))) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let (exact, rounding) ← (( do
                        if ((b__0 == (0b110#3 : (BitVec 3))) : Bool)
                        then
                          (do
                            let rounding ← (FPRoundingMode (← (FPCR_read ())))
                            let exact : Bool := true
                            (pure (exact, rounding)))
                        else
                          (do
                            let rounding ← (FPRoundingMode (← (FPCR_read ())))
                            (pure (exact, rounding))) ) : SailM (Bool × FPRounding) )
                      (pure (exact, rounding))) ) : SailM (Bool × FPRounding) )
                (pure (exact, rounding))) ) : SailM (Bool × FPRounding) )
          (pure (exact, rounding))) ) : SailM (Bool × FPRounding) )
    (pure (exact, rounding)) ) : SailM (Bool × FPRounding) )
  let rounding := rounding
  (execute_aarch64_instrs_float_arithmetic_round_frint d esize exact n rounding)

def decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd d datasize elements esize n)

def decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd d datasize elements esize n)

def decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd d datasize elements esize n)

def decode_frsqrte_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_float_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd d datasize elements esize n)

def decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 16
  let datasize := esize
  let elements := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd d datasize elements esize m n)

def decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd d datasize elements esize m n)

def decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 16
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd d datasize elements esize m n)

def decode_frsqrts_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_rsqrts_fp16_sisd d datasize elements esize m n)

def decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16 d datasize elements esize n)

def decode_fsqrt_advsimd_aarch64_instrs_vector_arithmetic_unary_special_sqrt (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_fp16 d datasize elements esize n)

def decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 16
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let abs : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd abs d datasize elements esize m n)

def decode_fsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let abs : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd abs d datasize elements esize m n)

def decode_gcsstr_aarch64_instrs_memory_gcs_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) : SailM Unit := do
  if ((! (← (HaveGCS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let is_gcssttr : Bool := (opc == 0b001#3)
  (execute_aarch64_instrs_memory_gcs_general_register is_gcssttr n t)

def decode_gcssttr_aarch64_instrs_memory_gcs_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) : SailM Unit := do
  if ((! (← (HaveGCS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let is_gcssttr : Bool := (opc == 0b001#3)
  (execute_aarch64_instrs_memory_gcs_general_register is_gcssttr n t)

def decode_gmi_aarch64_instrs_integer_tags_mcinserttagmask (Xd : (BitVec 5)) (Xn : (BitVec 5)) (Xm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Xd)
  let n := (BitVec.toNat Xn)
  let m := (BitVec.toNat Xm)
  (execute_aarch64_instrs_integer_tags_mcinserttagmask d m n)

def decode_hlt_aarch64_instrs_system_exceptions_debug_halt (imm16 : (BitVec 16)) : SailM Unit := do
  if ((←((pure ((_get_EDSCR_Type_HDE (← (EDSCR_read ()))) == 0#1)) <||> (do
       (pure (! (← (HaltingAllowed ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((← (HaveBTIExt ())) : Bool)
  then (SetBTypeCompatible true)
  else (pure ())
  (execute_aarch64_instrs_system_exceptions_debug_halt ())

def decode_hvc_aarch64_instrs_system_exceptions_runtime_hvc (imm16 : (BitVec 16)) : SailM Unit := do
  let imm : (BitVec 16) := imm16
  (execute_aarch64_instrs_system_exceptions_runtime_hvc imm)

def decode_ins_advsimd_elt_aarch64_instrs_vector_transfer_vector_insert (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm4 : (BitVec 4)) (imm5 : (BitVec 5)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let size := (LowestSetBit imm5)
  if ((size >b 3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  sail_assert (0 ≤b (size +i 1)) "src/instrs64.sail:22555.37-22555.38"
  let dst_index := (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 (size +i 1)))
  sail_assert (0 ≤b size) "src/instrs64.sail:22557.33-22557.34"
  let src_index := (BitVec.toNat (Sail.BitVec.extractLsb imm4 3 size))
  let idxdsize :=
    if (((BitVec.join1 [(BitVec.access imm4 3)]) == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 size)
  match esize with
  | 8 =>
    (do
      match idxdsize with
      | 64 => (execute_aarch64_instrs_vector_transfer_vector_insert d dst_index 8 64 n src_index)
      | 128 => (execute_aarch64_instrs_vector_transfer_vector_insert d dst_index 8 128 n src_index)
      | _ => sail_assert false "src/instrs64.sail:22571.28-22571.29")
  | 16 =>
    (do
      match idxdsize with
      | 64 => (execute_aarch64_instrs_vector_transfer_vector_insert d dst_index 16 64 n src_index)
      | 128 => (execute_aarch64_instrs_vector_transfer_vector_insert d dst_index 16 128 n src_index)
      | _ => sail_assert false "src/instrs64.sail:22584.28-22584.29")
  | 32 =>
    (do
      match idxdsize with
      | 64 => (execute_aarch64_instrs_vector_transfer_vector_insert d dst_index 32 64 n src_index)
      | 128 => (execute_aarch64_instrs_vector_transfer_vector_insert d dst_index 32 128 n src_index)
      | _ => sail_assert false "src/instrs64.sail:22597.28-22597.29")
  | 64 =>
    (do
      match idxdsize with
      | 64 => (execute_aarch64_instrs_vector_transfer_vector_insert d dst_index 64 64 n src_index)
      | 128 => (execute_aarch64_instrs_vector_transfer_vector_insert d dst_index 64 128 n src_index)
      | _ => sail_assert false "src/instrs64.sail:22610.28-22610.29")
  | _ => sail_assert false "src/instrs64.sail:22641.22-22641.23"

def decode_ins_advsimd_gen_aarch64_instrs_vector_transfer_integer_insert (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let size := (LowestSetBit imm5)
  if ((size >b 3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  sail_assert (0 ≤b (size +i 1)) "src/instrs64.sail:22677.37-22677.38"
  let index := (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 (size +i 1)))
  let esize := (_shl_int_general 8 size)
  let datasize := 128
  sail_assert ((((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) || (esize == 128)) || (esize == 256)) "src/instrs64.sail:22681.58-22681.59"
  (execute_aarch64_instrs_vector_transfer_integer_insert d datasize esize index n)

def decode_irg_aarch64_instrs_integer_tags_mcinsertrandomtag (Xd : (BitVec 5)) (Xn : (BitVec 5)) (Xm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Xd)
  let n := (BitVec.toNat Xn)
  let m := (BitVec.toNat Xm)
  (execute_aarch64_instrs_integer_tags_mcinsertrandomtag d m n)

def decode_isb_aarch64_instrs_system_barriers_isb (opc : (BitVec 2)) (CRm : (BitVec 4)) : SailM Unit := do
  (execute_aarch64_instrs_system_barriers_isb ())

def decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:22879.48-22879.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_ld1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:22949.48-22949.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:23019.48-23019.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_ld1r_advsimd_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:23089.48-23089.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:23159.48-23159.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_ld2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:23229.48-23229.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:23299.48-23299.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_ld2r_advsimd_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:23369.48-23369.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:23439.48-23439.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_ld3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:23509.48-23509.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:23579.48-23579.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_ld3r_advsimd_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:23649.48-23649.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:23719.48-23719.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_ld4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:23789.48-23789.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:23859.48-23859.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_ld4r_advsimd_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:23929.48-23929.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:23999.48-23999.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_st1_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:24069.48-24069.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:24139.48-24139.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_st2_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:24209.48-24209.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:24279.48-24279.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_st3_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:24349.48-24349.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (o2 : (BitVec 1)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:24419.48-24419.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_st4_advsimd_sngl_aarch64_instrs_memory_vector_single_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (Rm : (BitVec 5)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:24489.48-24489.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb datasize esize index m memop n nontemporal replicate selem t tagchecked wback)

def decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv datasize esize)
  let rpt : Nat := 1
  let selem : Nat := 1
  let (rpt, selem) ← (( do
    match (opcode : BitVec 4) with
    | 0b0000 =>
      (let rpt : Nat := 1
      let selem : Nat := 4
      (pure (rpt, selem)))
    | 0b0010 =>
      (let rpt : Nat := 4
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0100 =>
      (let rpt : Nat := 1
      let selem : Nat := 3
      (pure (rpt, selem)))
    | 0b0110 =>
      (let rpt : Nat := 3
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0111 =>
      (let rpt : Nat := 1
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b1000 =>
      (let rpt : Nat := 1
      let selem : Nat := 2
      (pure (rpt, selem)))
    | 0b1010 =>
      (let rpt : Nat := 2
      let selem : Nat := 1
      (pure (rpt, selem)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem := selem
  let rpt := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_memory_vector_multiple_no_wb datasize elements esize m memop n nontemporal rpt selem t tagchecked wback)

def decode_ld1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv datasize esize)
  let rpt : Nat := 1
  let selem : Nat := 1
  let (rpt, selem) ← (( do
    match (opcode : BitVec 4) with
    | 0b0000 =>
      (let rpt : Nat := 1
      let selem : Nat := 4
      (pure (rpt, selem)))
    | 0b0010 =>
      (let rpt : Nat := 4
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0100 =>
      (let rpt : Nat := 1
      let selem : Nat := 3
      (pure (rpt, selem)))
    | 0b0110 =>
      (let rpt : Nat := 3
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0111 =>
      (let rpt : Nat := 1
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b1000 =>
      (let rpt : Nat := 1
      let selem : Nat := 2
      (pure (rpt, selem)))
    | 0b1010 =>
      (let rpt : Nat := 2
      let selem : Nat := 1
      (pure (rpt, selem)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem := selem
  let rpt := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_memory_vector_multiple_no_wb datasize elements esize m memop n nontemporal rpt selem t tagchecked wback)

def decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv datasize esize)
  let rpt : Nat := 1
  let selem : Nat := 1
  let (rpt, selem) ← (( do
    match (opcode : BitVec 4) with
    | 0b0000 =>
      (let rpt : Nat := 1
      let selem : Nat := 4
      (pure (rpt, selem)))
    | 0b0010 =>
      (let rpt : Nat := 4
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0100 =>
      (let rpt : Nat := 1
      let selem : Nat := 3
      (pure (rpt, selem)))
    | 0b0110 =>
      (let rpt : Nat := 3
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0111 =>
      (let rpt : Nat := 1
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b1000 =>
      (let rpt : Nat := 1
      let selem : Nat := 2
      (pure (rpt, selem)))
    | 0b1010 =>
      (let rpt : Nat := 2
      let selem : Nat := 1
      (pure (rpt, selem)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem := selem
  let rpt := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_memory_vector_multiple_no_wb datasize elements esize m memop n nontemporal rpt selem t tagchecked wback)

def decode_ld2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv datasize esize)
  let rpt : Nat := 1
  let selem : Nat := 1
  let (rpt, selem) ← (( do
    match (opcode : BitVec 4) with
    | 0b0000 =>
      (let rpt : Nat := 1
      let selem : Nat := 4
      (pure (rpt, selem)))
    | 0b0010 =>
      (let rpt : Nat := 4
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0100 =>
      (let rpt : Nat := 1
      let selem : Nat := 3
      (pure (rpt, selem)))
    | 0b0110 =>
      (let rpt : Nat := 3
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0111 =>
      (let rpt : Nat := 1
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b1000 =>
      (let rpt : Nat := 1
      let selem : Nat := 2
      (pure (rpt, selem)))
    | 0b1010 =>
      (let rpt : Nat := 2
      let selem : Nat := 1
      (pure (rpt, selem)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem := selem
  let rpt := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_memory_vector_multiple_no_wb datasize elements esize m memop n nontemporal rpt selem t tagchecked wback)

def decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv datasize esize)
  let rpt : Nat := 1
  let selem : Nat := 1
  let (rpt, selem) ← (( do
    match (opcode : BitVec 4) with
    | 0b0000 =>
      (let rpt : Nat := 1
      let selem : Nat := 4
      (pure (rpt, selem)))
    | 0b0010 =>
      (let rpt : Nat := 4
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0100 =>
      (let rpt : Nat := 1
      let selem : Nat := 3
      (pure (rpt, selem)))
    | 0b0110 =>
      (let rpt : Nat := 3
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0111 =>
      (let rpt : Nat := 1
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b1000 =>
      (let rpt : Nat := 1
      let selem : Nat := 2
      (pure (rpt, selem)))
    | 0b1010 =>
      (let rpt : Nat := 2
      let selem : Nat := 1
      (pure (rpt, selem)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem := selem
  let rpt := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_memory_vector_multiple_no_wb datasize elements esize m memop n nontemporal rpt selem t tagchecked wback)

def decode_ld3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv datasize esize)
  let rpt : Nat := 1
  let selem : Nat := 1
  let (rpt, selem) ← (( do
    match (opcode : BitVec 4) with
    | 0b0000 =>
      (let rpt : Nat := 1
      let selem : Nat := 4
      (pure (rpt, selem)))
    | 0b0010 =>
      (let rpt : Nat := 4
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0100 =>
      (let rpt : Nat := 1
      let selem : Nat := 3
      (pure (rpt, selem)))
    | 0b0110 =>
      (let rpt : Nat := 3
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0111 =>
      (let rpt : Nat := 1
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b1000 =>
      (let rpt : Nat := 1
      let selem : Nat := 2
      (pure (rpt, selem)))
    | 0b1010 =>
      (let rpt : Nat := 2
      let selem : Nat := 1
      (pure (rpt, selem)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem := selem
  let rpt := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_memory_vector_multiple_no_wb datasize elements esize m memop n nontemporal rpt selem t tagchecked wback)

def decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv datasize esize)
  let rpt : Nat := 1
  let selem : Nat := 1
  let (rpt, selem) ← (( do
    match (opcode : BitVec 4) with
    | 0b0000 =>
      (let rpt : Nat := 1
      let selem : Nat := 4
      (pure (rpt, selem)))
    | 0b0010 =>
      (let rpt : Nat := 4
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0100 =>
      (let rpt : Nat := 1
      let selem : Nat := 3
      (pure (rpt, selem)))
    | 0b0110 =>
      (let rpt : Nat := 3
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0111 =>
      (let rpt : Nat := 1
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b1000 =>
      (let rpt : Nat := 1
      let selem : Nat := 2
      (pure (rpt, selem)))
    | 0b1010 =>
      (let rpt : Nat := 2
      let selem : Nat := 1
      (pure (rpt, selem)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem := selem
  let rpt := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_memory_vector_multiple_no_wb datasize elements esize m memop n nontemporal rpt selem t tagchecked wback)

def decode_ld4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv datasize esize)
  let rpt : Nat := 1
  let selem : Nat := 1
  let (rpt, selem) ← (( do
    match (opcode : BitVec 4) with
    | 0b0000 =>
      (let rpt : Nat := 1
      let selem : Nat := 4
      (pure (rpt, selem)))
    | 0b0010 =>
      (let rpt : Nat := 4
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0100 =>
      (let rpt : Nat := 1
      let selem : Nat := 3
      (pure (rpt, selem)))
    | 0b0110 =>
      (let rpt : Nat := 3
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0111 =>
      (let rpt : Nat := 1
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b1000 =>
      (let rpt : Nat := 1
      let selem : Nat := 2
      (pure (rpt, selem)))
    | 0b1010 =>
      (let rpt : Nat := 2
      let selem : Nat := 1
      (pure (rpt, selem)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem := selem
  let rpt := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_memory_vector_multiple_no_wb datasize elements esize m memop n nontemporal rpt selem t tagchecked wback)

def decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv datasize esize)
  let rpt : Nat := 1
  let selem : Nat := 1
  let (rpt, selem) ← (( do
    match (opcode : BitVec 4) with
    | 0b0000 =>
      (let rpt : Nat := 1
      let selem : Nat := 4
      (pure (rpt, selem)))
    | 0b0010 =>
      (let rpt : Nat := 4
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0100 =>
      (let rpt : Nat := 1
      let selem : Nat := 3
      (pure (rpt, selem)))
    | 0b0110 =>
      (let rpt : Nat := 3
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0111 =>
      (let rpt : Nat := 1
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b1000 =>
      (let rpt : Nat := 1
      let selem : Nat := 2
      (pure (rpt, selem)))
    | 0b1010 =>
      (let rpt : Nat := 2
      let selem : Nat := 1
      (pure (rpt, selem)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem := selem
  let rpt := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_memory_vector_multiple_no_wb datasize elements esize m memop n nontemporal rpt selem t tagchecked wback)

def decode_st1_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv datasize esize)
  let rpt : Nat := 1
  let selem : Nat := 1
  let (rpt, selem) ← (( do
    match (opcode : BitVec 4) with
    | 0b0000 =>
      (let rpt : Nat := 1
      let selem : Nat := 4
      (pure (rpt, selem)))
    | 0b0010 =>
      (let rpt : Nat := 4
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0100 =>
      (let rpt : Nat := 1
      let selem : Nat := 3
      (pure (rpt, selem)))
    | 0b0110 =>
      (let rpt : Nat := 3
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0111 =>
      (let rpt : Nat := 1
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b1000 =>
      (let rpt : Nat := 1
      let selem : Nat := 2
      (pure (rpt, selem)))
    | 0b1010 =>
      (let rpt : Nat := 2
      let selem : Nat := 1
      (pure (rpt, selem)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem := selem
  let rpt := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_memory_vector_multiple_no_wb datasize elements esize m memop n nontemporal rpt selem t tagchecked wback)

def decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv datasize esize)
  let rpt : Nat := 1
  let selem : Nat := 1
  let (rpt, selem) ← (( do
    match (opcode : BitVec 4) with
    | 0b0000 =>
      (let rpt : Nat := 1
      let selem : Nat := 4
      (pure (rpt, selem)))
    | 0b0010 =>
      (let rpt : Nat := 4
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0100 =>
      (let rpt : Nat := 1
      let selem : Nat := 3
      (pure (rpt, selem)))
    | 0b0110 =>
      (let rpt : Nat := 3
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0111 =>
      (let rpt : Nat := 1
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b1000 =>
      (let rpt : Nat := 1
      let selem : Nat := 2
      (pure (rpt, selem)))
    | 0b1010 =>
      (let rpt : Nat := 2
      let selem : Nat := 1
      (pure (rpt, selem)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem := selem
  let rpt := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_memory_vector_multiple_no_wb datasize elements esize m memop n nontemporal rpt selem t tagchecked wback)

def decode_st2_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv datasize esize)
  let rpt : Nat := 1
  let selem : Nat := 1
  let (rpt, selem) ← (( do
    match (opcode : BitVec 4) with
    | 0b0000 =>
      (let rpt : Nat := 1
      let selem : Nat := 4
      (pure (rpt, selem)))
    | 0b0010 =>
      (let rpt : Nat := 4
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0100 =>
      (let rpt : Nat := 1
      let selem : Nat := 3
      (pure (rpt, selem)))
    | 0b0110 =>
      (let rpt : Nat := 3
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0111 =>
      (let rpt : Nat := 1
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b1000 =>
      (let rpt : Nat := 1
      let selem : Nat := 2
      (pure (rpt, selem)))
    | 0b1010 =>
      (let rpt : Nat := 2
      let selem : Nat := 1
      (pure (rpt, selem)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem := selem
  let rpt := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_memory_vector_multiple_no_wb datasize elements esize m memop n nontemporal rpt selem t tagchecked wback)

def decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv datasize esize)
  let rpt : Nat := 1
  let selem : Nat := 1
  let (rpt, selem) ← (( do
    match (opcode : BitVec 4) with
    | 0b0000 =>
      (let rpt : Nat := 1
      let selem : Nat := 4
      (pure (rpt, selem)))
    | 0b0010 =>
      (let rpt : Nat := 4
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0100 =>
      (let rpt : Nat := 1
      let selem : Nat := 3
      (pure (rpt, selem)))
    | 0b0110 =>
      (let rpt : Nat := 3
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0111 =>
      (let rpt : Nat := 1
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b1000 =>
      (let rpt : Nat := 1
      let selem : Nat := 2
      (pure (rpt, selem)))
    | 0b1010 =>
      (let rpt : Nat := 2
      let selem : Nat := 1
      (pure (rpt, selem)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem := selem
  let rpt := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_memory_vector_multiple_no_wb datasize elements esize m memop n nontemporal rpt selem t tagchecked wback)

def decode_st3_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv datasize esize)
  let rpt : Nat := 1
  let selem : Nat := 1
  let (rpt, selem) ← (( do
    match (opcode : BitVec 4) with
    | 0b0000 =>
      (let rpt : Nat := 1
      let selem : Nat := 4
      (pure (rpt, selem)))
    | 0b0010 =>
      (let rpt : Nat := 4
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0100 =>
      (let rpt : Nat := 1
      let selem : Nat := 3
      (pure (rpt, selem)))
    | 0b0110 =>
      (let rpt : Nat := 3
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0111 =>
      (let rpt : Nat := 1
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b1000 =>
      (let rpt : Nat := 1
      let selem : Nat := 2
      (pure (rpt, selem)))
    | 0b1010 =>
      (let rpt : Nat := 2
      let selem : Nat := 1
      (pure (rpt, selem)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem := selem
  let rpt := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_memory_vector_multiple_no_wb datasize elements esize m memop n nontemporal rpt selem t tagchecked wback)

def decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_no_wb (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv datasize esize)
  let rpt : Nat := 1
  let selem : Nat := 1
  let (rpt, selem) ← (( do
    match (opcode : BitVec 4) with
    | 0b0000 =>
      (let rpt : Nat := 1
      let selem : Nat := 4
      (pure (rpt, selem)))
    | 0b0010 =>
      (let rpt : Nat := 4
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0100 =>
      (let rpt : Nat := 1
      let selem : Nat := 3
      (pure (rpt, selem)))
    | 0b0110 =>
      (let rpt : Nat := 3
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0111 =>
      (let rpt : Nat := 1
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b1000 =>
      (let rpt : Nat := 1
      let selem : Nat := 2
      (pure (rpt, selem)))
    | 0b1010 =>
      (let rpt : Nat := 2
      let selem : Nat := 1
      (pure (rpt, selem)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem := selem
  let rpt := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_memory_vector_multiple_no_wb datasize elements esize m memop n nontemporal rpt selem t tagchecked wback)

def decode_st4_advsimd_mult_aarch64_instrs_memory_vector_multiple_post_inc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (opcode : (BitVec 4)) (Rm : (BitVec 5)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let wback : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv datasize esize)
  let rpt : Nat := 1
  let selem : Nat := 1
  let (rpt, selem) ← (( do
    match (opcode : BitVec 4) with
    | 0b0000 =>
      (let rpt : Nat := 1
      let selem : Nat := 4
      (pure (rpt, selem)))
    | 0b0010 =>
      (let rpt : Nat := 4
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0100 =>
      (let rpt : Nat := 1
      let selem : Nat := 3
      (pure (rpt, selem)))
    | 0b0110 =>
      (let rpt : Nat := 3
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b0111 =>
      (let rpt : Nat := 1
      let selem : Nat := 1
      (pure (rpt, selem)))
    | 0b1000 =>
      (let rpt : Nat := 1
      let selem : Nat := 2
      (pure (rpt, selem)))
    | 0b1010 =>
      (let rpt : Nat := 2
      let selem : Nat := 1
      (pure (rpt, selem)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
  let selem := selem
  let rpt := rpt
  if ((((size +++ Q) == 0b110#3) && (selem != 1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_memory_vector_multiple_no_wb datasize elements esize m memop n nontemporal rpt selem t tagchecked wback)

def decode_ld64b_aarch64_instrs_memory_atomicops_ld_acc (Rt : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveFeatLS64 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((Sail.BitVec.extractLsb Rt 4 3) == 0b11#2) || ((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let memop : MemOp := MemOp_LOAD
  let tagchecked : Bool := (n != 31)
  let lst : (BitVec 2) := lst_64b
  (execute_aarch64_instrs_memory_atomicops_ld_acc lst memop n t tagchecked)

def decode_ldadd_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldaddb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldaddh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldclr_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldclrb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldclrh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldeor_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldeorb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldeorh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldset_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldsetb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldseth_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldsmax_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldsmaxb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldsmaxh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldsmin_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldsminb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldsminh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldumax_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldumaxb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldumaxh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldumin_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_lduminb_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_lduminh_aarch64_instrs_memory_atomicops_ld (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
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
  let is_load : Bool := (Rt != 0b11111#5)
  let release : Bool := (R == 1#1)
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b000 => MemAtomicOp_ADD
    | 0b001 => MemAtomicOp_BIC
    | 0b010 => MemAtomicOp_EOR
    | 0b011 => MemAtomicOp_ORR
    | 0b100 => MemAtomicOp_SMAX
    | 0b101 => MemAtomicOp_SMIN
    | 0b110 => MemAtomicOp_UMAX
    | _ => MemAtomicOp_UMIN
  let op := op
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld acquire datasize is_load n op regsize release s t tagchecked)

def decode_ldap1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:27226.48-27226.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb_ordered datasize esize index m memop n replicate selem t tagchecked wback)

def decode_stl1_advsimd_sngl_aarch64_instrs_memory_vector_single_no_wb_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (S : (BitVec 1)) (opcode : (BitVec 3)) (R : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let m ← do (__UNKNOWN_integer ())
  let wback : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := (wback || (n != 31))
  let init_scale := (BitVec.toNat (Sail.BitVec.extractLsb opcode 2 1))
  let scale : Int := init_scale
  let selem := ((BitVec.toNat ((BitVec.join1 [(BitVec.access opcode 0)]) +++ R)) +i 1)
  let replicate : Bool := false
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (index, replicate, scale) ← (( do
    match scale with
    | 3 =>
      (do
        if (((L == 0#1) || (S == 1#1)) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let scale : Int := (BitVec.toNat size)
        let replicate : Bool := true
        (pure (index, replicate, scale)))
    | 0 =>
      (let index : Int := (BitVec.toNat ((Q +++ S) +++ size))
      (pure (index, replicate, scale)))
    | 1 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 0)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let index : Int := (BitVec.toNat ((Q +++ S) +++ (BitVec.join1 [(BitVec.access size 1)])))
        (pure (index, replicate, scale)))
    | 2 =>
      (do
        if (((BitVec.join1 [(BitVec.access size 1)]) == 1#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        let (index, scale) ← (( do
          if (((BitVec.join1 [(BitVec.access size 0)]) == 0#1) : Bool)
          then
            (let index : Int := (BitVec.toNat (Q +++ S))
            (pure (index, scale)))
          else
            (do
              if ((S == 1#1) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ())
              let index : Int := (BitVec.toNat Q)
              let scale : Int := 3
              (pure (index, scale))) ) : SailM (Int × Int) )
        (pure (index, replicate, scale)))
    | _ => (pure (index, replicate, scale)) ) : SailM (Int × Bool × Int) )
  let scale := scale
  let index := index
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 scale)
  sail_assert ((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:27295.48-27295.49"
  (execute_aarch64_instrs_memory_vector_single_no_wb_ordered datasize esize index m memop n replicate selem t tagchecked wback)

def decode_ldapr_aarch64_instrs_memory_ordered_rcpc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let offset := 0
  let wb_unknown : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let s := (BitVec.toNat Rs)
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered_rcpc datasize n offset regsize t tagchecked wb_unknown wback)

def decode_ldapr_aarch64_instrs_memory_ordered_rcpc_writeback (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let regsize :=
    if ((size == 0b11#2) : Bool)
    then 64
    else 32
  let datasize := (Int.shiftl 8 (BitVec.toNat size))
  let offset := (Int.shiftl 1 (BitVec.toNat size))
  let tagchecked : Bool := (wback || (n != 31))
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((wback && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:27393.113-27393.114"
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
  (execute_aarch64_instrs_memory_ordered_rcpc datasize n offset regsize t tagchecked wb_unknown wback)

def decode_ldaprb_aarch64_instrs_memory_ordered_rcpc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let offset := 0
  let wb_unknown : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let s := (BitVec.toNat Rs)
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered_rcpc datasize n offset regsize t tagchecked wb_unknown wback)

def decode_ldaprh_aarch64_instrs_memory_ordered_rcpc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let offset := 0
  let wb_unknown : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let s := (BitVec.toNat Rs)
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered_rcpc datasize n offset regsize t tagchecked wb_unknown wback)

def decode_ldapur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:27586.113-27586.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:27605.107-27605.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl datasize memop n offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldapurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:27671.113-27671.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:27690.107-27690.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl datasize memop n offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldapurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:27756.113-27756.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:27775.107-27775.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl datasize memop n offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldapursb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:27841.113-27841.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:27860.107-27860.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl datasize memop n offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldapursh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:27926.113-27926.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:27945.107-27945.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl datasize memop n offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldapursw_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:28011.113-28011.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:28030.107-28030.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl datasize memop n offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_stlur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:28096.113-28096.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:28115.107-28115.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl datasize memop n offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_stlurb_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:28181.113-28181.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:28200.107-28200.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl datasize memop n offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_stlurh_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:28266.113-28266.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:28285.107-28285.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_lda_stl datasize memop n offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldapur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc 1)]) +++ size))
  if ((scale >b 4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  sail_assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "src/instrs64.sail:28378.72-28378.73"
  (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered datasize memop n offset postindex t tagchecked wback)

def decode_stlur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc 1)]) +++ size))
  if ((scale >b 4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  sail_assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "src/instrs64.sail:28408.72-28408.73"
  (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_ordered datasize memop n offset postindex t tagchecked wback)

def decode_ldar_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered datasize limitedordered memop n offset regsize rt_unknown t tagchecked wback)

def decode_ldarb_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered datasize limitedordered memop n offset regsize rt_unknown t tagchecked wback)

def decode_ldarh_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered datasize limitedordered memop n offset regsize rt_unknown t tagchecked wback)

def decode_ldlar_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered datasize limitedordered memop n offset regsize rt_unknown t tagchecked wback)

def decode_ldlarb_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered datasize limitedordered memop n offset regsize rt_unknown t tagchecked wback)

def decode_ldlarh_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered datasize limitedordered memop n offset regsize rt_unknown t tagchecked wback)

def decode_stllr_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered datasize limitedordered memop n offset regsize rt_unknown t tagchecked wback)

def decode_stllrb_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered datasize limitedordered memop n offset regsize rt_unknown t tagchecked wback)

def decode_stllrh_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered datasize limitedordered memop n offset regsize rt_unknown t tagchecked wback)

def decode_stlr_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered datasize limitedordered memop n offset regsize rt_unknown t tagchecked wback)

def decode_stlr_aarch64_instrs_memory_ordered_writeback (Rt : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let memop : MemOp := MemOp_STORE
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let limitedordered : Bool := false
  let regsize :=
    if ((size == 0b11#2) : Bool)
    then 64
    else 32
  let datasize := (Int.shiftl 8 (BitVec.toNat size))
  let offset := ((Neg.neg 1) *i (Int.shiftl 1 (BitVec.toNat size)))
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let rt_unknown ← (( do
    if (((wback && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:28844.107-28844.108"
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
  (execute_aarch64_instrs_memory_ordered datasize limitedordered memop n offset regsize rt_unknown t tagchecked wback)

def decode_stlrb_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered datasize limitedordered memop n offset regsize rt_unknown t tagchecked wback)

def decode_stlrh_aarch64_instrs_memory_ordered (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let wback : Bool := false
  let offset := 0
  let rt_unknown : Bool := false
  let limitedordered : Bool := (o0 == 0#1)
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize := elsize
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_ordered datasize limitedordered memop n offset regsize rt_unknown t tagchecked wback)

def decode_ldaxp_aarch64_instrs_memory_exclusive_pair (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := true
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 32 (BitVec.toNat sz))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29042.84-29042.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29059.88-29059.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rt_unknown))
              | _ => (pure rt_unknown))
          else (pure rt_unknown) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29075.88-29075.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rn_unknown))
              | _ => (pure rn_unknown))
          else (pure rn_unknown) ) : SailM Bool )
        (pure (rn_unknown, rt_unknown)))
    else (pure (rn_unknown, rt_unknown)) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_pair acqrel datasize elsize memop n pair regsize rn_unknown rt_unknown s t t2 tagchecked)

def decode_ldxp_aarch64_instrs_memory_exclusive_pair (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := true
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 32 (BitVec.toNat sz))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29128.84-29128.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29145.88-29145.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rt_unknown))
              | _ => (pure rt_unknown))
          else (pure rt_unknown) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29161.88-29161.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rn_unknown))
              | _ => (pure rn_unknown))
          else (pure rn_unknown) ) : SailM Bool )
        (pure (rn_unknown, rt_unknown)))
    else (pure (rn_unknown, rt_unknown)) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_pair acqrel datasize elsize memop n pair regsize rn_unknown rt_unknown s t t2 tagchecked)

def decode_stlxp_aarch64_instrs_memory_exclusive_pair (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := true
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 32 (BitVec.toNat sz))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29214.84-29214.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29231.88-29231.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rt_unknown))
              | _ => (pure rt_unknown))
          else (pure rt_unknown) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29247.88-29247.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rn_unknown))
              | _ => (pure rn_unknown))
          else (pure rn_unknown) ) : SailM Bool )
        (pure (rn_unknown, rt_unknown)))
    else (pure (rn_unknown, rt_unknown)) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_pair acqrel datasize elsize memop n pair regsize rn_unknown rt_unknown s t t2 tagchecked)

def decode_stxp_aarch64_instrs_memory_exclusive_pair (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := true
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 32 (BitVec.toNat sz))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29296.84-29296.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29313.88-29313.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rt_unknown))
              | _ => (pure rt_unknown))
          else (pure rt_unknown) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29329.88-29329.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rn_unknown))
              | _ => (pure rn_unknown))
          else (pure rn_unknown) ) : SailM Bool )
        (pure (rn_unknown, rt_unknown)))
    else (pure (rn_unknown, rt_unknown)) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_pair acqrel datasize elsize memop n pair regsize rn_unknown rt_unknown s t t2 tagchecked)

def decode_ldaxr_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29462.84-29462.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29479.88-29479.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rt_unknown))
              | _ => (pure rt_unknown))
          else (pure rt_unknown) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29495.88-29495.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rn_unknown))
              | _ => (pure rn_unknown))
          else (pure rn_unknown) ) : SailM Bool )
        (pure (rn_unknown, rt_unknown)))
    else (pure (rn_unknown, rt_unknown)) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel datasize elsize memop n pair regsize rn_unknown rt_unknown s t t2 tagchecked)

def decode_ldaxrb_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29548.84-29548.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29565.88-29565.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rt_unknown))
              | _ => (pure rt_unknown))
          else (pure rt_unknown) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29581.88-29581.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rn_unknown))
              | _ => (pure rn_unknown))
          else (pure rn_unknown) ) : SailM Bool )
        (pure (rn_unknown, rt_unknown)))
    else (pure (rn_unknown, rt_unknown)) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel datasize elsize memop n pair regsize rn_unknown rt_unknown s t t2 tagchecked)

def decode_ldaxrh_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29634.84-29634.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29651.88-29651.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rt_unknown))
              | _ => (pure rt_unknown))
          else (pure rt_unknown) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29667.88-29667.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rn_unknown))
              | _ => (pure rn_unknown))
          else (pure rn_unknown) ) : SailM Bool )
        (pure (rn_unknown, rt_unknown)))
    else (pure (rn_unknown, rt_unknown)) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel datasize elsize memop n pair regsize rn_unknown rt_unknown s t t2 tagchecked)

def decode_ldxr_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29720.84-29720.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29737.88-29737.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rt_unknown))
              | _ => (pure rt_unknown))
          else (pure rt_unknown) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29753.88-29753.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rn_unknown))
              | _ => (pure rn_unknown))
          else (pure rn_unknown) ) : SailM Bool )
        (pure (rn_unknown, rt_unknown)))
    else (pure (rn_unknown, rt_unknown)) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel datasize elsize memop n pair regsize rn_unknown rt_unknown s t t2 tagchecked)

def decode_ldxrb_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29806.84-29806.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29823.88-29823.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rt_unknown))
              | _ => (pure rt_unknown))
          else (pure rt_unknown) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29839.88-29839.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rn_unknown))
              | _ => (pure rn_unknown))
          else (pure rn_unknown) ) : SailM Bool )
        (pure (rn_unknown, rt_unknown)))
    else (pure (rn_unknown, rt_unknown)) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel datasize elsize memop n pair regsize rn_unknown rt_unknown s t t2 tagchecked)

def decode_ldxrh_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29892.84-29892.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29909.88-29909.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rt_unknown))
              | _ => (pure rt_unknown))
          else (pure rt_unknown) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29925.88-29925.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rn_unknown))
              | _ => (pure rn_unknown))
          else (pure rn_unknown) ) : SailM Bool )
        (pure (rn_unknown, rt_unknown)))
    else (pure (rn_unknown, rt_unknown)) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel datasize elsize memop n pair regsize rn_unknown rt_unknown s t t2 tagchecked)

def decode_stlxr_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29978.84-29978.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:29995.88-29995.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rt_unknown))
              | _ => (pure rt_unknown))
          else (pure rt_unknown) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30011.88-30011.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rn_unknown))
              | _ => (pure rn_unknown))
          else (pure rn_unknown) ) : SailM Bool )
        (pure (rn_unknown, rt_unknown)))
    else (pure (rn_unknown, rt_unknown)) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel datasize elsize memop n pair regsize rn_unknown rt_unknown s t t2 tagchecked)

def decode_stlxrb_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30064.84-30064.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30081.88-30081.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rt_unknown))
              | _ => (pure rt_unknown))
          else (pure rt_unknown) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30097.88-30097.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rn_unknown))
              | _ => (pure rn_unknown))
          else (pure rn_unknown) ) : SailM Bool )
        (pure (rn_unknown, rt_unknown)))
    else (pure (rn_unknown, rt_unknown)) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel datasize elsize memop n pair regsize rn_unknown rt_unknown s t t2 tagchecked)

def decode_stlxrh_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30150.84-30150.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30167.88-30167.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rt_unknown))
              | _ => (pure rt_unknown))
          else (pure rt_unknown) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30183.88-30183.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rn_unknown))
              | _ => (pure rn_unknown))
          else (pure rn_unknown) ) : SailM Bool )
        (pure (rn_unknown, rt_unknown)))
    else (pure (rn_unknown, rt_unknown)) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel datasize elsize memop n pair regsize rn_unknown rt_unknown s t t2 tagchecked)

def decode_stxr_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30236.84-30236.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30253.88-30253.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rt_unknown))
              | _ => (pure rt_unknown))
          else (pure rt_unknown) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30269.88-30269.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rn_unknown))
              | _ => (pure rn_unknown))
          else (pure rn_unknown) ) : SailM Bool )
        (pure (rn_unknown, rt_unknown)))
    else (pure (rn_unknown, rt_unknown)) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel datasize elsize memop n pair regsize rn_unknown rt_unknown s t t2 tagchecked)

def decode_stxrb_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30322.84-30322.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30339.88-30339.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rt_unknown))
              | _ => (pure rt_unknown))
          else (pure rt_unknown) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30355.88-30355.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rn_unknown))
              | _ => (pure rn_unknown))
          else (pure rn_unknown) ) : SailM Bool )
        (pure (rn_unknown, rt_unknown)))
    else (pure (rn_unknown, rt_unknown)) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel datasize elsize memop n pair regsize rn_unknown rt_unknown s t t2 tagchecked)

def decode_stxrh_aarch64_instrs_memory_exclusive_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let s := (BitVec.toNat Rs)
  let acqrel : Bool := (o0 == 1#1)
  let pair : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let elsize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((elsize == 64) : Bool)
    then 64
    else 32
  let datasize :=
    if (pair : Bool)
    then (elsize *i 2)
    else elsize
  let tagchecked : Bool := (n != 31)
  let rt_unknown : Bool := false
  let rn_unknown : Bool := false
  let rt_unknown ← (( do
    if ((((BEq.beq memop MemOp_LOAD) && pair) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30408.84-30408.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  let (rn_unknown, rt_unknown) ← (( do
    if ((BEq.beq memop MemOp_STORE) : Bool)
    then
      (do
        let rt_unknown ← (( do
          if (((s == t) || (pair && (s == t2))) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_DATAOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30425.88-30425.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rt_unknown))
              | _ => (pure rt_unknown))
          else (pure rt_unknown) ) : SailM Bool )
        let rn_unknown ← (( do
          if (((s == n) && (n != 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_BASEOVERLAP) ) : SailM Constraint )
              sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30441.88-30441.89"
              match c with
              | .Constraint_UNKNOWN => (pure true)
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ())
                  (pure rn_unknown))
              | _ => (pure rn_unknown))
          else (pure rn_unknown) ) : SailM Bool )
        (pure (rn_unknown, rt_unknown)))
    else (pure (rn_unknown, rt_unknown)) ) : SailM (Bool × Bool) )
  (execute_aarch64_instrs_memory_exclusive_single acqrel datasize elsize memop n pair regsize rn_unknown rt_unknown s t t2 tagchecked)

def decode_ldclrp_aarch64_instrs_memory_atomicops_ld_128_ldclrp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
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
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b001 => MemAtomicOp_BIC
    | 0b011 => MemAtomicOp_ORR
    | _ => op
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld_128_ldclrp acquire n op release t t2 tagchecked)

def decode_ldg_aarch64_instrs_integer_tags_mcgettag (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Xt)
  let n := (BitVec.toNat Xn)
  let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
  (execute_aarch64_instrs_integer_tags_mcgettag n offset t)

def decode_ldgm_aarch64_instrs_integer_tags_mcgettagarray (Xt : (BitVec 5)) (Xn : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveMTE2Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Xt)
  let n := (BitVec.toNat Xn)
  (execute_aarch64_instrs_integer_tags_mcgettagarray n t)

def decode_ldiapp_aarch64_instrs_memory_ordered_pair_ldiapp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc2 : (BitVec 4)) (Rt2 : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let postindex : Bool := ((BitVec.join1 [(BitVec.access opc2 0)]) == 0#1)
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:30759.113-30759.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:30778.107-30778.108"
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
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30797.84-30797.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((datasize == 32) || (datasize == 64)) "src/instrs64.sail:30811.44-30811.45"
  (execute_aarch64_instrs_memory_ordered_pair_ldiapp datasize memop n offset postindex rt_unknown t t2 tagchecked wb_unknown wback)

def decode_ldnp_gen_aarch64_instrs_memory_pair_general_no_alloc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := true
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let scale := (2 +i (BitVec.toNat (BitVec.join1 [(BitVec.access opc 1)])))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30921.84-30921.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((datasize == 32) || (datasize == 64)) "src/instrs64.sail:30935.44-30935.45"
  (execute_aarch64_instrs_memory_pair_general_no_alloc datasize memop n nontemporal offset postindex rt_unknown t t2 tagchecked wback)

def decode_stnp_gen_aarch64_instrs_memory_pair_general_no_alloc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := true
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let scale := (2 +i (BitVec.toNat (BitVec.join1 [(BitVec.access opc 1)])))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:30970.84-30970.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((datasize == 32) || (datasize == 64)) "src/instrs64.sail:30984.44-30984.45"
  (execute_aarch64_instrs_memory_pair_general_no_alloc datasize memop n nontemporal offset postindex rt_unknown t t2 tagchecked wback)

def decode_ldnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := true
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((opc == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let scale := (2 +i (BitVec.toNat opc))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:31076.84-31076.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((((datasize == 32) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) "src/instrs64.sail:31090.54-31090.55"
  (execute_aarch64_instrs_memory_pair_simdfp_no_alloc datasize memop n nontemporal offset postindex rt_unknown t t2 tagchecked wback)

def decode_stnp_fpsimd_aarch64_instrs_memory_pair_simdfp_no_alloc (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := true
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((opc == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let scale := (2 +i (BitVec.toNat opc))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:31125.84-31125.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((((datasize == 32) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) "src/instrs64.sail:31139.54-31139.55"
  (execute_aarch64_instrs_memory_pair_simdfp_no_alloc datasize memop n nontemporal offset postindex rt_unknown t t2 tagchecked wback)

def decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := true
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((opc == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let scale := (2 +i (BitVec.toNat opc))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:31231.84-31231.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((((datasize == 32) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) "src/instrs64.sail:31245.54-31245.55"
  (execute_aarch64_instrs_memory_pair_simdfp_post_idx datasize memop n nontemporal offset postindex rt_unknown t t2 tagchecked wback)

def decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((opc == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let scale := (2 +i (BitVec.toNat opc))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:31280.84-31280.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((((datasize == 32) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) "src/instrs64.sail:31294.54-31294.55"
  (execute_aarch64_instrs_memory_pair_simdfp_post_idx datasize memop n nontemporal offset postindex rt_unknown t t2 tagchecked wback)

def decode_ldp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((opc == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let scale := (2 +i (BitVec.toNat opc))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:31329.84-31329.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((((datasize == 32) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) "src/instrs64.sail:31343.54-31343.55"
  (execute_aarch64_instrs_memory_pair_simdfp_post_idx datasize memop n nontemporal offset postindex rt_unknown t t2 tagchecked wback)

def decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := true
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((opc == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let scale := (2 +i (BitVec.toNat opc))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:31378.84-31378.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((((datasize == 32) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) "src/instrs64.sail:31392.54-31392.55"
  (execute_aarch64_instrs_memory_pair_simdfp_post_idx datasize memop n nontemporal offset postindex rt_unknown t t2 tagchecked wback)

def decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((opc == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let scale := (2 +i (BitVec.toNat opc))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:31427.84-31427.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((((datasize == 32) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) "src/instrs64.sail:31441.54-31441.55"
  (execute_aarch64_instrs_memory_pair_simdfp_post_idx datasize memop n nontemporal offset postindex rt_unknown t t2 tagchecked wback)

def decode_stp_fpsimd_aarch64_instrs_memory_pair_simdfp_offset (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((opc == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let scale := (2 +i (BitVec.toNat opc))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:31476.84-31476.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((((datasize == 32) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) "src/instrs64.sail:31490.54-31490.55"
  (execute_aarch64_instrs_memory_pair_simdfp_post_idx datasize memop n nontemporal offset postindex rt_unknown t t2 tagchecked wback)

def decode_ldp_gen_aarch64_instrs_memory_pair_general_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := true
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((((L +++ (BitVec.join1 [(BitVec.access opc 0)])) == 0b01#2) || (opc == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := ((BitVec.join1 [(BitVec.access opc 0)]) != 0#1)
  let scale := (2 +i (BitVec.toNat (BitVec.join1 [(BitVec.access opc 1)])))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:31620.113-31620.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:31639.107-31639.108"
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
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:31658.84-31658.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((datasize == 32) || (datasize == 64)) "src/instrs64.sail:31672.44-31672.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx datasize memop n nontemporal offset postindex rt_unknown is_signed t t2 tagchecked wb_unknown wback)

def decode_ldp_gen_aarch64_instrs_memory_pair_general_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((((L +++ (BitVec.join1 [(BitVec.access opc 0)])) == 0b01#2) || (opc == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := ((BitVec.join1 [(BitVec.access opc 0)]) != 0#1)
  let scale := (2 +i (BitVec.toNat (BitVec.join1 [(BitVec.access opc 1)])))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:31709.113-31709.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:31728.107-31728.108"
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
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:31747.84-31747.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((datasize == 32) || (datasize == 64)) "src/instrs64.sail:31761.44-31761.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx datasize memop n nontemporal offset postindex rt_unknown is_signed t t2 tagchecked wb_unknown wback)

def decode_ldp_gen_aarch64_instrs_memory_pair_general_offset (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((((L +++ (BitVec.join1 [(BitVec.access opc 0)])) == 0b01#2) || (opc == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := ((BitVec.join1 [(BitVec.access opc 0)]) != 0#1)
  let scale := (2 +i (BitVec.toNat (BitVec.join1 [(BitVec.access opc 1)])))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:31798.113-31798.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:31817.107-31817.108"
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
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:31836.84-31836.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((datasize == 32) || (datasize == 64)) "src/instrs64.sail:31850.44-31850.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx datasize memop n nontemporal offset postindex rt_unknown is_signed t t2 tagchecked wb_unknown wback)

def decode_ldpsw_aarch64_instrs_memory_pair_general_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := true
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((((L +++ (BitVec.join1 [(BitVec.access opc 0)])) == 0b01#2) || (opc == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := ((BitVec.join1 [(BitVec.access opc 0)]) != 0#1)
  let scale := (2 +i (BitVec.toNat (BitVec.join1 [(BitVec.access opc 1)])))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:31887.113-31887.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:31906.107-31906.108"
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
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:31925.84-31925.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((datasize == 32) || (datasize == 64)) "src/instrs64.sail:31939.44-31939.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx datasize memop n nontemporal offset postindex rt_unknown is_signed t t2 tagchecked wb_unknown wback)

def decode_ldpsw_aarch64_instrs_memory_pair_general_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((((L +++ (BitVec.join1 [(BitVec.access opc 0)])) == 0b01#2) || (opc == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := ((BitVec.join1 [(BitVec.access opc 0)]) != 0#1)
  let scale := (2 +i (BitVec.toNat (BitVec.join1 [(BitVec.access opc 1)])))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:31976.113-31976.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:31995.107-31995.108"
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
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:32014.84-32014.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((datasize == 32) || (datasize == 64)) "src/instrs64.sail:32028.44-32028.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx datasize memop n nontemporal offset postindex rt_unknown is_signed t t2 tagchecked wb_unknown wback)

def decode_ldpsw_aarch64_instrs_memory_pair_general_offset (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((((L +++ (BitVec.join1 [(BitVec.access opc 0)])) == 0b01#2) || (opc == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := ((BitVec.join1 [(BitVec.access opc 0)]) != 0#1)
  let scale := (2 +i (BitVec.toNat (BitVec.join1 [(BitVec.access opc 1)])))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:32065.113-32065.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:32084.107-32084.108"
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
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:32103.84-32103.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((datasize == 32) || (datasize == 64)) "src/instrs64.sail:32117.44-32117.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx datasize memop n nontemporal offset postindex rt_unknown is_signed t t2 tagchecked wb_unknown wback)

def decode_stp_gen_aarch64_instrs_memory_pair_general_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := true
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((((L +++ (BitVec.join1 [(BitVec.access opc 0)])) == 0b01#2) || (opc == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := ((BitVec.join1 [(BitVec.access opc 0)]) != 0#1)
  let scale := (2 +i (BitVec.toNat (BitVec.join1 [(BitVec.access opc 1)])))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:32154.113-32154.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:32173.107-32173.108"
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
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:32192.84-32192.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((datasize == 32) || (datasize == 64)) "src/instrs64.sail:32206.44-32206.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx datasize memop n nontemporal offset postindex rt_unknown is_signed t t2 tagchecked wb_unknown wback)

def decode_stp_gen_aarch64_instrs_memory_pair_general_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((((L +++ (BitVec.join1 [(BitVec.access opc 0)])) == 0b01#2) || (opc == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := ((BitVec.join1 [(BitVec.access opc 0)]) != 0#1)
  let scale := (2 +i (BitVec.toNat (BitVec.join1 [(BitVec.access opc 1)])))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:32243.113-32243.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:32262.107-32262.108"
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
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:32281.84-32281.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((datasize == 32) || (datasize == 64)) "src/instrs64.sail:32295.44-32295.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx datasize memop n nontemporal offset postindex rt_unknown is_signed t t2 tagchecked wb_unknown wback)

def decode_stp_gen_aarch64_instrs_memory_pair_general_offset (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (imm7 : (BitVec 7)) (L : (BitVec 1)) (opc : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat Rt2)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if ((L == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  if ((((L +++ (BitVec.join1 [(BitVec.access opc 0)])) == 0b01#2) || (opc == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := ((BitVec.join1 [(BitVec.access opc 0)]) != 0#1)
  let scale := (2 +i (BitVec.toNat (BitVec.join1 [(BitVec.access opc 1)])))
  let datasize := (Int.shiftl 8 scale)
  let offset : (BitVec 64) := ((sign_extend imm7 64) <<< scale)
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:32332.113-32332.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:32351.107-32351.108"
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
        sail_assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP))) "src/instrs64.sail:32370.84-32370.85"
        match c with
        | .Constraint_UNKNOWN => (pure true)
        | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
        | .Constraint_NOP =>
          (do
            (EndOfInstruction ())
            (pure rt_unknown))
        | _ => (pure rt_unknown))
    else (pure rt_unknown) ) : SailM Bool )
  sail_assert ((datasize == 32) || (datasize == 64)) "src/instrs64.sail:32384.44-32384.45"
  (execute_aarch64_instrs_memory_pair_general_post_idx datasize memop n nontemporal offset postindex rt_unknown is_signed t t2 tagchecked wb_unknown wback)

def decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := true
  let scale := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc 1)]) +++ size))
  if ((scale >b 4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  sail_assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "src/instrs64.sail:32462.72-32462.73"
  (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx datasize memop n nontemporal offset postindex t tagchecked wback)

def decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := false
  let scale := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc 1)]) +++ size))
  if ((scale >b 4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  sail_assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "src/instrs64.sail:32492.72-32492.73"
  (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx datasize memop n nontemporal offset postindex t tagchecked wback)

def decode_ldr_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc 1)]) +++ size))
  if ((scale >b 4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let offset : (BitVec 64) := ((Sail.BitVec.zeroExtend imm12 64) <<< scale)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  sail_assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "src/instrs64.sail:32522.72-32522.73"
  (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx datasize memop n nontemporal offset postindex t tagchecked wback)

def decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := true
  let scale := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc 1)]) +++ size))
  if ((scale >b 4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  sail_assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "src/instrs64.sail:32552.72-32552.73"
  (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx datasize memop n nontemporal offset postindex t tagchecked wback)

def decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_pre_idx (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := true
  let postindex : Bool := false
  let scale := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc 1)]) +++ size))
  if ((scale >b 4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  sail_assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "src/instrs64.sail:32582.72-32582.73"
  (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx datasize memop n nontemporal offset postindex t tagchecked wback)

def decode_str_imm_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_unsigned (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc 1)]) +++ size))
  if ((scale >b 4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let offset : (BitVec 64) := ((Sail.BitVec.zeroExtend imm12 64) <<< scale)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  sail_assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "src/instrs64.sail:32612.72-32612.73"
  (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_post_idx datasize memop n nontemporal offset postindex t tagchecked wback)

def decode_ldr_lit_gen_aarch64_instrs_memory_literal_general (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (opc : (BitVec 2)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let memop : MemOp := MemOp_LOAD
  let is_signed : Bool := false
  let nontemporal : Bool := false
  let size : Nat := 4
  let (is_signed, memop, size) : (Bool × MemOp × Int) :=
    match (opc : BitVec 2) with
    | 0b00 =>
      (let size : Nat := 4
      (is_signed, memop, size))
    | 0b01 =>
      (let size : Nat := 8
      (is_signed, memop, size))
    | 0b10 =>
      (let size : Nat := 4
      let is_signed : Bool := true
      (is_signed, memop, size))
    | _ =>
      (let memop : MemOp := MemOp_PREFETCH
      (is_signed, memop, size))
  let size := size
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  let tagchecked : Bool := false
  (execute_aarch64_instrs_memory_literal_general memop nontemporal offset is_signed size t tagchecked)

def decode_ldrsw_lit_aarch64_instrs_memory_literal_general (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (opc : (BitVec 2)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let memop : MemOp := MemOp_LOAD
  let is_signed : Bool := false
  let nontemporal : Bool := false
  let size : Nat := 4
  let (is_signed, memop, size) : (Bool × MemOp × Int) :=
    match (opc : BitVec 2) with
    | 0b00 =>
      (let size : Nat := 4
      (is_signed, memop, size))
    | 0b01 =>
      (let size : Nat := 8
      (is_signed, memop, size))
    | 0b10 =>
      (let size : Nat := 4
      let is_signed : Bool := true
      (is_signed, memop, size))
    | _ =>
      (let memop : MemOp := MemOp_PREFETCH
      (is_signed, memop, size))
  let size := size
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  let tagchecked : Bool := false
  (execute_aarch64_instrs_memory_literal_general memop nontemporal offset is_signed size t tagchecked)

def decode_prfm_lit_aarch64_instrs_memory_literal_general (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (opc : (BitVec 2)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let memop : MemOp := MemOp_LOAD
  let is_signed : Bool := false
  let nontemporal : Bool := false
  let size : Nat := 4
  let (is_signed, memop, size) : (Bool × MemOp × Int) :=
    match (opc : BitVec 2) with
    | 0b00 =>
      (let size : Nat := 4
      (is_signed, memop, size))
    | 0b01 =>
      (let size : Nat := 8
      (is_signed, memop, size))
    | 0b10 =>
      (let size : Nat := 4
      let is_signed : Bool := true
      (is_signed, memop, size))
    | _ =>
      (let memop : MemOp := MemOp_PREFETCH
      (is_signed, memop, size))
  let size := size
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  let tagchecked : Bool := false
  (execute_aarch64_instrs_memory_literal_general memop nontemporal offset is_signed size t tagchecked)

def decode_ldr_lit_fpsimd_aarch64_instrs_memory_literal_simdfp (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (opc : (BitVec 2)) : SailM Unit := do
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let size : Nat := 4
  let size ← (( do
    match (opc : BitVec 2) with
    | 0b00 => (pure 4)
    | 0b01 => (pure 8)
    | 0b10 => (pure 16)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM Int )
  let size := size
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  let tagchecked : Bool := false
  (execute_aarch64_instrs_memory_literal_simdfp nontemporal offset size t tagchecked)

def decode_ldr_reg_gen_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  if (((BitVec.join1 [(BitVec.access option_name 1)]) == 0#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let m := (BitVec.toNat Rm)
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
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35320.113-35320.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35339.107-35339.108"
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
  (execute_aarch64_instrs_memory_single_general_register datasize extend_type m memop n nontemporal postindex regsize rt_unknown shift is_signed t tagchecked wb_unknown wback)

def decode_ldrb_reg_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  if (((BitVec.join1 [(BitVec.access option_name 1)]) == 0#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let m := (BitVec.toNat Rm)
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
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35417.113-35417.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35436.107-35436.108"
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
  (execute_aarch64_instrs_memory_single_general_register datasize extend_type m memop n nontemporal postindex regsize rt_unknown shift is_signed t tagchecked wb_unknown wback)

def decode_ldrh_reg_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  if (((BitVec.join1 [(BitVec.access option_name 1)]) == 0#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let m := (BitVec.toNat Rm)
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
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35514.113-35514.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35533.107-35533.108"
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
  (execute_aarch64_instrs_memory_single_general_register datasize extend_type m memop n nontemporal postindex regsize rt_unknown shift is_signed t tagchecked wb_unknown wback)

def decode_ldrsb_reg_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  if (((BitVec.join1 [(BitVec.access option_name 1)]) == 0#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let m := (BitVec.toNat Rm)
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
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35611.113-35611.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35630.107-35630.108"
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
  (execute_aarch64_instrs_memory_single_general_register datasize extend_type m memop n nontemporal postindex regsize rt_unknown shift is_signed t tagchecked wb_unknown wback)

def decode_ldrsh_reg_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  if (((BitVec.join1 [(BitVec.access option_name 1)]) == 0#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let m := (BitVec.toNat Rm)
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
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35708.113-35708.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35727.107-35727.108"
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
  (execute_aarch64_instrs_memory_single_general_register datasize extend_type m memop n nontemporal postindex regsize rt_unknown shift is_signed t tagchecked wb_unknown wback)

def decode_ldrsw_reg_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  if (((BitVec.join1 [(BitVec.access option_name 1)]) == 0#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let m := (BitVec.toNat Rm)
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
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35805.113-35805.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35824.107-35824.108"
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
  (execute_aarch64_instrs_memory_single_general_register datasize extend_type m memop n nontemporal postindex regsize rt_unknown shift is_signed t tagchecked wb_unknown wback)

def decode_prfm_reg_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  sail_assert (! (let b__0 := Rt
    if (((Sail.BitVec.extractLsb b__0 4 3) == (0b11#2 : (BitVec 2))) : Bool)
    then true
    else false : Bool)) "src/instrs64.sail:35862.14-35862.15"
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  if (((BitVec.join1 [(BitVec.access option_name 1)]) == 0#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let m := (BitVec.toNat Rm)
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
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35906.113-35906.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:35925.107-35925.108"
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
  (execute_aarch64_instrs_memory_single_general_register datasize extend_type m memop n nontemporal postindex regsize rt_unknown shift is_signed t tagchecked wb_unknown wback)

def decode_str_reg_gen_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  if (((BitVec.join1 [(BitVec.access option_name 1)]) == 0#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let m := (BitVec.toNat Rm)
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
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:36006.113-36006.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:36025.107-36025.108"
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
  (execute_aarch64_instrs_memory_single_general_register datasize extend_type m memop n nontemporal postindex regsize rt_unknown shift is_signed t tagchecked wb_unknown wback)

def decode_strb_reg_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  if (((BitVec.join1 [(BitVec.access option_name 1)]) == 0#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let m := (BitVec.toNat Rm)
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
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:36103.113-36103.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:36122.107-36122.108"
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
  (execute_aarch64_instrs_memory_single_general_register datasize extend_type m memop n nontemporal postindex regsize rt_unknown shift is_signed t tagchecked wb_unknown wback)

def decode_strh_reg_aarch64_instrs_memory_single_general_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat size)
  if (((BitVec.join1 [(BitVec.access option_name 1)]) == 0#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let m := (BitVec.toNat Rm)
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
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  let wb_unknown : Bool := false
  let rt_unknown : Bool := false
  let c ← (( do (undefined_Constraint ()) ) : SailM Constraint )
  let (c, wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && (n == t)) && (n != 31)) : Bool)
    then
      (do
        let c ← (ConstrainUnpredictable Unpredictable_WBOVERLAPLD)
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:36200.113-36200.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:36219.107-36219.108"
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
  (execute_aarch64_instrs_memory_single_general_register datasize extend_type m memop n nontemporal postindex regsize rt_unknown shift is_signed t tagchecked wb_unknown wback)

def decode_ldr_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc 1)]) +++ size))
  if ((scale >b 4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access option_name 1)]) == 0#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let m := (BitVec.toNat Rm)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  sail_assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "src/instrs64.sail:36320.72-36320.73"
  (execute_aarch64_instrs_memory_single_simdfp_register datasize extend_type m memop n nontemporal postindex shift t tagchecked wback)

def decode_str_reg_fpsimd_aarch64_instrs_memory_single_simdfp_register (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc 1)]) +++ size))
  if ((scale >b 4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access option_name 1)]) == 0#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift :=
    if ((S == 1#1) : Bool)
    then scale
    else 0
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let m := (BitVec.toNat Rm)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := (bne memop MemOp_PREFETCH)
  sail_assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "src/instrs64.sail:36357.72-36357.73"
  (execute_aarch64_instrs_memory_single_simdfp_register datasize extend_type m memop n nontemporal postindex shift t tagchecked wback)

def decode_ldra_aarch64_instrs_memory_single_general_immediate_signed_pac (Rt : (BitVec 5)) (Rn : (BitVec 5)) (W : (BitVec 1)) (imm9 : (BitVec 9)) (S : (BitVec 1)) (M : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  if (((! (← (HavePACExt ()))) || (size != 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let wback : Bool := (W == 1#1)
  let use_key_a : Bool := (M == 0#1)
  let S10 : (BitVec 10) := (S +++ imm9)
  let scale := 3
  let offset : (BitVec 64) := ((sign_extend S10 64) <<< scale)
  let nontemporal : Bool := false
  let memop : MemOp := MemOp_LOAD
  let tagchecked : Bool := (wback || (n != 31))
  (execute_aarch64_instrs_memory_single_general_immediate_signed_pac memop n nontemporal offset t tagchecked use_key_a wback)

def decode_ldsetp_aarch64_instrs_memory_atomicops_ld_128_ldsetp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
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
  let op ← (( do (undefined_MemAtomicOp ()) ) : SailM MemAtomicOp )
  let op : MemAtomicOp :=
    match (opc : BitVec 3) with
    | 0b001 => MemAtomicOp_BIC
    | 0b011 => MemAtomicOp_ORR
    | _ => op
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_ld_128_ldsetp acquire n op release t t2 tagchecked)

def decode_ldtr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:36647.113-36647.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:36666.107-36666.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldtrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:36733.113-36733.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:36752.107-36752.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldtrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:36819.113-36819.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:36838.107-36838.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldtrsb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:36905.113-36905.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:36924.107-36924.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldtrsh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:36991.113-36991.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37010.107-37010.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldtrsw_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37077.113-37077.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37096.107-37096.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_sttr_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37163.113-37163.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37182.107-37182.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_sttrb_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37249.113-37249.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37268.107-37268.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_sttrh_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37335.113-37335.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:37354.107-37354.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_signed_offset_unpriv datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_ldur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc 1)]) +++ size))
  if ((scale >b 4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  sail_assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "src/instrs64.sail:37447.72-37447.73"
  (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal datasize memop n nontemporal offset postindex t tagchecked wback)

def decode_stur_fpsimd_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm9 : (BitVec 9)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let wback : Bool := false
  let postindex : Bool := false
  let scale := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc 1)]) +++ size))
  if ((scale >b 4) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let offset : (BitVec 64) := (sign_extend imm9 64)
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let nontemporal : Bool := false
  let memop : MemOp :=
    if (((BitVec.join1 [(BitVec.access opc 0)]) == 1#1) : Bool)
    then MemOp_LOAD
    else MemOp_STORE
  let datasize := (Int.shiftl 8 scale)
  let tagchecked : Bool := ((bne memop MemOp_PREFETCH) && (wback || (n != 31)))
  sail_assert ((((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256)) || (datasize == 512)) || (datasize == 1024)) "src/instrs64.sail:37477.72-37477.73"
  (execute_aarch64_instrs_memory_single_simdfp_immediate_signed_offset_normal datasize memop n nontemporal offset postindex t tagchecked wback)

def decode_mla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let sub_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum d datasize elements esize m n sub_op)

def decode_mls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let sub_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_accum d datasize elements esize m n sub_op)

def decode_mla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
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
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int d datasize elements esize idxdsize index m n sub_op)

def decode_mls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
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
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_int d datasize elements esize idxdsize index m n sub_op)

def decode_mrrs_aarch64_instrs_system_register_system_128 (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (o0 : (BitVec 1)) (L : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveSysReg128 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (AArch64_CheckSystemAccess (1#1 +++ o0) op1 CRn CRm op2 Rt L)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat (BitVec.addInt Rt 1))
  let sys_op0 := (2 +i (BitVec.toNat o0))
  let sys_op1 := (BitVec.toNat op1)
  let sys_op2 := (BitVec.toNat op2)
  let sys_crn := (BitVec.toNat CRn)
  let sys_crm := (BitVec.toNat CRm)
  let read : Bool := (L == 1#1)
  (execute_aarch64_instrs_system_register_system_128 read sys_crm sys_crn sys_op0 sys_op1 sys_op2 t t2)

def decode_msrr_aarch64_instrs_system_register_system_128 (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (o0 : (BitVec 1)) (L : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveSysReg128 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (AArch64_CheckSystemAccess (1#1 +++ o0) op1 CRn CRm op2 Rt L)
  let t := (BitVec.toNat Rt)
  let t2 := (BitVec.toNat (BitVec.addInt Rt 1))
  let sys_op0 := (2 +i (BitVec.toNat o0))
  let sys_op1 := (BitVec.toNat op1)
  let sys_op2 := (BitVec.toNat op2)
  let sys_crn := (BitVec.toNat CRn)
  let sys_crm := (BitVec.toNat CRm)
  let read : Bool := (L == 1#1)
  (execute_aarch64_instrs_system_register_system_128 read sys_crm sys_crn sys_op0 sys_op1 sys_op2 t t2)

def decode_mrs_aarch64_instrs_system_register_system (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (o0 : (BitVec 1)) (L : (BitVec 1)) : SailM Unit := do
  (AArch64_CheckSystemAccess (1#1 +++ o0) op1 CRn CRm op2 Rt L)
  let t := (BitVec.toNat Rt)
  let sys_op0 := (2 +i (BitVec.toNat o0))
  let sys_op1 := (BitVec.toNat op1)
  let sys_op2 := (BitVec.toNat op2)
  let sys_crn := (BitVec.toNat CRn)
  let sys_crm := (BitVec.toNat CRm)
  let read : Bool := (L == 1#1)
  (execute_aarch64_instrs_system_register_system read sys_crm sys_crn sys_op0 sys_op1 sys_op2 t)

def decode_msr_reg_aarch64_instrs_system_register_system (Rt : (BitVec 5)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (CRn : (BitVec 4)) (op1 : (BitVec 3)) (o0 : (BitVec 1)) (L : (BitVec 1)) : SailM Unit := do
  (AArch64_CheckSystemAccess (1#1 +++ o0) op1 CRn CRm op2 Rt L)
  let t := (BitVec.toNat Rt)
  let sys_op0 := (2 +i (BitVec.toNat o0))
  let sys_op1 := (BitVec.toNat op1)
  let sys_op2 := (BitVec.toNat op2)
  let sys_crn := (BitVec.toNat CRn)
  let sys_crm := (BitVec.toNat CRm)
  let read : Bool := (L == 1#1)
  (execute_aarch64_instrs_system_register_system read sys_crm sys_crn sys_op0 sys_op1 sys_op2 t)

def decode_msr_imm_aarch64_instrs_system_register_cpsr (op2 : (BitVec 3)) (CRm : (BitVec 4)) (op1 : (BitVec 3)) : SailM Unit := do
  if (((op1 == 0b000#3) && (op2 == 0b000#3)) : Bool)
  then (sailThrow ((Error_See "CFINV")) : SailM Unit)
  else (pure ())
  if (((op1 == 0b000#3) && (op2 == 0b001#3)) : Bool)
  then (sailThrow ((Error_See "XAFLAG")) : SailM Unit)
  else (pure ())
  if (((op1 == 0b000#3) && (op2 == 0b010#3)) : Bool)
  then (sailThrow ((Error_See "AXFLAG")) : SailM Unit)
  else (pure ())
  (AArch64_CheckSystemAccess 0b00#2 op1 0b0100#4 CRm op2 0b11111#5 0#1)
  let min_EL ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let need_secure : Bool := false
  let (min_EL, need_secure) ← (( do
    let b__0 := op1
    let (min_EL, need_secure) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 1) == (0b00#2 : (BitVec 2))) : Bool)
      then
        (let min_EL : (BitVec 2) := EL1
        (pure (min_EL, need_secure)))
      else
        (do
          let (min_EL, need_secure) ← (( do
            if ((b__0 == (0b010#3 : (BitVec 3))) : Bool)
            then
              (let min_EL : (BitVec 2) := EL1
              (pure (min_EL, need_secure)))
            else
              (do
                let (min_EL, need_secure) ← (( do
                  if ((b__0 == (0b011#3 : (BitVec 3))) : Bool)
                  then
                    (let min_EL : (BitVec 2) := EL0
                    (pure (min_EL, need_secure)))
                  else
                    (do
                      let (min_EL, need_secure) ← (( do
                        if ((b__0 == (0b100#3 : (BitVec 3))) : Bool)
                        then
                          (let min_EL : (BitVec 2) := EL2
                          (pure (min_EL, need_secure)))
                        else
                          (do
                            let (min_EL, need_secure) ← (( do
                              if ((b__0 == (0b101#3 : (BitVec 3))) : Bool)
                              then
                                (do
                                  if ((! (← (HaveVirtHostExt ()))) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (pure ())
                                  let min_EL : (BitVec 2) := EL2
                                  (pure (min_EL, need_secure)))
                              else
                                (let (min_EL, need_secure) : ((BitVec 2) × Bool) :=
                                  if ((b__0 == (0b110#3 : (BitVec 3))) : Bool)
                                  then
                                    (let min_EL : (BitVec 2) := EL3
                                    (min_EL, need_secure))
                                  else
                                    (let min_EL : (BitVec 2) := EL1
                                    let need_secure : Bool := true
                                    (min_EL, need_secure))
                                (pure (min_EL, need_secure))) ) : SailM ((BitVec 2) × Bool) )
                            (pure (min_EL, need_secure))) ) : SailM ((BitVec 2) × Bool) )
                      (pure (min_EL, need_secure))) ) : SailM ((BitVec 2) × Bool) )
                (pure (min_EL, need_secure))) ) : SailM ((BitVec 2) × Bool) )
          (pure (min_EL, need_secure))) ) : SailM ((BitVec 2) × Bool) )
    (pure (min_EL, need_secure)) ) : SailM ((BitVec 2) × Bool) )
  let min_EL := min_EL
  if ((←((pure ((BitVec.toNat (← readReg PSTATE).EL) <b (BitVec.toNat min_EL))) <||> (do
       (pure need_secure) <&&> (do
         (pure (bne (← (CurrentSecurityState ())) SS_Secure)))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let operand : (BitVec 4) := CRm
  let field ← (( do (undefined_PSTATEField ()) ) : SailM PSTATEField )
  let field ← (( do
    match ((op1 +++ op2) : BitVec 6) with
    | 0b000011 =>
      (do
        if ((! (← (HaveUAOExt ()))) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure PSTATEField_UAO))
    | 0b000100 =>
      (do
        if ((! (← (HavePANExt ()))) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure PSTATEField_PAN))
    | 0b000101 => (pure PSTATEField_SP)
    | 0b001000 =>
      (do
        let b__6 := CRm
        if (((Sail.BitVec.extractLsb b__6 3 1) == (0b000#3 : (BitVec 3))) : Bool)
        then
          (do
            if ((! (← (HaveFeatNMI ()))) : Bool)
            then (sailThrow ((Error_Undefined ())) : SailM Unit)
            else (pure ())
            (pure PSTATEField_ALLINT))
        else
          (do
            if (((Sail.BitVec.extractLsb b__6 3 1) == (0b001#3 : (BitVec 3))) : Bool)
            then
              (do
                if ((! (← (HaveFeatEBEP ()))) : Bool)
                then (sailThrow ((Error_Undefined ())) : SailM Unit)
                else (pure ())
                (pure PSTATEField_PM))
            else sailThrow ((Error_Undefined ()))))
    | 0b011010 =>
      (do
        if ((! (← (HaveDITExt ()))) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure PSTATEField_DIT))
    | 0b011011 =>
      (do
        let b__8 := CRm
        if (((Sail.BitVec.extractLsb b__8 3 1) == (0b001#3 : (BitVec 3))) : Bool)
        then
          (do
            if ((! (← (HaveSME ()))) : Bool)
            then (sailThrow ((Error_Undefined ())) : SailM Unit)
            else (pure ())
            (pure PSTATEField_SVCRSM))
        else
          (do
            if (((Sail.BitVec.extractLsb b__8 3 1) == (0b010#3 : (BitVec 3))) : Bool)
            then
              (do
                if ((! (← (HaveSME ()))) : Bool)
                then (sailThrow ((Error_Undefined ())) : SailM Unit)
                else (pure ())
                (pure PSTATEField_SVCRZA))
            else
              (do
                if (((Sail.BitVec.extractLsb b__8 3 1) == (0b011#3 : (BitVec 3))) : Bool)
                then
                  (do
                    if ((! (← (HaveSME ()))) : Bool)
                    then (sailThrow ((Error_Undefined ())) : SailM Unit)
                    else (pure ())
                    (pure PSTATEField_SVCRSMZA))
                else sailThrow ((Error_Undefined ())))))
    | 0b011100 =>
      (do
        if ((! (← (HaveMTEExt ()))) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure PSTATEField_TCO))
    | 0b011110 => (pure PSTATEField_DAIFSet)
    | 0b011111 => (pure PSTATEField_DAIFClr)
    | 0b011001 =>
      (do
        if ((! (← (HaveSSBSExt ()))) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure PSTATEField_SSBS))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM PSTATEField )
  if ((((← readReg PSTATE).EL == EL0) && ((BEq.beq field PSTATEField_DAIFSet) || (BEq.beq field PSTATEField_DAIFClr))) : Bool)
  then
    (do
      if ((←((IsInHost ()) <||> (do
           (pure ((_get_SCTLR_EL1_Type_UMA (← readReg SCTLR_EL1)) == 0#1))))) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
          then (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))
          else (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8)))
      else (pure ()))
  else (pure ())
  (execute_aarch64_instrs_system_register_cpsr field operand)

def decode_mul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((U == 1#1) && (size != 0b00#2)) : Bool)
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
  let poly : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product d datasize elements esize m n poly)

def decode_pmul_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((U == 1#1) && (size != 0b00#2)) : Bool)
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
  let poly : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_product d datasize elements esize m n poly)

def decode_mul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_int d datasize elements esize idxdsize index m n)

def decode_not_advsimd_aarch64_instrs_vector_arithmetic_unary_not (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 8
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize 8)
  (execute_aarch64_instrs_vector_arithmetic_unary_not d datasize elements esize n)

def decode_pacda_aarch64_instrs_integer_pac_pacda_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_integer_pac_pacda_dp_1src d n source_is_sp)

def decode_pacdb_aarch64_instrs_integer_pac_pacdb_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_integer_pac_pacdb_dp_1src d n source_is_sp)

def decode_pacga_aarch64_instrs_integer_pac_pacga_dp_2src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((! (← (HavePACExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let source_is_sp : Bool :=
    if ((m == 31) : Bool)
    then true
    else source_is_sp
  (execute_aarch64_instrs_integer_pac_pacga_dp_2src d m n source_is_sp)

def decode_pacia_aarch64_instrs_integer_pac_pacia_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_integer_pac_pacia_dp_1src d n source_is_sp)

def decode_pacia_aarch64_instrs_integer_pac_pacia_hint (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let d : Nat := 17
  let n ← (( do (undefined_int ()) ) : SailM Int )
  let source_is_sp : Bool := false
  let (d, n, source_is_sp) ← (( do
    let b__0 := (CRm +++ op2)
    let (d, n, source_is_sp) ← (( do
      if ((b__0 == (0b0011000#7 : (BitVec 7))) : Bool)
      then
        (let d : Nat := 30
        let n : Int := 31
        (pure (d, n, source_is_sp)))
      else
        (do
          let (d, n, source_is_sp) ← (( do
            if ((b__0 == (0b0011001#7 : (BitVec 7))) : Bool)
            then
              (do
                let d : Nat := 30
                let source_is_sp : Bool := true
                if ((← (HaveBTIExt ())) : Bool)
                then (SetBTypeCompatible (← (BTypeCompatible_PACIXSP ())))
                else (pure ())
                (pure (d, n, source_is_sp)))
            else
              (do
                let (d, n) ← (( do
                  if ((b__0 == (0b0001000#7 : (BitVec 7))) : Bool)
                  then
                    (let d : Nat := 17
                    let n : Int := 16
                    (pure (d, n)))
                  else
                    (do
                      if ((b__0 == (0b0001010#7 : (BitVec 7))) : Bool)
                      then (sailThrow ((Error_See "PACIB")) : SailM Unit)
                      else
                        (do
                          if ((b__0 == (0b0001100#7 : (BitVec 7))) : Bool)
                          then (sailThrow ((Error_See "AUTIA")) : SailM Unit)
                          else
                            (do
                              if ((b__0 == (0b0001110#7 : (BitVec 7))) : Bool)
                              then (sailThrow ((Error_See "AUTIB")) : SailM Unit)
                              else
                                (do
                                  if (((Sail.BitVec.extractLsb b__0 6 1) == (0b001101#6 : (BitVec 6))) : Bool)
                                  then (sailThrow ((Error_See "PACIB")) : SailM Unit)
                                  else
                                    (do
                                      if (((Sail.BitVec.extractLsb b__0 6 1) == (0b001110#6 : (BitVec 6))) : Bool)
                                      then (sailThrow ((Error_See "AUTIA")) : SailM Unit)
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
  sail_assert ((0 ≤b n) && (n ≤b 31)) "src/instrs64.sail:39615.43-39615.44"
  (execute_aarch64_instrs_integer_pac_pacia_dp_1src d n source_is_sp)

def decode_pacib_aarch64_instrs_integer_pac_pacib_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_integer_pac_pacib_dp_1src d n source_is_sp)

def decode_pacib_aarch64_instrs_integer_pac_pacib_hint (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let d : Nat := 17
  let n ← (( do (undefined_int ()) ) : SailM Int )
  let source_is_sp : Bool := false
  let (d, n, source_is_sp) ← (( do
    let b__0 := (CRm +++ op2)
    let (d, n, source_is_sp) ← (( do
      if ((b__0 == (0b0011010#7 : (BitVec 7))) : Bool)
      then
        (let d : Nat := 30
        let n : Int := 31
        (pure (d, n, source_is_sp)))
      else
        (do
          let (d, n, source_is_sp) ← (( do
            if ((b__0 == (0b0011011#7 : (BitVec 7))) : Bool)
            then
              (do
                let d : Nat := 30
                let source_is_sp : Bool := true
                if ((← (HaveBTIExt ())) : Bool)
                then (SetBTypeCompatible (← (BTypeCompatible_PACIXSP ())))
                else (pure ())
                (pure (d, n, source_is_sp)))
            else
              (do
                let (d, n) ← (( do
                  if ((b__0 == (0b0001010#7 : (BitVec 7))) : Bool)
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
                          if ((b__0 == (0b0001100#7 : (BitVec 7))) : Bool)
                          then (sailThrow ((Error_See "AUTIA")) : SailM Unit)
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
                                      if (((Sail.BitVec.extractLsb b__0 6 1) == (0b001110#6 : (BitVec 6))) : Bool)
                                      then (sailThrow ((Error_See "AUTIA")) : SailM Unit)
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
  sail_assert ((0 ≤b n) && (n ≤b 31)) "src/instrs64.sail:39722.43-39722.44"
  (execute_aarch64_instrs_integer_pac_pacib_dp_1src d n source_is_sp)

def decode_pmull_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((size == 0b01#2) || (size == 0b10#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure (size == 0b11#2)) <&&> (do
       (pure (! (← (HaveBit128PMULLExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_mul_poly d datasize elements esize m n part)

def decode_prfm_imm_aarch64_instrs_memory_single_general_immediate_unsigned (Rt : (BitVec 5)) (Rn : (BitVec 5)) (imm12 : (BitVec 12)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
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
        sail_assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:39889.113-39889.114"
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
        sail_assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "src/instrs64.sail:39908.107-39908.108"
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
  (execute_aarch64_instrs_memory_single_general_immediate_unsigned datasize memop n nontemporal offset postindex regsize rt_unknown is_signed t tagchecked wb_unknown wback)

def decode_rax1_advsimd_aarch64_instrs_vector_crypto_sha3_rax1 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSHA3Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  (execute_aarch64_instrs_vector_crypto_sha3_rax1 d m n)

def decode_rbit_advsimd_aarch64_instrs_vector_arithmetic_unary_rbit (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 8
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize 8)
  (execute_aarch64_instrs_vector_arithmetic_unary_rbit d datasize elements esize n)

def decode_rbit_int_aarch64_instrs_integer_arithmetic_rbit (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  (execute_aarch64_instrs_integer_arithmetic_rbit d datasize n)

def decode_rcwcas_aarch64_instrs_memory_rcw_cas (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveTHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let s := (BitVec.toNat Rs)
  let soft : Bool := false
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcw_cas acquire n release s soft t tagchecked)

def decode_rcwcasp_aarch64_instrs_memory_rcw_cas_128 (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((←((pure (! (← (Have128BitDescriptorExt ())))) <||> (do
       (pure (! (← (HaveTHExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access Rs 0)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let s := (BitVec.toNat Rs)
  let soft : Bool := false
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcw_cas_128 acquire n release s soft t tagchecked)

def decode_rcwclr_aarch64_instrs_memory_rcw_ld_rcwclr (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveTHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let s := (BitVec.toNat Rs)
  let soft : Bool := false
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let op : MemAtomicOp :=
    if ((opc == 0b001#3) : Bool)
    then MemAtomicOp_BIC
    else MemAtomicOp_ORR
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcw_ld_rcwclr acquire n op release s soft t tagchecked)

def decode_rcwclrp_aarch64_instrs_memory_rcw_ld_128_rcwclrp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((←((pure (! (← (Have128BitDescriptorExt ())))) <||> (do
       (pure (! (← (HaveTHExt ()))))))) : Bool)
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
  let soft : Bool := false
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let op : MemAtomicOp :=
    if ((opc == 0b001#3) : Bool)
    then MemAtomicOp_BIC
    else MemAtomicOp_ORR
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcw_ld_128_rcwclrp acquire n op release soft t t2 tagchecked)

def decode_rcwscas_aarch64_instrs_memory_rcws_cas (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveTHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let s := (BitVec.toNat Rs)
  let soft : Bool := true
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcws_cas acquire n release s soft t tagchecked)

def decode_rcwscasp_aarch64_instrs_memory_rcws_cas_128 (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((←((pure (! (← (Have128BitDescriptorExt ())))) <||> (do
       (pure (! (← (HaveTHExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access Rs 0)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let s := (BitVec.toNat Rs)
  let soft : Bool := true
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcws_cas_128 acquire n release s soft t tagchecked)

def decode_rcwsclr_aarch64_instrs_memory_rcws_ld_rcwsclr (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveTHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let s := (BitVec.toNat Rs)
  let soft : Bool := true
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let op : MemAtomicOp :=
    if ((opc == 0b001#3) : Bool)
    then MemAtomicOp_BIC
    else MemAtomicOp_ORR
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcws_ld_rcwsclr acquire n op release s soft t tagchecked)

def decode_rcwsclrp_aarch64_instrs_memory_rcws_ld_128_rcwsclrp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((←((pure (! (← (Have128BitDescriptorExt ())))) <||> (do
       (pure (! (← (HaveTHExt ()))))))) : Bool)
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
  let soft : Bool := true
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let op : MemAtomicOp :=
    if ((opc == 0b001#3) : Bool)
    then MemAtomicOp_BIC
    else MemAtomicOp_ORR
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcws_ld_128_rcwsclrp acquire n op release soft t t2 tagchecked)

def decode_rcwset_aarch64_instrs_memory_rcw_ld_rcwset (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveTHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let s := (BitVec.toNat Rs)
  let soft : Bool := false
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let op : MemAtomicOp :=
    if ((opc == 0b001#3) : Bool)
    then MemAtomicOp_BIC
    else MemAtomicOp_ORR
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcw_ld_rcwset acquire n op release s soft t tagchecked)

def decode_rcwsetp_aarch64_instrs_memory_rcw_ld_128_rcwsetp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((←((pure (! (← (Have128BitDescriptorExt ())))) <||> (do
       (pure (! (← (HaveTHExt ()))))))) : Bool)
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
  let soft : Bool := false
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let op : MemAtomicOp :=
    if ((opc == 0b001#3) : Bool)
    then MemAtomicOp_BIC
    else MemAtomicOp_ORR
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcw_ld_128_rcwsetp acquire n op release soft t t2 tagchecked)

def decode_rcwsset_aarch64_instrs_memory_rcws_ld_rcwsset (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveTHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let s := (BitVec.toNat Rs)
  let soft : Bool := true
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let op : MemAtomicOp :=
    if ((opc == 0b001#3) : Bool)
    then MemAtomicOp_BIC
    else MemAtomicOp_ORR
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcws_ld_rcwsset acquire n op release s soft t tagchecked)

def decode_rcwssetp_aarch64_instrs_memory_rcws_ld_128_rcwssetp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((←((pure (! (← (Have128BitDescriptorExt ())))) <||> (do
       (pure (! (← (HaveTHExt ()))))))) : Bool)
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
  let soft : Bool := true
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let op : MemAtomicOp :=
    if ((opc == 0b001#3) : Bool)
    then MemAtomicOp_BIC
    else MemAtomicOp_ORR
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcws_ld_128_rcwssetp acquire n op release soft t t2 tagchecked)

def decode_rcwsswp_aarch64_instrs_memory_rcws_swp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveTHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let s := (BitVec.toNat Rs)
  let soft : Bool := true
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcws_swp acquire n release s soft t tagchecked)

def decode_rcwsswpp_aarch64_instrs_memory_rcws_swp_128 (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((←((pure (! (← (Have128BitDescriptorExt ())))) <||> (do
       (pure (! (← (HaveTHExt ()))))))) : Bool)
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
  let soft : Bool := true
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcws_swp_128 acquire n release soft t t2 tagchecked)

def decode_rcwswp_aarch64_instrs_memory_rcw_swp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rs : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveTHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Rt)
  let n := (BitVec.toNat Rn)
  let s := (BitVec.toNat Rs)
  let soft : Bool := false
  let acquire : Bool := ((A == 1#1) && (Rt != 0b11111#5))
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcw_swp acquire n release s soft t tagchecked)

def decode_rcwswpp_aarch64_instrs_memory_rcw_swp_128 (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 3)) (o3 : (BitVec 1)) (Rt2 : (BitVec 5)) (R : (BitVec 1)) (A : (BitVec 1)) (S : (BitVec 1)) : SailM Unit := do
  if ((←((pure (! (← (Have128BitDescriptorExt ())))) <||> (do
       (pure (! (← (HaveTHExt ()))))))) : Bool)
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
  let soft : Bool := false
  let acquire : Bool := (A == 1#1)
  let release : Bool := (R == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_rcw_swp_128 acquire n release soft t t2 tagchecked)

def decode_rev_aarch64_instrs_integer_arithmetic_rev (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let container_size : Nat := 16
  let container_size ← (( do
    match (opc : BitVec 2) with
    | 0b00 =>
      (do
        (Unreachable ())
        (pure container_size))
    | 0b01 => (pure 16)
    | 0b10 => (pure 32)
    | _ =>
      (do
        if ((sf == 0#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 64)) ) : SailM Int )
  let container_size := container_size
  (execute_aarch64_instrs_integer_arithmetic_rev container_size d datasize n)

def decode_rev16_int_aarch64_instrs_integer_arithmetic_rev (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let container_size : Nat := 16
  let container_size ← (( do
    match (opc : BitVec 2) with
    | 0b00 =>
      (do
        (Unreachable ())
        (pure container_size))
    | 0b01 => (pure 16)
    | 0b10 => (pure 32)
    | _ =>
      (do
        if ((sf == 0#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 64)) ) : SailM Int )
  let container_size := container_size
  (execute_aarch64_instrs_integer_arithmetic_rev container_size d datasize n)

def decode_rev32_int_aarch64_instrs_integer_arithmetic_rev (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let container_size : Nat := 16
  let container_size ← (( do
    match (opc : BitVec 2) with
    | 0b00 =>
      (do
        (Unreachable ())
        (pure container_size))
    | 0b01 => (pure 16)
    | 0b10 => (pure 32)
    | _ =>
      (do
        if ((sf == 0#1) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 64)) ) : SailM Int )
  let container_size := container_size
  (execute_aarch64_instrs_integer_arithmetic_rev container_size d datasize n)

def decode_rev16_advsimd_aarch64_instrs_vector_arithmetic_unary_rev (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let op : (BitVec 2) := (o0 +++ U)
  if ((((BitVec.toNat op) +i (BitVec.toNat size)) ≥b 3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let container_size : Nat := 16
  let container_size : Int :=
    match (op : BitVec 2) with
    | 0b10 => 16
    | 0b01 => 32
    | 0b00 => 64
    | _ => container_size
  let container_size := container_size
  let containers := (Int.ediv datasize container_size)
  let elements_per_container := (Int.ediv container_size esize)
  (execute_aarch64_instrs_vector_arithmetic_unary_rev containers d datasize elements_per_container esize n)

def decode_rev32_advsimd_aarch64_instrs_vector_arithmetic_unary_rev (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let op : (BitVec 2) := (o0 +++ U)
  if ((((BitVec.toNat op) +i (BitVec.toNat size)) ≥b 3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let container_size : Nat := 16
  let container_size : Int :=
    match (op : BitVec 2) with
    | 0b10 => 16
    | 0b01 => 32
    | 0b00 => 64
    | _ => container_size
  let container_size := container_size
  let containers := (Int.ediv datasize container_size)
  let elements_per_container := (Int.ediv container_size esize)
  (execute_aarch64_instrs_vector_arithmetic_unary_rev containers d datasize elements_per_container esize n)

def decode_rev64_advsimd_aarch64_instrs_vector_arithmetic_unary_rev (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let op : (BitVec 2) := (o0 +++ U)
  if ((((BitVec.toNat op) +i (BitVec.toNat size)) ≥b 3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let container_size : Nat := 16
  let container_size : Int :=
    match (op : BitVec 2) with
    | 0b10 => 16
    | 0b01 => 32
    | 0b00 => 64
    | _ => container_size
  let container_size := container_size
  let containers := (Int.ediv datasize container_size)
  let elements_per_container := (Int.ediv container_size esize)
  (execute_aarch64_instrs_vector_arithmetic_unary_rev containers d datasize elements_per_container esize n)

def decode_rmif_aarch64_instrs_integer_flags_rmif (mask : (BitVec 4)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (sf : (BitVec 1)) : SailM Unit := do
  if (((! (← (HaveFlagManipulateExt ()))) || (sf != 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let lsb := (BitVec.toNat imm6)
  let n := (BitVec.toNat Rn)
  (execute_aarch64_instrs_integer_flags_rmif lsb mask n)

def decode_rprfm_reg_aarch64_instrs_memory_single_general_range (Rt : (BitVec 5)) (Rn : (BitVec 5)) (S : (BitVec 1)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (opc : (BitVec 2)) (size : (BitVec 2)) : SailM Unit := do
  let operation : (BitVec 6) := ((((BitVec.join1 [(BitVec.access option_name 2)]) +++ (BitVec.join1 [(BitVec.access option_name 0)])) +++ S) +++ (Sail.BitVec.extractLsb Rt 2 0))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  (execute_aarch64_instrs_memory_single_general_range m n operation)

def decode_rshrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) : SailM Unit := do
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
  sail_assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:41451.51-41451.52"
  (execute_aarch64_instrs_vector_shift_right_narrow_logical d datasize elements esize n part round shift)

def decode_shrn_advsimd_aarch64_instrs_vector_shift_right_narrow_logical (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) : SailM Unit := do
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
  sail_assert (((((esize == 4) || (esize == 8)) || (esize == 16)) || (esize == 32)) || (esize == 64)) "src/instrs64.sail:41483.51-41483.52"
  (execute_aarch64_instrs_vector_shift_right_narrow_logical d datasize elements esize n part round shift)

def decode_saba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let accumulate : Bool := (ac == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff accumulate d datasize elements esize m n is_unsigned)

def decode_sabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let accumulate : Bool := (ac == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff accumulate d datasize elements esize m n is_unsigned)

def decode_uaba_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let accumulate : Bool := (ac == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff accumulate d datasize elements esize m n is_unsigned)

def decode_uabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let accumulate : Bool := (ac == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_diff accumulate d datasize elements esize m n is_unsigned)

def decode_sabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let accumulate : Bool := (op == 0#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff accumulate d datasize elements esize m n part is_unsigned)

def decode_sabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let accumulate : Bool := (op == 0#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff accumulate d datasize elements esize m n part is_unsigned)

def decode_uabal_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let accumulate : Bool := (op == 0#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff accumulate d datasize elements esize m n part is_unsigned)

def decode_uabdl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_diff (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let accumulate : Bool := (op == 0#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_diff accumulate d datasize elements esize m n part is_unsigned)

def decode_sadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize (2 *i esize))
  let acc : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise acc d datasize elements esize n is_unsigned)

def decode_saddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize (2 *i esize))
  let acc : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise acc d datasize elements esize n is_unsigned)

def decode_uadalp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize (2 *i esize))
  let acc : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise acc d datasize elements esize n is_unsigned)

def decode_uaddlp_advsimd_aarch64_instrs_vector_arithmetic_unary_add_pairwise (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize (2 *i esize))
  let acc : Bool := (op == 1#1)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_add_pairwise acc d datasize elements esize n is_unsigned)

def decode_saddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long d datasize elements esize m n part sub_op is_unsigned)

def decode_ssubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long d datasize elements esize m n part sub_op is_unsigned)

def decode_uaddl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long d datasize elements esize m n part sub_op is_unsigned)

def decode_usubl_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_long d datasize elements esize m n part sub_op is_unsigned)

def decode_saddlv_advsimd_aarch64_instrs_vector_reduce_add_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_reduce_add_long d datasize elements esize n is_unsigned)

def decode_uaddlv_advsimd_aarch64_instrs_vector_reduce_add_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_reduce_add_long d datasize elements esize n is_unsigned)

def decode_saddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide d datasize elements esize m n part sub_op is_unsigned)

def decode_ssubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide d datasize elements esize m n part sub_op is_unsigned)

def decode_uaddw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide d datasize elements esize m n part sub_op is_unsigned)

def decode_usubw_advsimd_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_disparate_add_sub_wide d datasize elements esize m n part sub_op is_unsigned)

def decode_sb_aarch64_instrs_system_barriers_sb (opc : (BitVec 2)) (CRm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveSBExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_system_barriers_sb ())

def decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((let b__0 := immh
       if (((Sail.BitVec.extractLsb b__0 3 1) == (0b000#3 : (BitVec 3))) : Bool)
       then true
       else false : Bool) || ((let b__1 := immh
         if (((Sail.BitVec.extractLsb b__1 3 1) == (0b001#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) && (! (HaveFP16Ext ())))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize :=
    if ((let b__3 := immh
       if (((Sail.BitVec.extractLsb b__3 3 3) == (1#1 : (BitVec 1))) : Bool)
       then true
       else false : Bool) : Bool)
    then 64
    else
      (if ((let b__2 := immh
         if (((Sail.BitVec.extractLsb b__2 3 2) == (0b01#2 : (BitVec 2))) : Bool)
         then true
         else false : Bool) : Bool)
      then 32
      else 16)
  let datasize := esize
  let elements := 1
  let fracbits := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  (execute_aarch64_instrs_vector_shift_conv_int_sisd d datasize elements esize fracbits n rounding is_unsigned)

def decode_scvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if (((let b__0 := immh
       if (((Sail.BitVec.extractLsb b__0 3 1) == (0b000#3 : (BitVec 3))) : Bool)
       then true
       else false : Bool) || ((let b__1 := immh
         if (((Sail.BitVec.extractLsb b__1 3 1) == (0b001#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) && (! (HaveFP16Ext ())))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access immh 3)]) +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize :=
    if ((let b__3 := immh
       if (((Sail.BitVec.extractLsb b__3 3 3) == (1#1 : (BitVec 1))) : Bool)
       then true
       else false : Bool) : Bool)
    then 64
    else
      (if ((let b__2 := immh
         if (((Sail.BitVec.extractLsb b__2 3 2) == (0b01#2 : (BitVec 2))) : Bool)
         then true
         else false : Bool) : Bool)
      then 32
      else 16)
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let fracbits := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  (execute_aarch64_instrs_vector_shift_conv_int_sisd d datasize elements esize fracbits n rounding is_unsigned)

def decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((let b__0 := immh
       if (((Sail.BitVec.extractLsb b__0 3 1) == (0b000#3 : (BitVec 3))) : Bool)
       then true
       else false : Bool) || ((let b__1 := immh
         if (((Sail.BitVec.extractLsb b__1 3 1) == (0b001#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) && (! (HaveFP16Ext ())))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize :=
    if ((let b__3 := immh
       if (((Sail.BitVec.extractLsb b__3 3 3) == (1#1 : (BitVec 1))) : Bool)
       then true
       else false : Bool) : Bool)
    then 64
    else
      (if ((let b__2 := immh
         if (((Sail.BitVec.extractLsb b__2 3 2) == (0b01#2 : (BitVec 2))) : Bool)
         then true
         else false : Bool) : Bool)
      then 32
      else 16)
  let datasize := esize
  let elements := 1
  let fracbits := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  (execute_aarch64_instrs_vector_shift_conv_int_sisd d datasize elements esize fracbits n rounding is_unsigned)

def decode_ucvtf_advsimd_fix_aarch64_instrs_vector_shift_conv_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((immh == 0b0000#4) : Bool)
  then (sailThrow ((Error_See "asimdimm")) : SailM Unit)
  else (pure ())
  if (((let b__0 := immh
       if (((Sail.BitVec.extractLsb b__0 3 1) == (0b000#3 : (BitVec 3))) : Bool)
       then true
       else false : Bool) || ((let b__1 := immh
         if (((Sail.BitVec.extractLsb b__1 3 1) == (0b001#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) && (! (HaveFP16Ext ())))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access immh 3)]) +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize :=
    if ((let b__3 := immh
       if (((Sail.BitVec.extractLsb b__3 3 3) == (1#1 : (BitVec 1))) : Bool)
       then true
       else false : Bool) : Bool)
    then 64
    else
      (if ((let b__2 := immh
         if (((Sail.BitVec.extractLsb b__2 3 2) == (0b01#2 : (BitVec 2))) : Bool)
         then true
         else false : Bool) : Bool)
      then 32
      else 16)
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let fracbits := ((esize *i 2) -i (BitVec.toNat (immh +++ immb)))
  let is_unsigned : Bool := (U == 1#1)
  let rounding ← (( do (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  (execute_aarch64_instrs_vector_shift_conv_int_sisd d datasize elements esize fracbits n rounding is_unsigned)

def decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd d datasize elements esize n is_unsigned)

def decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd d datasize elements esize n is_unsigned)

def decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd d datasize elements esize n is_unsigned)

def decode_scvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd d datasize elements esize n is_unsigned)

def decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd d datasize elements esize n is_unsigned)

def decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd d datasize elements esize n is_unsigned)

def decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd d datasize elements esize n is_unsigned)

def decode_ucvtf_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((sz +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_int_sisd d datasize elements esize n is_unsigned)

def decode_sdiv_aarch64_instrs_integer_arithmetic_div (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let is_unsigned : Bool := (o1 == 0#1)
  (execute_aarch64_instrs_integer_arithmetic_div d datasize m n is_unsigned)

def decode_udiv_aarch64_instrs_integer_arithmetic_div (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let is_unsigned : Bool := (o1 == 0#1)
  (execute_aarch64_instrs_integer_arithmetic_div d datasize m n is_unsigned)

def decode_sdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveDOTPExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size != 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := (U == 0#1)
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp d datasize elements esize m n is_signed)

def decode_udot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveDOTPExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size != 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := (U == 0#1)
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_dotp d datasize elements esize m n is_signed)

def decode_sdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveDOTPExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size != 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := (U == 0#1)
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (M +++ Rm))
  let index := (BitVec.toNat (H +++ L))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_dotp d datasize elements esize index m n is_signed)

def decode_udot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_dotp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveDOTPExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size != 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := (U == 0#1)
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (M +++ Rm))
  let index := (BitVec.toNat (H +++ L))
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_dotp d datasize elements esize index m n is_signed)

def decode_setp_aarch64_instrs_memory_mcpymset_set (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match ((Sail.BitVec.extractLsb op2 3 2) : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:43117.58-43117.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_set d n options_name s stage)

def decode_setpn_aarch64_instrs_memory_mcpymset_set (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match ((Sail.BitVec.extractLsb op2 3 2) : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:43173.58-43173.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_set d n options_name s stage)

def decode_setpt_aarch64_instrs_memory_mcpymset_set (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match ((Sail.BitVec.extractLsb op2 3 2) : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:43229.58-43229.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_set d n options_name s stage)

def decode_setptn_aarch64_instrs_memory_mcpymset_set (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match ((Sail.BitVec.extractLsb op2 3 2) : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:43285.58-43285.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_set d n options_name s stage)

def decode_setf_aarch64_instrs_integer_flags_setf (Rn : (BitVec 5)) (sz : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  if (((! (← (HaveFlagManipulateExt ()))) || (sf != 0#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let msb :=
    if ((sz == 1#1) : Bool)
    then 15
    else 7
  let n := (BitVec.toNat Rn)
  (execute_aarch64_instrs_integer_flags_setf msb n)

def decode_setgp_aarch64_instrs_memory_mcpymset_setg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match ((Sail.BitVec.extractLsb op2 3 2) : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:43530.58-43530.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_setg d n options_name s stage)

def decode_setgpn_aarch64_instrs_memory_mcpymset_setg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match ((Sail.BitVec.extractLsb op2 3 2) : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:43589.58-43589.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_setg d n options_name s stage)

def decode_setgpt_aarch64_instrs_memory_mcpymset_setg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match ((Sail.BitVec.extractLsb op2 3 2) : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:43648.58-43648.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_setg d n options_name s stage)

def decode_setgptn_aarch64_instrs_memory_mcpymset_setg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveMTEExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match ((Sail.BitVec.extractLsb op2 3 2) : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:43707.58-43707.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_setg d n options_name s stage)

def decode_sha1c_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((! (← (HaveSHA1Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_choose d m n)

def decode_sha1h_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_hash (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((! (← (HaveSHA1Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_vector_crypto_sha2op_sha1_hash d n)

def decode_sha1m_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((! (← (HaveSHA1Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_majority d m n)

def decode_sha1p_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((! (← (HaveSHA1Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_vector_crypto_sha3op_sha1_hash_parity d m n)

def decode_sha1su0_advsimd_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((! (← (HaveSHA1Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_vector_crypto_sha3op_sha1_sched0 d m n)

def decode_sha1su1_advsimd_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((! (← (HaveSHA1Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_vector_crypto_sha2op_sha1_sched1 d n)

def decode_sha256h_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash (Rd : (BitVec 5)) (Rn : (BitVec 5)) (P : (BitVec 1)) (Rm : (BitVec 5)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((! (← (HaveSHA256Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let part1 : Bool := (P == 0#1)
  (execute_aarch64_instrs_vector_crypto_sha3op_sha256_hash d m n part1)

def decode_sha256h2_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_hash (Rd : (BitVec 5)) (Rn : (BitVec 5)) (P : (BitVec 1)) (Rm : (BitVec 5)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((! (← (HaveSHA256Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let part1 : Bool := (P == 0#1)
  (execute_aarch64_instrs_vector_crypto_sha3op_sha256_hash d m n part1)

def decode_sha256su0_advsimd_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((! (← (HaveSHA256Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_vector_crypto_sha2op_sha256_sched0 d n)

def decode_sha256su1_advsimd_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((! (← (HaveSHA256Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_vector_crypto_sha3op_sha256_sched1 d m n)

def decode_sha512h_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSHA512Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  (execute_aarch64_instrs_vector_crypto_sha512_sha512h d m n)

def decode_sha512h2_advsimd_aarch64_instrs_vector_crypto_sha512_sha512h2 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSHA512Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  (execute_aarch64_instrs_vector_crypto_sha512_sha512h2 d m n)

def decode_sha512su0_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su0 (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSHA512Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  (execute_aarch64_instrs_vector_crypto_sha512_sha512su0 d n)

def decode_sha512su1_advsimd_aarch64_instrs_vector_crypto_sha512_sha512su1 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSHA512Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  (execute_aarch64_instrs_vector_crypto_sha512_sha512su1 d m n)

def decode_shadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating d datasize elements esize m n is_unsigned)

def decode_uhadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_halving_truncating d datasize elements esize m n is_unsigned)

def decode_shl_advsimd_aarch64_instrs_vector_shift_left_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((BitVec.join1 [(BitVec.access immh 3)]) != 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 3)
  let datasize := esize
  let elements := 1
  let shift := ((BitVec.toNat (immh +++ immb)) -i esize)
  (execute_aarch64_instrs_vector_shift_left_sisd d datasize elements esize n shift)

def decode_shl_advsimd_aarch64_instrs_vector_shift_left_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_shift_left_sisd d datasize elements esize n shift)

def decode_shll_advsimd_aarch64_instrs_vector_arithmetic_unary_shift (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv datasize esize)
  let shift := esize
  let is_unsigned : Bool := false
  (execute_aarch64_instrs_vector_arithmetic_unary_shift d datasize elements esize n part shift is_unsigned)

def decode_shsub_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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


