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

def decode_autib_aarch64_instrs_integer_pac_autib_hint (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let d : Nat := 17
  let n ← (( do (undefined_int ()) ) : SailM Int )
  let source_is_sp : Bool := false
  let (d, n, source_is_sp) ← (( do
    let b__0 := (CRm +++ op2)
    let (d, n, source_is_sp) ← (( do
      if ((b__0 == (0b0011110#7 : (BitVec 7))) : Bool)
      then
        (let d : Nat := 30
        let n : Int := 31
        (pure (d, n, source_is_sp)))
      else
        (do
          let (d, n, source_is_sp) ← (( do
            if ((b__0 == (0b0011111#7 : (BitVec 7))) : Bool)
            then
              (let d : Nat := 30
              let source_is_sp : Bool := true
              (pure (d, n, source_is_sp)))
            else
              (do
                let (d, n) ← (( do
                  if ((b__0 == (0b0001110#7 : (BitVec 7))) : Bool)
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
                              if ((b__0 == (0b0001100#7 : (BitVec 7))) : Bool)
                              then (sailThrow ((Error_See "AUTIA")) : SailM Unit)
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
                                          if (((Sail.BitVec.extractLsb b__0 6 1) == (0b001110#6 : (BitVec 6))) : Bool)
                                          then (sailThrow ((Error_See "AUTIA")) : SailM Unit)
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
  sail_assert ((0 ≤b n) && (n ≤b 31)) "src/instrs64.sail:2575.43-2575.44"
  (execute_aarch64_instrs_integer_pac_autib_dp_1src d n source_is_sp)

def decode_axflag_aarch64_instrs_integer_flags_axflag (CRm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveFlagFormatExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_integer_flags_axflag ())

def decode_bc_cond_aarch64_instrs_branch_conditional_hinted (cond : (BitVec 4)) (imm19 : (BitVec 19)) : SailM Unit := do
  if ((! (← (HaveFeatHBC ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  let condition : (BitVec 4) := cond
  (execute_aarch64_instrs_branch_conditional_hinted condition offset)

def decode_bcax_advsimd_aarch64_instrs_vector_crypto_sha3_bcax (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSHA3Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let a := (BitVec.toNat Ra)
  (execute_aarch64_instrs_vector_crypto_sha3_bcax a d m n)

def decode_bfcvt_float_aarch64_instrs_vector_cvt_bf16_scalar (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveBF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let d := (BitVec.toNat Rd)
  (execute_aarch64_instrs_vector_cvt_bf16_scalar d n)

def decode_bfcvtn_advsimd_aarch64_instrs_vector_cvt_bf16_vector (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveBF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let d := (BitVec.toNat Rd)
  let part := (BitVec.toNat Q)
  let elements := (Int.ediv 64 16)
  (execute_aarch64_instrs_vector_cvt_bf16_vector d elements n part)

def decode_bfdot_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_bfdot (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveBF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (M +++ Rm))
  let d := (BitVec.toNat Rd)
  let i := (BitVec.toNat (H +++ L))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize 32)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_bfdot d datasize elements i m n)

def decode_bfdot_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_bfdot (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveBF16Ext ()))) : Bool)
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_int_bfdot d datasize elements m n)

def decode_bfm_aarch64_instrs_integer_bitfield (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let inzero ← (( do (undefined_bool ()) ) : SailM Bool )
  let extend ← (( do (undefined_bool ()) ) : SailM Bool )
  let wmask ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let tmask ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let (extend, inzero) ← (( do
    match (opc : BitVec 2) with
    | 0b00 =>
      (let inzero : Bool := true
      let extend : Bool := true
      (pure (extend, inzero)))
    | 0b01 =>
      (let inzero : Bool := false
      let extend : Bool := false
      (pure (extend, inzero)))
    | 0b10 =>
      (let inzero : Bool := true
      let extend : Bool := false
      (pure (extend, inzero)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × Bool) )
  let extend := extend
  let inzero := inzero
  if (((sf == 1#1) && (N != 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((sf == 0#1) && (((N != 0#1) || ((BitVec.join1 [(BitVec.access immr 5)]) != 0#1)) || ((BitVec.join1 [(BitVec.access imms 5)]) != 0#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let r := (BitVec.toNat immr)
  let s := (BitVec.toNat imms)
  let (tmask, wmask) ← (( do
    let (tup__0, tup__1) ← do (DecodeBitMasks N imms immr false datasize)
    let wmask : (BitVec datasize) := tup__0
    let tmask : (BitVec datasize) := tup__1
    (pure (tmask, wmask)) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
  (execute_aarch64_instrs_integer_bitfield d datasize extend inzero n r s tmask wmask)

def decode_sbfm_aarch64_instrs_integer_bitfield (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let inzero ← (( do (undefined_bool ()) ) : SailM Bool )
  let extend ← (( do (undefined_bool ()) ) : SailM Bool )
  let wmask ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let tmask ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let (extend, inzero) ← (( do
    match (opc : BitVec 2) with
    | 0b00 =>
      (let inzero : Bool := true
      let extend : Bool := true
      (pure (extend, inzero)))
    | 0b01 =>
      (let inzero : Bool := false
      let extend : Bool := false
      (pure (extend, inzero)))
    | 0b10 =>
      (let inzero : Bool := true
      let extend : Bool := false
      (pure (extend, inzero)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × Bool) )
  let extend := extend
  let inzero := inzero
  if (((sf == 1#1) && (N != 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((sf == 0#1) && (((N != 0#1) || ((BitVec.join1 [(BitVec.access immr 5)]) != 0#1)) || ((BitVec.join1 [(BitVec.access imms 5)]) != 0#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let r := (BitVec.toNat immr)
  let s := (BitVec.toNat imms)
  let (tmask, wmask) ← (( do
    let (tup__0, tup__1) ← do (DecodeBitMasks N imms immr false datasize)
    let wmask : (BitVec datasize) := tup__0
    let tmask : (BitVec datasize) := tup__1
    (pure (tmask, wmask)) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
  (execute_aarch64_instrs_integer_bitfield d datasize extend inzero n r s tmask wmask)

def decode_ubfm_aarch64_instrs_integer_bitfield (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let inzero ← (( do (undefined_bool ()) ) : SailM Bool )
  let extend ← (( do (undefined_bool ()) ) : SailM Bool )
  let wmask ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let tmask ← (( do (undefined_bitvector datasize) ) : SailM (BitVec datasize) )
  let (extend, inzero) ← (( do
    match (opc : BitVec 2) with
    | 0b00 =>
      (let inzero : Bool := true
      let extend : Bool := true
      (pure (extend, inzero)))
    | 0b01 =>
      (let inzero : Bool := false
      let extend : Bool := false
      (pure (extend, inzero)))
    | 0b10 =>
      (let inzero : Bool := true
      let extend : Bool := false
      (pure (extend, inzero)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × Bool) )
  let extend := extend
  let inzero := inzero
  if (((sf == 1#1) && (N != 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((sf == 0#1) && (((N != 0#1) || ((BitVec.join1 [(BitVec.access immr 5)]) != 0#1)) || ((BitVec.join1 [(BitVec.access imms 5)]) != 0#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let r := (BitVec.toNat immr)
  let s := (BitVec.toNat imms)
  let (tmask, wmask) ← (( do
    let (tup__0, tup__1) ← do (DecodeBitMasks N imms immr false datasize)
    let wmask : (BitVec datasize) := tup__0
    let tmask : (BitVec datasize) := tup__1
    (pure (tmask, wmask)) ) : SailM ((BitVec datasize) × (BitVec datasize)) )
  (execute_aarch64_instrs_integer_bitfield d datasize extend inzero n r s tmask wmask)

def decode_bfmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_bf16_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveBF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (0#1 +++ Rm))
  let d := (BitVec.toNat Rd)
  let index := (BitVec.toNat ((H +++ L) +++ M))
  let elements := (Int.ediv 128 32)
  let sel := (BitVec.toNat Q)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_bf16_long d elements index m n sel)

def decode_bfmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_acc_bf16_long (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveBF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let elements := (Int.ediv 128 32)
  let sel := (BitVec.toNat Q)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_acc_bf16_long d elements m n sel)

def decode_bfmmla_advsimd_aarch64_instrs_vector_bfmmla (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveBF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  (execute_aarch64_instrs_vector_bfmmla d m n)

def decode_bic_advsimd_imm_aarch64_instrs_vector_logical (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let rd := (BitVec.toNat Rd)
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let operation ← (( do (undefined_ImmediateOp ()) ) : SailM ImmediateOp )
  let operation ← (( do
    let b__0 := (cmode +++ op)
    if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
    then (pure ImmediateOp_MOVI)
    else
      (do
        if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b01#2 : (BitVec 2)))) : Bool)
        then (pure ImmediateOp_MVNI)
        else
          (do
            if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b10#2 : (BitVec 2)))) : Bool)
            then (pure ImmediateOp_ORR)
            else
              (do
                if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
                then (pure ImmediateOp_BIC)
                else
                  (do
                    if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
                    then (pure ImmediateOp_MOVI)
                    else
                      (do
                        if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b01#2 : (BitVec 2)))) : Bool)
                        then (pure ImmediateOp_MVNI)
                        else
                          (do
                            if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b10#2 : (BitVec 2)))) : Bool)
                            then (pure ImmediateOp_ORR)
                            else
                              (do
                                if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
                                then (pure ImmediateOp_BIC)
                                else
                                  (do
                                    if ((((Sail.BitVec.extractLsb b__0 4 2) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                    then (pure ImmediateOp_MOVI)
                                    else
                                      (do
                                        if ((((Sail.BitVec.extractLsb b__0 4 2) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb b__0 0 0) == (1#1 : (BitVec 1)))) : Bool)
                                        then (pure ImmediateOp_MVNI)
                                        else
                                          (do
                                            if (((Sail.BitVec.extractLsb b__0 4 1) == (0xE#4 : (BitVec 4))) : Bool)
                                            then (pure ImmediateOp_MOVI)
                                            else
                                              (do
                                                if ((b__0 == (0b11110#5 : (BitVec 5))) : Bool)
                                                then (pure ImmediateOp_MOVI)
                                                else
                                                  (do
                                                    if ((Q == 0#1) : Bool)
                                                    then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                    else (pure ())
                                                    (pure ImmediateOp_MOVI))))))))))))) ) : SailM ImmediateOp )
  let operation := operation
  let imm64 ← (( do (AdvSIMDExpandImm op cmode (((((((a +++ b) +++ c) +++ d) +++ e) +++ f) +++ g) +++ h)) ) : SailM (BitVec 64) )
  let imm : (BitVec datasize) := (BitVec.replicateBits imm64 (Int.ediv datasize 64))
  (execute_aarch64_instrs_vector_logical datasize imm operation rd)

def decode_movi_advsimd_aarch64_instrs_vector_logical (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let rd := (BitVec.toNat Rd)
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let operation ← (( do (undefined_ImmediateOp ()) ) : SailM ImmediateOp )
  let operation ← (( do
    let b__0 := (cmode +++ op)
    if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
    then (pure ImmediateOp_MOVI)
    else
      (do
        if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b01#2 : (BitVec 2)))) : Bool)
        then (pure ImmediateOp_MVNI)
        else
          (do
            if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b10#2 : (BitVec 2)))) : Bool)
            then (pure ImmediateOp_ORR)
            else
              (do
                if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
                then (pure ImmediateOp_BIC)
                else
                  (do
                    if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
                    then (pure ImmediateOp_MOVI)
                    else
                      (do
                        if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b01#2 : (BitVec 2)))) : Bool)
                        then (pure ImmediateOp_MVNI)
                        else
                          (do
                            if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b10#2 : (BitVec 2)))) : Bool)
                            then (pure ImmediateOp_ORR)
                            else
                              (do
                                if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
                                then (pure ImmediateOp_BIC)
                                else
                                  (do
                                    if ((((Sail.BitVec.extractLsb b__0 4 2) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                    then (pure ImmediateOp_MOVI)
                                    else
                                      (do
                                        if ((((Sail.BitVec.extractLsb b__0 4 2) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb b__0 0 0) == (1#1 : (BitVec 1)))) : Bool)
                                        then (pure ImmediateOp_MVNI)
                                        else
                                          (do
                                            if (((Sail.BitVec.extractLsb b__0 4 1) == (0xE#4 : (BitVec 4))) : Bool)
                                            then (pure ImmediateOp_MOVI)
                                            else
                                              (do
                                                if ((b__0 == (0b11110#5 : (BitVec 5))) : Bool)
                                                then (pure ImmediateOp_MOVI)
                                                else
                                                  (do
                                                    if ((Q == 0#1) : Bool)
                                                    then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                    else (pure ())
                                                    (pure ImmediateOp_MOVI))))))))))))) ) : SailM ImmediateOp )
  let operation := operation
  let imm64 ← (( do (AdvSIMDExpandImm op cmode (((((((a +++ b) +++ c) +++ d) +++ e) +++ f) +++ g) +++ h)) ) : SailM (BitVec 64) )
  let imm : (BitVec datasize) := (BitVec.replicateBits imm64 (Int.ediv datasize 64))
  (execute_aarch64_instrs_vector_logical datasize imm operation rd)

def decode_mvni_advsimd_aarch64_instrs_vector_logical (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let rd := (BitVec.toNat Rd)
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let operation ← (( do (undefined_ImmediateOp ()) ) : SailM ImmediateOp )
  let operation ← (( do
    let b__0 := (cmode +++ op)
    if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
    then (pure ImmediateOp_MOVI)
    else
      (do
        if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b01#2 : (BitVec 2)))) : Bool)
        then (pure ImmediateOp_MVNI)
        else
          (do
            if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b10#2 : (BitVec 2)))) : Bool)
            then (pure ImmediateOp_ORR)
            else
              (do
                if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
                then (pure ImmediateOp_BIC)
                else
                  (do
                    if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
                    then (pure ImmediateOp_MOVI)
                    else
                      (do
                        if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b01#2 : (BitVec 2)))) : Bool)
                        then (pure ImmediateOp_MVNI)
                        else
                          (do
                            if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b10#2 : (BitVec 2)))) : Bool)
                            then (pure ImmediateOp_ORR)
                            else
                              (do
                                if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
                                then (pure ImmediateOp_BIC)
                                else
                                  (do
                                    if ((((Sail.BitVec.extractLsb b__0 4 2) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                    then (pure ImmediateOp_MOVI)
                                    else
                                      (do
                                        if ((((Sail.BitVec.extractLsb b__0 4 2) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb b__0 0 0) == (1#1 : (BitVec 1)))) : Bool)
                                        then (pure ImmediateOp_MVNI)
                                        else
                                          (do
                                            if (((Sail.BitVec.extractLsb b__0 4 1) == (0xE#4 : (BitVec 4))) : Bool)
                                            then (pure ImmediateOp_MOVI)
                                            else
                                              (do
                                                if ((b__0 == (0b11110#5 : (BitVec 5))) : Bool)
                                                then (pure ImmediateOp_MOVI)
                                                else
                                                  (do
                                                    if ((Q == 0#1) : Bool)
                                                    then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                    else (pure ())
                                                    (pure ImmediateOp_MOVI))))))))))))) ) : SailM ImmediateOp )
  let operation := operation
  let imm64 ← (( do (AdvSIMDExpandImm op cmode (((((((a +++ b) +++ c) +++ d) +++ e) +++ f) +++ g) +++ h)) ) : SailM (BitVec 64) )
  let imm : (BitVec datasize) := (BitVec.replicateBits imm64 (Int.ediv datasize 64))
  (execute_aarch64_instrs_vector_logical datasize imm operation rd)

def decode_orr_advsimd_imm_aarch64_instrs_vector_logical (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let rd := (BitVec.toNat Rd)
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let operation ← (( do (undefined_ImmediateOp ()) ) : SailM ImmediateOp )
  let operation ← (( do
    let b__0 := (cmode +++ op)
    if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
    then (pure ImmediateOp_MOVI)
    else
      (do
        if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b01#2 : (BitVec 2)))) : Bool)
        then (pure ImmediateOp_MVNI)
        else
          (do
            if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b10#2 : (BitVec 2)))) : Bool)
            then (pure ImmediateOp_ORR)
            else
              (do
                if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
                then (pure ImmediateOp_BIC)
                else
                  (do
                    if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
                    then (pure ImmediateOp_MOVI)
                    else
                      (do
                        if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b01#2 : (BitVec 2)))) : Bool)
                        then (pure ImmediateOp_MVNI)
                        else
                          (do
                            if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b10#2 : (BitVec 2)))) : Bool)
                            then (pure ImmediateOp_ORR)
                            else
                              (do
                                if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
                                then (pure ImmediateOp_BIC)
                                else
                                  (do
                                    if ((((Sail.BitVec.extractLsb b__0 4 2) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                    then (pure ImmediateOp_MOVI)
                                    else
                                      (do
                                        if ((((Sail.BitVec.extractLsb b__0 4 2) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb b__0 0 0) == (1#1 : (BitVec 1)))) : Bool)
                                        then (pure ImmediateOp_MVNI)
                                        else
                                          (do
                                            if (((Sail.BitVec.extractLsb b__0 4 1) == (0xE#4 : (BitVec 4))) : Bool)
                                            then (pure ImmediateOp_MOVI)
                                            else
                                              (do
                                                if ((b__0 == (0b11110#5 : (BitVec 5))) : Bool)
                                                then (pure ImmediateOp_MOVI)
                                                else
                                                  (do
                                                    if ((Q == 0#1) : Bool)
                                                    then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                    else (pure ())
                                                    (pure ImmediateOp_MOVI))))))))))))) ) : SailM ImmediateOp )
  let operation := operation
  let imm64 ← (( do (AdvSIMDExpandImm op cmode (((((((a +++ b) +++ c) +++ d) +++ e) +++ f) +++ g) +++ h)) ) : SailM (BitVec 64) )
  let imm : (BitVec datasize) := (BitVec.replicateBits imm64 (Int.ediv datasize 64))
  (execute_aarch64_instrs_vector_logical datasize imm operation rd)

def decode_bif_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (opc2 : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 8
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let op ← (( do (undefined_VBitOp ()) ) : SailM VBitOp )
  let op : VBitOp :=
    match (opc2 : BitVec 2) with
    | 0b00 => VBitOp_VEOR
    | 0b01 => VBitOp_VBSL
    | 0b10 => VBitOp_VBIT
    | _ => VBitOp_VBIF
  let op := op
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor d datasize m n op)

def decode_bit_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (opc2 : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 8
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let op ← (( do (undefined_VBitOp ()) ) : SailM VBitOp )
  let op : VBitOp :=
    match (opc2 : BitVec 2) with
    | 0b00 => VBitOp_VEOR
    | 0b01 => VBitOp_VBSL
    | 0b10 => VBitOp_VBIT
    | _ => VBitOp_VBIF
  let op := op
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor d datasize m n op)

def decode_bsl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (opc2 : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 8
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let op ← (( do (undefined_VBitOp ()) ) : SailM VBitOp )
  let op : VBitOp :=
    match (opc2 : BitVec 2) with
    | 0b00 => VBitOp_VEOR
    | 0b01 => VBitOp_VBSL
    | 0b10 => VBitOp_VBIT
    | _ => VBitOp_VBIF
  let op := op
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor d datasize m n op)

def decode_eor_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (opc2 : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 8
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let op ← (( do (undefined_VBitOp ()) ) : SailM VBitOp )
  let op : VBitOp :=
    match (opc2 : BitVec 2) with
    | 0b00 => VBitOp_VEOR
    | 0b01 => VBitOp_VBSL
    | 0b10 => VBitOp_VBIT
    | _ => VBitOp_VBIF
  let op := op
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor d datasize m n op)

def decode_brk_aarch64_instrs_system_exceptions_debug_breakpoint (imm16 : (BitVec 16)) : SailM Unit := do
  let comment : (BitVec 16) := imm16
  if ((← (HaveBTIExt ())) : Bool)
  then (SetBTypeCompatible true)
  else (pure ())
  (execute_aarch64_instrs_system_exceptions_debug_breakpoint comment)

def decode_bti_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp ()) ) : SailM SystemHintOp )
  let op ← (( do
    let b__0 := (CRm +++ op2)
    if ((b__0 == (0b0000000#7 : (BitVec 7))) : Bool)
    then (pure SystemHintOp_NOP)
    else
      (do
        if ((b__0 == (0b0000001#7 : (BitVec 7))) : Bool)
        then (pure SystemHintOp_YIELD)
        else
          (do
            if ((b__0 == (0b0000010#7 : (BitVec 7))) : Bool)
            then (pure SystemHintOp_WFE)
            else
              (do
                if ((b__0 == (0b0000011#7 : (BitVec 7))) : Bool)
                then (pure SystemHintOp_WFI)
                else
                  (do
                    if ((b__0 == (0b0000100#7 : (BitVec 7))) : Bool)
                    then (pure SystemHintOp_SEV)
                    else
                      (do
                        if ((b__0 == (0b0000101#7 : (BitVec 7))) : Bool)
                        then (pure SystemHintOp_SEVL)
                        else
                          (do
                            if ((b__0 == (0b0000110#7 : (BitVec 7))) : Bool)
                            then
                              (do
                                if ((! (← (HaveDGHExt ()))) : Bool)
                                then (EndOfInstruction ())
                                else (pure ())
                                (pure SystemHintOp_DGH))
                            else
                              (do
                                if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                then sailThrow ((Error_See "XPACLRI"))
                                else
                                  (do
                                    if (((Sail.BitVec.extractLsb b__0 6 3) == (0x1#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        match (op2 : BitVec 3) with
                                        | 0b000 => (sailThrow ((Error_See "PACIA1716")) : SailM Unit)
                                        | 0b010 => (sailThrow ((Error_See "PACIB1716")) : SailM Unit)
                                        | 0b100 => (sailThrow ((Error_See "AUTIA1716")) : SailM Unit)
                                        | 0b110 => (sailThrow ((Error_See "AUTIB1716")) : SailM Unit)
                                        | _ => (EndOfInstruction ())
                                        (pure op))
                                    else
                                      (do
                                        if ((b__0 == (0b0010000#7 : (BitVec 7))) : Bool)
                                        then
                                          (do
                                            if ((! (← (HaveRASExt ()))) : Bool)
                                            then (EndOfInstruction ())
                                            else (pure ())
                                            (pure SystemHintOp_ESB))
                                        else
                                          (do
                                            if ((b__0 == (0b0010001#7 : (BitVec 7))) : Bool)
                                            then
                                              (do
                                                if ((! (← (HaveStatisticalProfiling ()))) : Bool)
                                                then (EndOfInstruction ())
                                                else (pure ())
                                                (pure SystemHintOp_PSB))
                                            else
                                              (do
                                                if ((b__0 == (0b0010010#7 : (BitVec 7))) : Bool)
                                                then
                                                  (do
                                                    if ((! (← (HaveSelfHostedTrace ()))) : Bool)
                                                    then (EndOfInstruction ())
                                                    else (pure ())
                                                    (pure SystemHintOp_TSB))
                                                else
                                                  (do
                                                    if ((b__0 == (0b0010011#7 : (BitVec 7))) : Bool)
                                                    then
                                                      (do
                                                        if ((! (← (IsFeatureImplemented FEAT_GCS))) : Bool)
                                                        then (EndOfInstruction ())
                                                        else (pure ())
                                                        (pure SystemHintOp_GCSB))
                                                    else
                                                      (do
                                                        if ((b__0 == (0b0010100#7 : (BitVec 7))) : Bool)
                                                        then (pure SystemHintOp_CSDB)
                                                        else
                                                          (do
                                                            if ((b__0 == (0b0010110#7 : (BitVec 7))) : Bool)
                                                            then
                                                              (do
                                                                if ((! (← (HaveFeatCLRBHB ()))) : Bool)
                                                                then (EndOfInstruction ())
                                                                else (pure ())
                                                                (pure SystemHintOp_CLRBHB))
                                                            else
                                                              (do
                                                                if (((Sail.BitVec.extractLsb b__0 6 3) == (0x3#4 : (BitVec 4))) : Bool)
                                                                then
                                                                  (do
                                                                    match (op2 : BitVec 3) with
                                                                    | 0b000 => (sailThrow ((Error_See "PACIAZ")) : SailM Unit)
                                                                    | 0b001 => (sailThrow ((Error_See "PACIASP")) : SailM Unit)
                                                                    | 0b010 => (sailThrow ((Error_See "PACIBZ")) : SailM Unit)
                                                                    | 0b011 => (sailThrow ((Error_See "PACIBSP")) : SailM Unit)
                                                                    | 0b100 => (sailThrow ((Error_See "AUTIAZ")) : SailM Unit)
                                                                    | 0b101 => (sailThrow ((Error_See "AUTIASP")) : SailM Unit)
                                                                    | 0b110 => (sailThrow ((Error_See "AUTIBZ")) : SailM Unit)
                                                                    | _ => (sailThrow ((Error_See "AUTIBSP")) : SailM Unit)
                                                                    (pure op))
                                                                else
                                                                  (do
                                                                    if ((((Sail.BitVec.extractLsb b__0 6 3) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                                                    then
                                                                      (do
                                                                        let op : SystemHintOp := SystemHintOp_BTI
                                                                        (SetBTypeCompatible (← (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1))))
                                                                        (pure op))
                                                                    else
                                                                      (do
                                                                        if ((b__0 == (0b0101000#7 : (BitVec 7))) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((! (← (IsFeatureImplemented FEAT_CHK))) : Bool)
                                                                            then (EndOfInstruction ())
                                                                            else (pure ())
                                                                            (pure SystemHintOp_CHKFEAT))
                                                                        else
                                                                          (do
                                                                            (EndOfInstruction ())
                                                                            (pure op))))))))))))))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)

def decode_chkfeat_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp ()) ) : SailM SystemHintOp )
  let op ← (( do
    let b__0 := (CRm +++ op2)
    if ((b__0 == (0b0000000#7 : (BitVec 7))) : Bool)
    then (pure SystemHintOp_NOP)
    else
      (do
        if ((b__0 == (0b0000001#7 : (BitVec 7))) : Bool)
        then (pure SystemHintOp_YIELD)
        else
          (do
            if ((b__0 == (0b0000010#7 : (BitVec 7))) : Bool)
            then (pure SystemHintOp_WFE)
            else
              (do
                if ((b__0 == (0b0000011#7 : (BitVec 7))) : Bool)
                then (pure SystemHintOp_WFI)
                else
                  (do
                    if ((b__0 == (0b0000100#7 : (BitVec 7))) : Bool)
                    then (pure SystemHintOp_SEV)
                    else
                      (do
                        if ((b__0 == (0b0000101#7 : (BitVec 7))) : Bool)
                        then (pure SystemHintOp_SEVL)
                        else
                          (do
                            if ((b__0 == (0b0000110#7 : (BitVec 7))) : Bool)
                            then
                              (do
                                if ((! (← (HaveDGHExt ()))) : Bool)
                                then (EndOfInstruction ())
                                else (pure ())
                                (pure SystemHintOp_DGH))
                            else
                              (do
                                if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                then sailThrow ((Error_See "XPACLRI"))
                                else
                                  (do
                                    if (((Sail.BitVec.extractLsb b__0 6 3) == (0x1#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        match (op2 : BitVec 3) with
                                        | 0b000 => (sailThrow ((Error_See "PACIA1716")) : SailM Unit)
                                        | 0b010 => (sailThrow ((Error_See "PACIB1716")) : SailM Unit)
                                        | 0b100 => (sailThrow ((Error_See "AUTIA1716")) : SailM Unit)
                                        | 0b110 => (sailThrow ((Error_See "AUTIB1716")) : SailM Unit)
                                        | _ => (EndOfInstruction ())
                                        (pure op))
                                    else
                                      (do
                                        if ((b__0 == (0b0010000#7 : (BitVec 7))) : Bool)
                                        then
                                          (do
                                            if ((! (← (HaveRASExt ()))) : Bool)
                                            then (EndOfInstruction ())
                                            else (pure ())
                                            (pure SystemHintOp_ESB))
                                        else
                                          (do
                                            if ((b__0 == (0b0010001#7 : (BitVec 7))) : Bool)
                                            then
                                              (do
                                                if ((! (← (HaveStatisticalProfiling ()))) : Bool)
                                                then (EndOfInstruction ())
                                                else (pure ())
                                                (pure SystemHintOp_PSB))
                                            else
                                              (do
                                                if ((b__0 == (0b0010010#7 : (BitVec 7))) : Bool)
                                                then
                                                  (do
                                                    if ((! (← (HaveSelfHostedTrace ()))) : Bool)
                                                    then (EndOfInstruction ())
                                                    else (pure ())
                                                    (pure SystemHintOp_TSB))
                                                else
                                                  (do
                                                    if ((b__0 == (0b0010011#7 : (BitVec 7))) : Bool)
                                                    then
                                                      (do
                                                        if ((! (← (IsFeatureImplemented FEAT_GCS))) : Bool)
                                                        then (EndOfInstruction ())
                                                        else (pure ())
                                                        (pure SystemHintOp_GCSB))
                                                    else
                                                      (do
                                                        if ((b__0 == (0b0010100#7 : (BitVec 7))) : Bool)
                                                        then (pure SystemHintOp_CSDB)
                                                        else
                                                          (do
                                                            if ((b__0 == (0b0010110#7 : (BitVec 7))) : Bool)
                                                            then
                                                              (do
                                                                if ((! (← (HaveFeatCLRBHB ()))) : Bool)
                                                                then (EndOfInstruction ())
                                                                else (pure ())
                                                                (pure SystemHintOp_CLRBHB))
                                                            else
                                                              (do
                                                                if (((Sail.BitVec.extractLsb b__0 6 3) == (0x3#4 : (BitVec 4))) : Bool)
                                                                then
                                                                  (do
                                                                    match (op2 : BitVec 3) with
                                                                    | 0b000 => (sailThrow ((Error_See "PACIAZ")) : SailM Unit)
                                                                    | 0b001 => (sailThrow ((Error_See "PACIASP")) : SailM Unit)
                                                                    | 0b010 => (sailThrow ((Error_See "PACIBZ")) : SailM Unit)
                                                                    | 0b011 => (sailThrow ((Error_See "PACIBSP")) : SailM Unit)
                                                                    | 0b100 => (sailThrow ((Error_See "AUTIAZ")) : SailM Unit)
                                                                    | 0b101 => (sailThrow ((Error_See "AUTIASP")) : SailM Unit)
                                                                    | 0b110 => (sailThrow ((Error_See "AUTIBZ")) : SailM Unit)
                                                                    | _ => (sailThrow ((Error_See "AUTIBSP")) : SailM Unit)
                                                                    (pure op))
                                                                else
                                                                  (do
                                                                    if ((((Sail.BitVec.extractLsb b__0 6 3) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                                                    then
                                                                      (do
                                                                        let op : SystemHintOp := SystemHintOp_BTI
                                                                        (SetBTypeCompatible (← (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1))))
                                                                        (pure op))
                                                                    else
                                                                      (do
                                                                        if ((b__0 == (0b0101000#7 : (BitVec 7))) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((! (← (IsFeatureImplemented FEAT_CHK))) : Bool)
                                                                            then (EndOfInstruction ())
                                                                            else (pure ())
                                                                            (pure SystemHintOp_CHKFEAT))
                                                                        else
                                                                          (do
                                                                            (EndOfInstruction ())
                                                                            (pure op))))))))))))))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)

def decode_clrbhb_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp ()) ) : SailM SystemHintOp )
  let op ← (( do
    let b__0 := (CRm +++ op2)
    if ((b__0 == (0b0000000#7 : (BitVec 7))) : Bool)
    then (pure SystemHintOp_NOP)
    else
      (do
        if ((b__0 == (0b0000001#7 : (BitVec 7))) : Bool)
        then (pure SystemHintOp_YIELD)
        else
          (do
            if ((b__0 == (0b0000010#7 : (BitVec 7))) : Bool)
            then (pure SystemHintOp_WFE)
            else
              (do
                if ((b__0 == (0b0000011#7 : (BitVec 7))) : Bool)
                then (pure SystemHintOp_WFI)
                else
                  (do
                    if ((b__0 == (0b0000100#7 : (BitVec 7))) : Bool)
                    then (pure SystemHintOp_SEV)
                    else
                      (do
                        if ((b__0 == (0b0000101#7 : (BitVec 7))) : Bool)
                        then (pure SystemHintOp_SEVL)
                        else
                          (do
                            if ((b__0 == (0b0000110#7 : (BitVec 7))) : Bool)
                            then
                              (do
                                if ((! (← (HaveDGHExt ()))) : Bool)
                                then (EndOfInstruction ())
                                else (pure ())
                                (pure SystemHintOp_DGH))
                            else
                              (do
                                if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                then sailThrow ((Error_See "XPACLRI"))
                                else
                                  (do
                                    if (((Sail.BitVec.extractLsb b__0 6 3) == (0x1#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        match (op2 : BitVec 3) with
                                        | 0b000 => (sailThrow ((Error_See "PACIA1716")) : SailM Unit)
                                        | 0b010 => (sailThrow ((Error_See "PACIB1716")) : SailM Unit)
                                        | 0b100 => (sailThrow ((Error_See "AUTIA1716")) : SailM Unit)
                                        | 0b110 => (sailThrow ((Error_See "AUTIB1716")) : SailM Unit)
                                        | _ => (EndOfInstruction ())
                                        (pure op))
                                    else
                                      (do
                                        if ((b__0 == (0b0010000#7 : (BitVec 7))) : Bool)
                                        then
                                          (do
                                            if ((! (← (HaveRASExt ()))) : Bool)
                                            then (EndOfInstruction ())
                                            else (pure ())
                                            (pure SystemHintOp_ESB))
                                        else
                                          (do
                                            if ((b__0 == (0b0010001#7 : (BitVec 7))) : Bool)
                                            then
                                              (do
                                                if ((! (← (HaveStatisticalProfiling ()))) : Bool)
                                                then (EndOfInstruction ())
                                                else (pure ())
                                                (pure SystemHintOp_PSB))
                                            else
                                              (do
                                                if ((b__0 == (0b0010010#7 : (BitVec 7))) : Bool)
                                                then
                                                  (do
                                                    if ((! (← (HaveSelfHostedTrace ()))) : Bool)
                                                    then (EndOfInstruction ())
                                                    else (pure ())
                                                    (pure SystemHintOp_TSB))
                                                else
                                                  (do
                                                    if ((b__0 == (0b0010011#7 : (BitVec 7))) : Bool)
                                                    then
                                                      (do
                                                        if ((! (← (IsFeatureImplemented FEAT_GCS))) : Bool)
                                                        then (EndOfInstruction ())
                                                        else (pure ())
                                                        (pure SystemHintOp_GCSB))
                                                    else
                                                      (do
                                                        if ((b__0 == (0b0010100#7 : (BitVec 7))) : Bool)
                                                        then (pure SystemHintOp_CSDB)
                                                        else
                                                          (do
                                                            if ((b__0 == (0b0010110#7 : (BitVec 7))) : Bool)
                                                            then
                                                              (do
                                                                if ((! (← (HaveFeatCLRBHB ()))) : Bool)
                                                                then (EndOfInstruction ())
                                                                else (pure ())
                                                                (pure SystemHintOp_CLRBHB))
                                                            else
                                                              (do
                                                                if (((Sail.BitVec.extractLsb b__0 6 3) == (0x3#4 : (BitVec 4))) : Bool)
                                                                then
                                                                  (do
                                                                    match (op2 : BitVec 3) with
                                                                    | 0b000 => (sailThrow ((Error_See "PACIAZ")) : SailM Unit)
                                                                    | 0b001 => (sailThrow ((Error_See "PACIASP")) : SailM Unit)
                                                                    | 0b010 => (sailThrow ((Error_See "PACIBZ")) : SailM Unit)
                                                                    | 0b011 => (sailThrow ((Error_See "PACIBSP")) : SailM Unit)
                                                                    | 0b100 => (sailThrow ((Error_See "AUTIAZ")) : SailM Unit)
                                                                    | 0b101 => (sailThrow ((Error_See "AUTIASP")) : SailM Unit)
                                                                    | 0b110 => (sailThrow ((Error_See "AUTIBZ")) : SailM Unit)
                                                                    | _ => (sailThrow ((Error_See "AUTIBSP")) : SailM Unit)
                                                                    (pure op))
                                                                else
                                                                  (do
                                                                    if ((((Sail.BitVec.extractLsb b__0 6 3) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                                                    then
                                                                      (do
                                                                        let op : SystemHintOp := SystemHintOp_BTI
                                                                        (SetBTypeCompatible (← (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1))))
                                                                        (pure op))
                                                                    else
                                                                      (do
                                                                        if ((b__0 == (0b0101000#7 : (BitVec 7))) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((! (← (IsFeatureImplemented FEAT_CHK))) : Bool)
                                                                            then (EndOfInstruction ())
                                                                            else (pure ())
                                                                            (pure SystemHintOp_CHKFEAT))
                                                                        else
                                                                          (do
                                                                            (EndOfInstruction ())
                                                                            (pure op))))))))))))))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)

def decode_csdb_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp ()) ) : SailM SystemHintOp )
  let op ← (( do
    let b__0 := (CRm +++ op2)
    if ((b__0 == (0b0000000#7 : (BitVec 7))) : Bool)
    then (pure SystemHintOp_NOP)
    else
      (do
        if ((b__0 == (0b0000001#7 : (BitVec 7))) : Bool)
        then (pure SystemHintOp_YIELD)
        else
          (do
            if ((b__0 == (0b0000010#7 : (BitVec 7))) : Bool)
            then (pure SystemHintOp_WFE)
            else
              (do
                if ((b__0 == (0b0000011#7 : (BitVec 7))) : Bool)
                then (pure SystemHintOp_WFI)
                else
                  (do
                    if ((b__0 == (0b0000100#7 : (BitVec 7))) : Bool)
                    then (pure SystemHintOp_SEV)
                    else
                      (do
                        if ((b__0 == (0b0000101#7 : (BitVec 7))) : Bool)
                        then (pure SystemHintOp_SEVL)
                        else
                          (do
                            if ((b__0 == (0b0000110#7 : (BitVec 7))) : Bool)
                            then
                              (do
                                if ((! (← (HaveDGHExt ()))) : Bool)
                                then (EndOfInstruction ())
                                else (pure ())
                                (pure SystemHintOp_DGH))
                            else
                              (do
                                if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                then sailThrow ((Error_See "XPACLRI"))
                                else
                                  (do
                                    if (((Sail.BitVec.extractLsb b__0 6 3) == (0x1#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        match (op2 : BitVec 3) with
                                        | 0b000 => (sailThrow ((Error_See "PACIA1716")) : SailM Unit)
                                        | 0b010 => (sailThrow ((Error_See "PACIB1716")) : SailM Unit)
                                        | 0b100 => (sailThrow ((Error_See "AUTIA1716")) : SailM Unit)
                                        | 0b110 => (sailThrow ((Error_See "AUTIB1716")) : SailM Unit)
                                        | _ => (EndOfInstruction ())
                                        (pure op))
                                    else
                                      (do
                                        if ((b__0 == (0b0010000#7 : (BitVec 7))) : Bool)
                                        then
                                          (do
                                            if ((! (← (HaveRASExt ()))) : Bool)
                                            then (EndOfInstruction ())
                                            else (pure ())
                                            (pure SystemHintOp_ESB))
                                        else
                                          (do
                                            if ((b__0 == (0b0010001#7 : (BitVec 7))) : Bool)
                                            then
                                              (do
                                                if ((! (← (HaveStatisticalProfiling ()))) : Bool)
                                                then (EndOfInstruction ())
                                                else (pure ())
                                                (pure SystemHintOp_PSB))
                                            else
                                              (do
                                                if ((b__0 == (0b0010010#7 : (BitVec 7))) : Bool)
                                                then
                                                  (do
                                                    if ((! (← (HaveSelfHostedTrace ()))) : Bool)
                                                    then (EndOfInstruction ())
                                                    else (pure ())
                                                    (pure SystemHintOp_TSB))
                                                else
                                                  (do
                                                    if ((b__0 == (0b0010011#7 : (BitVec 7))) : Bool)
                                                    then
                                                      (do
                                                        if ((! (← (IsFeatureImplemented FEAT_GCS))) : Bool)
                                                        then (EndOfInstruction ())
                                                        else (pure ())
                                                        (pure SystemHintOp_GCSB))
                                                    else
                                                      (do
                                                        if ((b__0 == (0b0010100#7 : (BitVec 7))) : Bool)
                                                        then (pure SystemHintOp_CSDB)
                                                        else
                                                          (do
                                                            if ((b__0 == (0b0010110#7 : (BitVec 7))) : Bool)
                                                            then
                                                              (do
                                                                if ((! (← (HaveFeatCLRBHB ()))) : Bool)
                                                                then (EndOfInstruction ())
                                                                else (pure ())
                                                                (pure SystemHintOp_CLRBHB))
                                                            else
                                                              (do
                                                                if (((Sail.BitVec.extractLsb b__0 6 3) == (0x3#4 : (BitVec 4))) : Bool)
                                                                then
                                                                  (do
                                                                    match (op2 : BitVec 3) with
                                                                    | 0b000 => (sailThrow ((Error_See "PACIAZ")) : SailM Unit)
                                                                    | 0b001 => (sailThrow ((Error_See "PACIASP")) : SailM Unit)
                                                                    | 0b010 => (sailThrow ((Error_See "PACIBZ")) : SailM Unit)
                                                                    | 0b011 => (sailThrow ((Error_See "PACIBSP")) : SailM Unit)
                                                                    | 0b100 => (sailThrow ((Error_See "AUTIAZ")) : SailM Unit)
                                                                    | 0b101 => (sailThrow ((Error_See "AUTIASP")) : SailM Unit)
                                                                    | 0b110 => (sailThrow ((Error_See "AUTIBZ")) : SailM Unit)
                                                                    | _ => (sailThrow ((Error_See "AUTIBSP")) : SailM Unit)
                                                                    (pure op))
                                                                else
                                                                  (do
                                                                    if ((((Sail.BitVec.extractLsb b__0 6 3) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                                                    then
                                                                      (do
                                                                        let op : SystemHintOp := SystemHintOp_BTI
                                                                        (SetBTypeCompatible (← (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1))))
                                                                        (pure op))
                                                                    else
                                                                      (do
                                                                        if ((b__0 == (0b0101000#7 : (BitVec 7))) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((! (← (IsFeatureImplemented FEAT_CHK))) : Bool)
                                                                            then (EndOfInstruction ())
                                                                            else (pure ())
                                                                            (pure SystemHintOp_CHKFEAT))
                                                                        else
                                                                          (do
                                                                            (EndOfInstruction ())
                                                                            (pure op))))))))))))))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)

def decode_dgh_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp ()) ) : SailM SystemHintOp )
  let op ← (( do
    let b__0 := (CRm +++ op2)
    if ((b__0 == (0b0000000#7 : (BitVec 7))) : Bool)
    then (pure SystemHintOp_NOP)
    else
      (do
        if ((b__0 == (0b0000001#7 : (BitVec 7))) : Bool)
        then (pure SystemHintOp_YIELD)
        else
          (do
            if ((b__0 == (0b0000010#7 : (BitVec 7))) : Bool)
            then (pure SystemHintOp_WFE)
            else
              (do
                if ((b__0 == (0b0000011#7 : (BitVec 7))) : Bool)
                then (pure SystemHintOp_WFI)
                else
                  (do
                    if ((b__0 == (0b0000100#7 : (BitVec 7))) : Bool)
                    then (pure SystemHintOp_SEV)
                    else
                      (do
                        if ((b__0 == (0b0000101#7 : (BitVec 7))) : Bool)
                        then (pure SystemHintOp_SEVL)
                        else
                          (do
                            if ((b__0 == (0b0000110#7 : (BitVec 7))) : Bool)
                            then
                              (do
                                if ((! (← (HaveDGHExt ()))) : Bool)
                                then (EndOfInstruction ())
                                else (pure ())
                                (pure SystemHintOp_DGH))
                            else
                              (do
                                if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                then sailThrow ((Error_See "XPACLRI"))
                                else
                                  (do
                                    if (((Sail.BitVec.extractLsb b__0 6 3) == (0x1#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        match (op2 : BitVec 3) with
                                        | 0b000 => (sailThrow ((Error_See "PACIA1716")) : SailM Unit)
                                        | 0b010 => (sailThrow ((Error_See "PACIB1716")) : SailM Unit)
                                        | 0b100 => (sailThrow ((Error_See "AUTIA1716")) : SailM Unit)
                                        | 0b110 => (sailThrow ((Error_See "AUTIB1716")) : SailM Unit)
                                        | _ => (EndOfInstruction ())
                                        (pure op))
                                    else
                                      (do
                                        if ((b__0 == (0b0010000#7 : (BitVec 7))) : Bool)
                                        then
                                          (do
                                            if ((! (← (HaveRASExt ()))) : Bool)
                                            then (EndOfInstruction ())
                                            else (pure ())
                                            (pure SystemHintOp_ESB))
                                        else
                                          (do
                                            if ((b__0 == (0b0010001#7 : (BitVec 7))) : Bool)
                                            then
                                              (do
                                                if ((! (← (HaveStatisticalProfiling ()))) : Bool)
                                                then (EndOfInstruction ())
                                                else (pure ())
                                                (pure SystemHintOp_PSB))
                                            else
                                              (do
                                                if ((b__0 == (0b0010010#7 : (BitVec 7))) : Bool)
                                                then
                                                  (do
                                                    if ((! (← (HaveSelfHostedTrace ()))) : Bool)
                                                    then (EndOfInstruction ())
                                                    else (pure ())
                                                    (pure SystemHintOp_TSB))
                                                else
                                                  (do
                                                    if ((b__0 == (0b0010011#7 : (BitVec 7))) : Bool)
                                                    then
                                                      (do
                                                        if ((! (← (IsFeatureImplemented FEAT_GCS))) : Bool)
                                                        then (EndOfInstruction ())
                                                        else (pure ())
                                                        (pure SystemHintOp_GCSB))
                                                    else
                                                      (do
                                                        if ((b__0 == (0b0010100#7 : (BitVec 7))) : Bool)
                                                        then (pure SystemHintOp_CSDB)
                                                        else
                                                          (do
                                                            if ((b__0 == (0b0010110#7 : (BitVec 7))) : Bool)
                                                            then
                                                              (do
                                                                if ((! (← (HaveFeatCLRBHB ()))) : Bool)
                                                                then (EndOfInstruction ())
                                                                else (pure ())
                                                                (pure SystemHintOp_CLRBHB))
                                                            else
                                                              (do
                                                                if (((Sail.BitVec.extractLsb b__0 6 3) == (0x3#4 : (BitVec 4))) : Bool)
                                                                then
                                                                  (do
                                                                    match (op2 : BitVec 3) with
                                                                    | 0b000 => (sailThrow ((Error_See "PACIAZ")) : SailM Unit)
                                                                    | 0b001 => (sailThrow ((Error_See "PACIASP")) : SailM Unit)
                                                                    | 0b010 => (sailThrow ((Error_See "PACIBZ")) : SailM Unit)
                                                                    | 0b011 => (sailThrow ((Error_See "PACIBSP")) : SailM Unit)
                                                                    | 0b100 => (sailThrow ((Error_See "AUTIAZ")) : SailM Unit)
                                                                    | 0b101 => (sailThrow ((Error_See "AUTIASP")) : SailM Unit)
                                                                    | 0b110 => (sailThrow ((Error_See "AUTIBZ")) : SailM Unit)
                                                                    | _ => (sailThrow ((Error_See "AUTIBSP")) : SailM Unit)
                                                                    (pure op))
                                                                else
                                                                  (do
                                                                    if ((((Sail.BitVec.extractLsb b__0 6 3) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                                                    then
                                                                      (do
                                                                        let op : SystemHintOp := SystemHintOp_BTI
                                                                        (SetBTypeCompatible (← (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1))))
                                                                        (pure op))
                                                                    else
                                                                      (do
                                                                        if ((b__0 == (0b0101000#7 : (BitVec 7))) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((! (← (IsFeatureImplemented FEAT_CHK))) : Bool)
                                                                            then (EndOfInstruction ())
                                                                            else (pure ())
                                                                            (pure SystemHintOp_CHKFEAT))
                                                                        else
                                                                          (do
                                                                            (EndOfInstruction ())
                                                                            (pure op))))))))))))))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)

def decode_esb_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp ()) ) : SailM SystemHintOp )
  let op ← (( do
    let b__0 := (CRm +++ op2)
    if ((b__0 == (0b0000000#7 : (BitVec 7))) : Bool)
    then (pure SystemHintOp_NOP)
    else
      (do
        if ((b__0 == (0b0000001#7 : (BitVec 7))) : Bool)
        then (pure SystemHintOp_YIELD)
        else
          (do
            if ((b__0 == (0b0000010#7 : (BitVec 7))) : Bool)
            then (pure SystemHintOp_WFE)
            else
              (do
                if ((b__0 == (0b0000011#7 : (BitVec 7))) : Bool)
                then (pure SystemHintOp_WFI)
                else
                  (do
                    if ((b__0 == (0b0000100#7 : (BitVec 7))) : Bool)
                    then (pure SystemHintOp_SEV)
                    else
                      (do
                        if ((b__0 == (0b0000101#7 : (BitVec 7))) : Bool)
                        then (pure SystemHintOp_SEVL)
                        else
                          (do
                            if ((b__0 == (0b0000110#7 : (BitVec 7))) : Bool)
                            then
                              (do
                                if ((! (← (HaveDGHExt ()))) : Bool)
                                then (EndOfInstruction ())
                                else (pure ())
                                (pure SystemHintOp_DGH))
                            else
                              (do
                                if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                then sailThrow ((Error_See "XPACLRI"))
                                else
                                  (do
                                    if (((Sail.BitVec.extractLsb b__0 6 3) == (0x1#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        match (op2 : BitVec 3) with
                                        | 0b000 => (sailThrow ((Error_See "PACIA1716")) : SailM Unit)
                                        | 0b010 => (sailThrow ((Error_See "PACIB1716")) : SailM Unit)
                                        | 0b100 => (sailThrow ((Error_See "AUTIA1716")) : SailM Unit)
                                        | 0b110 => (sailThrow ((Error_See "AUTIB1716")) : SailM Unit)
                                        | _ => (EndOfInstruction ())
                                        (pure op))
                                    else
                                      (do
                                        if ((b__0 == (0b0010000#7 : (BitVec 7))) : Bool)
                                        then
                                          (do
                                            if ((! (← (HaveRASExt ()))) : Bool)
                                            then (EndOfInstruction ())
                                            else (pure ())
                                            (pure SystemHintOp_ESB))
                                        else
                                          (do
                                            if ((b__0 == (0b0010001#7 : (BitVec 7))) : Bool)
                                            then
                                              (do
                                                if ((! (← (HaveStatisticalProfiling ()))) : Bool)
                                                then (EndOfInstruction ())
                                                else (pure ())
                                                (pure SystemHintOp_PSB))
                                            else
                                              (do
                                                if ((b__0 == (0b0010010#7 : (BitVec 7))) : Bool)
                                                then
                                                  (do
                                                    if ((! (← (HaveSelfHostedTrace ()))) : Bool)
                                                    then (EndOfInstruction ())
                                                    else (pure ())
                                                    (pure SystemHintOp_TSB))
                                                else
                                                  (do
                                                    if ((b__0 == (0b0010011#7 : (BitVec 7))) : Bool)
                                                    then
                                                      (do
                                                        if ((! (← (IsFeatureImplemented FEAT_GCS))) : Bool)
                                                        then (EndOfInstruction ())
                                                        else (pure ())
                                                        (pure SystemHintOp_GCSB))
                                                    else
                                                      (do
                                                        if ((b__0 == (0b0010100#7 : (BitVec 7))) : Bool)
                                                        then (pure SystemHintOp_CSDB)
                                                        else
                                                          (do
                                                            if ((b__0 == (0b0010110#7 : (BitVec 7))) : Bool)
                                                            then
                                                              (do
                                                                if ((! (← (HaveFeatCLRBHB ()))) : Bool)
                                                                then (EndOfInstruction ())
                                                                else (pure ())
                                                                (pure SystemHintOp_CLRBHB))
                                                            else
                                                              (do
                                                                if (((Sail.BitVec.extractLsb b__0 6 3) == (0x3#4 : (BitVec 4))) : Bool)
                                                                then
                                                                  (do
                                                                    match (op2 : BitVec 3) with
                                                                    | 0b000 => (sailThrow ((Error_See "PACIAZ")) : SailM Unit)
                                                                    | 0b001 => (sailThrow ((Error_See "PACIASP")) : SailM Unit)
                                                                    | 0b010 => (sailThrow ((Error_See "PACIBZ")) : SailM Unit)
                                                                    | 0b011 => (sailThrow ((Error_See "PACIBSP")) : SailM Unit)
                                                                    | 0b100 => (sailThrow ((Error_See "AUTIAZ")) : SailM Unit)
                                                                    | 0b101 => (sailThrow ((Error_See "AUTIASP")) : SailM Unit)
                                                                    | 0b110 => (sailThrow ((Error_See "AUTIBZ")) : SailM Unit)
                                                                    | _ => (sailThrow ((Error_See "AUTIBSP")) : SailM Unit)
                                                                    (pure op))
                                                                else
                                                                  (do
                                                                    if ((((Sail.BitVec.extractLsb b__0 6 3) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                                                    then
                                                                      (do
                                                                        let op : SystemHintOp := SystemHintOp_BTI
                                                                        (SetBTypeCompatible (← (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1))))
                                                                        (pure op))
                                                                    else
                                                                      (do
                                                                        if ((b__0 == (0b0101000#7 : (BitVec 7))) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((! (← (IsFeatureImplemented FEAT_CHK))) : Bool)
                                                                            then (EndOfInstruction ())
                                                                            else (pure ())
                                                                            (pure SystemHintOp_CHKFEAT))
                                                                        else
                                                                          (do
                                                                            (EndOfInstruction ())
                                                                            (pure op))))))))))))))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)

def decode_gcsb_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp ()) ) : SailM SystemHintOp )
  let op ← (( do
    let b__0 := (CRm +++ op2)
    if ((b__0 == (0b0000000#7 : (BitVec 7))) : Bool)
    then (pure SystemHintOp_NOP)
    else
      (do
        if ((b__0 == (0b0000001#7 : (BitVec 7))) : Bool)
        then (pure SystemHintOp_YIELD)
        else
          (do
            if ((b__0 == (0b0000010#7 : (BitVec 7))) : Bool)
            then (pure SystemHintOp_WFE)
            else
              (do
                if ((b__0 == (0b0000011#7 : (BitVec 7))) : Bool)
                then (pure SystemHintOp_WFI)
                else
                  (do
                    if ((b__0 == (0b0000100#7 : (BitVec 7))) : Bool)
                    then (pure SystemHintOp_SEV)
                    else
                      (do
                        if ((b__0 == (0b0000101#7 : (BitVec 7))) : Bool)
                        then (pure SystemHintOp_SEVL)
                        else
                          (do
                            if ((b__0 == (0b0000110#7 : (BitVec 7))) : Bool)
                            then
                              (do
                                if ((! (← (HaveDGHExt ()))) : Bool)
                                then (EndOfInstruction ())
                                else (pure ())
                                (pure SystemHintOp_DGH))
                            else
                              (do
                                if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                then sailThrow ((Error_See "XPACLRI"))
                                else
                                  (do
                                    if (((Sail.BitVec.extractLsb b__0 6 3) == (0x1#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        match (op2 : BitVec 3) with
                                        | 0b000 => (sailThrow ((Error_See "PACIA1716")) : SailM Unit)
                                        | 0b010 => (sailThrow ((Error_See "PACIB1716")) : SailM Unit)
                                        | 0b100 => (sailThrow ((Error_See "AUTIA1716")) : SailM Unit)
                                        | 0b110 => (sailThrow ((Error_See "AUTIB1716")) : SailM Unit)
                                        | _ => (EndOfInstruction ())
                                        (pure op))
                                    else
                                      (do
                                        if ((b__0 == (0b0010000#7 : (BitVec 7))) : Bool)
                                        then
                                          (do
                                            if ((! (← (HaveRASExt ()))) : Bool)
                                            then (EndOfInstruction ())
                                            else (pure ())
                                            (pure SystemHintOp_ESB))
                                        else
                                          (do
                                            if ((b__0 == (0b0010001#7 : (BitVec 7))) : Bool)
                                            then
                                              (do
                                                if ((! (← (HaveStatisticalProfiling ()))) : Bool)
                                                then (EndOfInstruction ())
                                                else (pure ())
                                                (pure SystemHintOp_PSB))
                                            else
                                              (do
                                                if ((b__0 == (0b0010010#7 : (BitVec 7))) : Bool)
                                                then
                                                  (do
                                                    if ((! (← (HaveSelfHostedTrace ()))) : Bool)
                                                    then (EndOfInstruction ())
                                                    else (pure ())
                                                    (pure SystemHintOp_TSB))
                                                else
                                                  (do
                                                    if ((b__0 == (0b0010011#7 : (BitVec 7))) : Bool)
                                                    then
                                                      (do
                                                        if ((! (← (IsFeatureImplemented FEAT_GCS))) : Bool)
                                                        then (EndOfInstruction ())
                                                        else (pure ())
                                                        (pure SystemHintOp_GCSB))
                                                    else
                                                      (do
                                                        if ((b__0 == (0b0010100#7 : (BitVec 7))) : Bool)
                                                        then (pure SystemHintOp_CSDB)
                                                        else
                                                          (do
                                                            if ((b__0 == (0b0010110#7 : (BitVec 7))) : Bool)
                                                            then
                                                              (do
                                                                if ((! (← (HaveFeatCLRBHB ()))) : Bool)
                                                                then (EndOfInstruction ())
                                                                else (pure ())
                                                                (pure SystemHintOp_CLRBHB))
                                                            else
                                                              (do
                                                                if (((Sail.BitVec.extractLsb b__0 6 3) == (0x3#4 : (BitVec 4))) : Bool)
                                                                then
                                                                  (do
                                                                    match (op2 : BitVec 3) with
                                                                    | 0b000 => (sailThrow ((Error_See "PACIAZ")) : SailM Unit)
                                                                    | 0b001 => (sailThrow ((Error_See "PACIASP")) : SailM Unit)
                                                                    | 0b010 => (sailThrow ((Error_See "PACIBZ")) : SailM Unit)
                                                                    | 0b011 => (sailThrow ((Error_See "PACIBSP")) : SailM Unit)
                                                                    | 0b100 => (sailThrow ((Error_See "AUTIAZ")) : SailM Unit)
                                                                    | 0b101 => (sailThrow ((Error_See "AUTIASP")) : SailM Unit)
                                                                    | 0b110 => (sailThrow ((Error_See "AUTIBZ")) : SailM Unit)
                                                                    | _ => (sailThrow ((Error_See "AUTIBSP")) : SailM Unit)
                                                                    (pure op))
                                                                else
                                                                  (do
                                                                    if ((((Sail.BitVec.extractLsb b__0 6 3) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                                                    then
                                                                      (do
                                                                        let op : SystemHintOp := SystemHintOp_BTI
                                                                        (SetBTypeCompatible (← (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1))))
                                                                        (pure op))
                                                                    else
                                                                      (do
                                                                        if ((b__0 == (0b0101000#7 : (BitVec 7))) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((! (← (IsFeatureImplemented FEAT_CHK))) : Bool)
                                                                            then (EndOfInstruction ())
                                                                            else (pure ())
                                                                            (pure SystemHintOp_CHKFEAT))
                                                                        else
                                                                          (do
                                                                            (EndOfInstruction ())
                                                                            (pure op))))))))))))))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)

def decode_hint_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp ()) ) : SailM SystemHintOp )
  let op ← (( do
    let b__0 := (CRm +++ op2)
    if ((b__0 == (0b0000000#7 : (BitVec 7))) : Bool)
    then (pure SystemHintOp_NOP)
    else
      (do
        if ((b__0 == (0b0000001#7 : (BitVec 7))) : Bool)
        then (pure SystemHintOp_YIELD)
        else
          (do
            if ((b__0 == (0b0000010#7 : (BitVec 7))) : Bool)
            then (pure SystemHintOp_WFE)
            else
              (do
                if ((b__0 == (0b0000011#7 : (BitVec 7))) : Bool)
                then (pure SystemHintOp_WFI)
                else
                  (do
                    if ((b__0 == (0b0000100#7 : (BitVec 7))) : Bool)
                    then (pure SystemHintOp_SEV)
                    else
                      (do
                        if ((b__0 == (0b0000101#7 : (BitVec 7))) : Bool)
                        then (pure SystemHintOp_SEVL)
                        else
                          (do
                            if ((b__0 == (0b0000110#7 : (BitVec 7))) : Bool)
                            then
                              (do
                                if ((! (← (HaveDGHExt ()))) : Bool)
                                then (EndOfInstruction ())
                                else (pure ())
                                (pure SystemHintOp_DGH))
                            else
                              (do
                                if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                then sailThrow ((Error_See "XPACLRI"))
                                else
                                  (do
                                    if (((Sail.BitVec.extractLsb b__0 6 3) == (0x1#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        match (op2 : BitVec 3) with
                                        | 0b000 => (sailThrow ((Error_See "PACIA1716")) : SailM Unit)
                                        | 0b010 => (sailThrow ((Error_See "PACIB1716")) : SailM Unit)
                                        | 0b100 => (sailThrow ((Error_See "AUTIA1716")) : SailM Unit)
                                        | 0b110 => (sailThrow ((Error_See "AUTIB1716")) : SailM Unit)
                                        | _ => (EndOfInstruction ())
                                        (pure op))
                                    else
                                      (do
                                        if ((b__0 == (0b0010000#7 : (BitVec 7))) : Bool)
                                        then
                                          (do
                                            if ((! (← (HaveRASExt ()))) : Bool)
                                            then (EndOfInstruction ())
                                            else (pure ())
                                            (pure SystemHintOp_ESB))
                                        else
                                          (do
                                            if ((b__0 == (0b0010001#7 : (BitVec 7))) : Bool)
                                            then
                                              (do
                                                if ((! (← (HaveStatisticalProfiling ()))) : Bool)
                                                then (EndOfInstruction ())
                                                else (pure ())
                                                (pure SystemHintOp_PSB))
                                            else
                                              (do
                                                if ((b__0 == (0b0010010#7 : (BitVec 7))) : Bool)
                                                then
                                                  (do
                                                    if ((! (← (HaveSelfHostedTrace ()))) : Bool)
                                                    then (EndOfInstruction ())
                                                    else (pure ())
                                                    (pure SystemHintOp_TSB))
                                                else
                                                  (do
                                                    if ((b__0 == (0b0010011#7 : (BitVec 7))) : Bool)
                                                    then
                                                      (do
                                                        if ((! (← (IsFeatureImplemented FEAT_GCS))) : Bool)
                                                        then (EndOfInstruction ())
                                                        else (pure ())
                                                        (pure SystemHintOp_GCSB))
                                                    else
                                                      (do
                                                        if ((b__0 == (0b0010100#7 : (BitVec 7))) : Bool)
                                                        then (pure SystemHintOp_CSDB)
                                                        else
                                                          (do
                                                            if ((b__0 == (0b0010110#7 : (BitVec 7))) : Bool)
                                                            then
                                                              (do
                                                                if ((! (← (HaveFeatCLRBHB ()))) : Bool)
                                                                then (EndOfInstruction ())
                                                                else (pure ())
                                                                (pure SystemHintOp_CLRBHB))
                                                            else
                                                              (do
                                                                if (((Sail.BitVec.extractLsb b__0 6 3) == (0x3#4 : (BitVec 4))) : Bool)
                                                                then
                                                                  (do
                                                                    match (op2 : BitVec 3) with
                                                                    | 0b000 => (sailThrow ((Error_See "PACIAZ")) : SailM Unit)
                                                                    | 0b001 => (sailThrow ((Error_See "PACIASP")) : SailM Unit)
                                                                    | 0b010 => (sailThrow ((Error_See "PACIBZ")) : SailM Unit)
                                                                    | 0b011 => (sailThrow ((Error_See "PACIBSP")) : SailM Unit)
                                                                    | 0b100 => (sailThrow ((Error_See "AUTIAZ")) : SailM Unit)
                                                                    | 0b101 => (sailThrow ((Error_See "AUTIASP")) : SailM Unit)
                                                                    | 0b110 => (sailThrow ((Error_See "AUTIBZ")) : SailM Unit)
                                                                    | _ => (sailThrow ((Error_See "AUTIBSP")) : SailM Unit)
                                                                    (pure op))
                                                                else
                                                                  (do
                                                                    if ((((Sail.BitVec.extractLsb b__0 6 3) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                                                    then
                                                                      (do
                                                                        let op : SystemHintOp := SystemHintOp_BTI
                                                                        (SetBTypeCompatible (← (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1))))
                                                                        (pure op))
                                                                    else
                                                                      (do
                                                                        if ((b__0 == (0b0101000#7 : (BitVec 7))) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((! (← (IsFeatureImplemented FEAT_CHK))) : Bool)
                                                                            then (EndOfInstruction ())
                                                                            else (pure ())
                                                                            (pure SystemHintOp_CHKFEAT))
                                                                        else
                                                                          (do
                                                                            (EndOfInstruction ())
                                                                            (pure op))))))))))))))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)

def decode_nop_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp ()) ) : SailM SystemHintOp )
  let op ← (( do
    let b__0 := (CRm +++ op2)
    if ((b__0 == (0b0000000#7 : (BitVec 7))) : Bool)
    then (pure SystemHintOp_NOP)
    else
      (do
        if ((b__0 == (0b0000001#7 : (BitVec 7))) : Bool)
        then (pure SystemHintOp_YIELD)
        else
          (do
            if ((b__0 == (0b0000010#7 : (BitVec 7))) : Bool)
            then (pure SystemHintOp_WFE)
            else
              (do
                if ((b__0 == (0b0000011#7 : (BitVec 7))) : Bool)
                then (pure SystemHintOp_WFI)
                else
                  (do
                    if ((b__0 == (0b0000100#7 : (BitVec 7))) : Bool)
                    then (pure SystemHintOp_SEV)
                    else
                      (do
                        if ((b__0 == (0b0000101#7 : (BitVec 7))) : Bool)
                        then (pure SystemHintOp_SEVL)
                        else
                          (do
                            if ((b__0 == (0b0000110#7 : (BitVec 7))) : Bool)
                            then
                              (do
                                if ((! (← (HaveDGHExt ()))) : Bool)
                                then (EndOfInstruction ())
                                else (pure ())
                                (pure SystemHintOp_DGH))
                            else
                              (do
                                if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                then sailThrow ((Error_See "XPACLRI"))
                                else
                                  (do
                                    if (((Sail.BitVec.extractLsb b__0 6 3) == (0x1#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        match (op2 : BitVec 3) with
                                        | 0b000 => (sailThrow ((Error_See "PACIA1716")) : SailM Unit)
                                        | 0b010 => (sailThrow ((Error_See "PACIB1716")) : SailM Unit)
                                        | 0b100 => (sailThrow ((Error_See "AUTIA1716")) : SailM Unit)
                                        | 0b110 => (sailThrow ((Error_See "AUTIB1716")) : SailM Unit)
                                        | _ => (EndOfInstruction ())
                                        (pure op))
                                    else
                                      (do
                                        if ((b__0 == (0b0010000#7 : (BitVec 7))) : Bool)
                                        then
                                          (do
                                            if ((! (← (HaveRASExt ()))) : Bool)
                                            then (EndOfInstruction ())
                                            else (pure ())
                                            (pure SystemHintOp_ESB))
                                        else
                                          (do
                                            if ((b__0 == (0b0010001#7 : (BitVec 7))) : Bool)
                                            then
                                              (do
                                                if ((! (← (HaveStatisticalProfiling ()))) : Bool)
                                                then (EndOfInstruction ())
                                                else (pure ())
                                                (pure SystemHintOp_PSB))
                                            else
                                              (do
                                                if ((b__0 == (0b0010010#7 : (BitVec 7))) : Bool)
                                                then
                                                  (do
                                                    if ((! (← (HaveSelfHostedTrace ()))) : Bool)
                                                    then (EndOfInstruction ())
                                                    else (pure ())
                                                    (pure SystemHintOp_TSB))
                                                else
                                                  (do
                                                    if ((b__0 == (0b0010011#7 : (BitVec 7))) : Bool)
                                                    then
                                                      (do
                                                        if ((! (← (IsFeatureImplemented FEAT_GCS))) : Bool)
                                                        then (EndOfInstruction ())
                                                        else (pure ())
                                                        (pure SystemHintOp_GCSB))
                                                    else
                                                      (do
                                                        if ((b__0 == (0b0010100#7 : (BitVec 7))) : Bool)
                                                        then (pure SystemHintOp_CSDB)
                                                        else
                                                          (do
                                                            if ((b__0 == (0b0010110#7 : (BitVec 7))) : Bool)
                                                            then
                                                              (do
                                                                if ((! (← (HaveFeatCLRBHB ()))) : Bool)
                                                                then (EndOfInstruction ())
                                                                else (pure ())
                                                                (pure SystemHintOp_CLRBHB))
                                                            else
                                                              (do
                                                                if (((Sail.BitVec.extractLsb b__0 6 3) == (0x3#4 : (BitVec 4))) : Bool)
                                                                then
                                                                  (do
                                                                    match (op2 : BitVec 3) with
                                                                    | 0b000 => (sailThrow ((Error_See "PACIAZ")) : SailM Unit)
                                                                    | 0b001 => (sailThrow ((Error_See "PACIASP")) : SailM Unit)
                                                                    | 0b010 => (sailThrow ((Error_See "PACIBZ")) : SailM Unit)
                                                                    | 0b011 => (sailThrow ((Error_See "PACIBSP")) : SailM Unit)
                                                                    | 0b100 => (sailThrow ((Error_See "AUTIAZ")) : SailM Unit)
                                                                    | 0b101 => (sailThrow ((Error_See "AUTIASP")) : SailM Unit)
                                                                    | 0b110 => (sailThrow ((Error_See "AUTIBZ")) : SailM Unit)
                                                                    | _ => (sailThrow ((Error_See "AUTIBSP")) : SailM Unit)
                                                                    (pure op))
                                                                else
                                                                  (do
                                                                    if ((((Sail.BitVec.extractLsb b__0 6 3) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                                                    then
                                                                      (do
                                                                        let op : SystemHintOp := SystemHintOp_BTI
                                                                        (SetBTypeCompatible (← (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1))))
                                                                        (pure op))
                                                                    else
                                                                      (do
                                                                        if ((b__0 == (0b0101000#7 : (BitVec 7))) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((! (← (IsFeatureImplemented FEAT_CHK))) : Bool)
                                                                            then (EndOfInstruction ())
                                                                            else (pure ())
                                                                            (pure SystemHintOp_CHKFEAT))
                                                                        else
                                                                          (do
                                                                            (EndOfInstruction ())
                                                                            (pure op))))))))))))))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)

def decode_psb_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp ()) ) : SailM SystemHintOp )
  let op ← (( do
    let b__0 := (CRm +++ op2)
    if ((b__0 == (0b0000000#7 : (BitVec 7))) : Bool)
    then (pure SystemHintOp_NOP)
    else
      (do
        if ((b__0 == (0b0000001#7 : (BitVec 7))) : Bool)
        then (pure SystemHintOp_YIELD)
        else
          (do
            if ((b__0 == (0b0000010#7 : (BitVec 7))) : Bool)
            then (pure SystemHintOp_WFE)
            else
              (do
                if ((b__0 == (0b0000011#7 : (BitVec 7))) : Bool)
                then (pure SystemHintOp_WFI)
                else
                  (do
                    if ((b__0 == (0b0000100#7 : (BitVec 7))) : Bool)
                    then (pure SystemHintOp_SEV)
                    else
                      (do
                        if ((b__0 == (0b0000101#7 : (BitVec 7))) : Bool)
                        then (pure SystemHintOp_SEVL)
                        else
                          (do
                            if ((b__0 == (0b0000110#7 : (BitVec 7))) : Bool)
                            then
                              (do
                                if ((! (← (HaveDGHExt ()))) : Bool)
                                then (EndOfInstruction ())
                                else (pure ())
                                (pure SystemHintOp_DGH))
                            else
                              (do
                                if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                then sailThrow ((Error_See "XPACLRI"))
                                else
                                  (do
                                    if (((Sail.BitVec.extractLsb b__0 6 3) == (0x1#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        match (op2 : BitVec 3) with
                                        | 0b000 => (sailThrow ((Error_See "PACIA1716")) : SailM Unit)
                                        | 0b010 => (sailThrow ((Error_See "PACIB1716")) : SailM Unit)
                                        | 0b100 => (sailThrow ((Error_See "AUTIA1716")) : SailM Unit)
                                        | 0b110 => (sailThrow ((Error_See "AUTIB1716")) : SailM Unit)
                                        | _ => (EndOfInstruction ())
                                        (pure op))
                                    else
                                      (do
                                        if ((b__0 == (0b0010000#7 : (BitVec 7))) : Bool)
                                        then
                                          (do
                                            if ((! (← (HaveRASExt ()))) : Bool)
                                            then (EndOfInstruction ())
                                            else (pure ())
                                            (pure SystemHintOp_ESB))
                                        else
                                          (do
                                            if ((b__0 == (0b0010001#7 : (BitVec 7))) : Bool)
                                            then
                                              (do
                                                if ((! (← (HaveStatisticalProfiling ()))) : Bool)
                                                then (EndOfInstruction ())
                                                else (pure ())
                                                (pure SystemHintOp_PSB))
                                            else
                                              (do
                                                if ((b__0 == (0b0010010#7 : (BitVec 7))) : Bool)
                                                then
                                                  (do
                                                    if ((! (← (HaveSelfHostedTrace ()))) : Bool)
                                                    then (EndOfInstruction ())
                                                    else (pure ())
                                                    (pure SystemHintOp_TSB))
                                                else
                                                  (do
                                                    if ((b__0 == (0b0010011#7 : (BitVec 7))) : Bool)
                                                    then
                                                      (do
                                                        if ((! (← (IsFeatureImplemented FEAT_GCS))) : Bool)
                                                        then (EndOfInstruction ())
                                                        else (pure ())
                                                        (pure SystemHintOp_GCSB))
                                                    else
                                                      (do
                                                        if ((b__0 == (0b0010100#7 : (BitVec 7))) : Bool)
                                                        then (pure SystemHintOp_CSDB)
                                                        else
                                                          (do
                                                            if ((b__0 == (0b0010110#7 : (BitVec 7))) : Bool)
                                                            then
                                                              (do
                                                                if ((! (← (HaveFeatCLRBHB ()))) : Bool)
                                                                then (EndOfInstruction ())
                                                                else (pure ())
                                                                (pure SystemHintOp_CLRBHB))
                                                            else
                                                              (do
                                                                if (((Sail.BitVec.extractLsb b__0 6 3) == (0x3#4 : (BitVec 4))) : Bool)
                                                                then
                                                                  (do
                                                                    match (op2 : BitVec 3) with
                                                                    | 0b000 => (sailThrow ((Error_See "PACIAZ")) : SailM Unit)
                                                                    | 0b001 => (sailThrow ((Error_See "PACIASP")) : SailM Unit)
                                                                    | 0b010 => (sailThrow ((Error_See "PACIBZ")) : SailM Unit)
                                                                    | 0b011 => (sailThrow ((Error_See "PACIBSP")) : SailM Unit)
                                                                    | 0b100 => (sailThrow ((Error_See "AUTIAZ")) : SailM Unit)
                                                                    | 0b101 => (sailThrow ((Error_See "AUTIASP")) : SailM Unit)
                                                                    | 0b110 => (sailThrow ((Error_See "AUTIBZ")) : SailM Unit)
                                                                    | _ => (sailThrow ((Error_See "AUTIBSP")) : SailM Unit)
                                                                    (pure op))
                                                                else
                                                                  (do
                                                                    if ((((Sail.BitVec.extractLsb b__0 6 3) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                                                    then
                                                                      (do
                                                                        let op : SystemHintOp := SystemHintOp_BTI
                                                                        (SetBTypeCompatible (← (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1))))
                                                                        (pure op))
                                                                    else
                                                                      (do
                                                                        if ((b__0 == (0b0101000#7 : (BitVec 7))) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((! (← (IsFeatureImplemented FEAT_CHK))) : Bool)
                                                                            then (EndOfInstruction ())
                                                                            else (pure ())
                                                                            (pure SystemHintOp_CHKFEAT))
                                                                        else
                                                                          (do
                                                                            (EndOfInstruction ())
                                                                            (pure op))))))))))))))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)

def decode_sev_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp ()) ) : SailM SystemHintOp )
  let op ← (( do
    let b__0 := (CRm +++ op2)
    if ((b__0 == (0b0000000#7 : (BitVec 7))) : Bool)
    then (pure SystemHintOp_NOP)
    else
      (do
        if ((b__0 == (0b0000001#7 : (BitVec 7))) : Bool)
        then (pure SystemHintOp_YIELD)
        else
          (do
            if ((b__0 == (0b0000010#7 : (BitVec 7))) : Bool)
            then (pure SystemHintOp_WFE)
            else
              (do
                if ((b__0 == (0b0000011#7 : (BitVec 7))) : Bool)
                then (pure SystemHintOp_WFI)
                else
                  (do
                    if ((b__0 == (0b0000100#7 : (BitVec 7))) : Bool)
                    then (pure SystemHintOp_SEV)
                    else
                      (do
                        if ((b__0 == (0b0000101#7 : (BitVec 7))) : Bool)
                        then (pure SystemHintOp_SEVL)
                        else
                          (do
                            if ((b__0 == (0b0000110#7 : (BitVec 7))) : Bool)
                            then
                              (do
                                if ((! (← (HaveDGHExt ()))) : Bool)
                                then (EndOfInstruction ())
                                else (pure ())
                                (pure SystemHintOp_DGH))
                            else
                              (do
                                if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                then sailThrow ((Error_See "XPACLRI"))
                                else
                                  (do
                                    if (((Sail.BitVec.extractLsb b__0 6 3) == (0x1#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        match (op2 : BitVec 3) with
                                        | 0b000 => (sailThrow ((Error_See "PACIA1716")) : SailM Unit)
                                        | 0b010 => (sailThrow ((Error_See "PACIB1716")) : SailM Unit)
                                        | 0b100 => (sailThrow ((Error_See "AUTIA1716")) : SailM Unit)
                                        | 0b110 => (sailThrow ((Error_See "AUTIB1716")) : SailM Unit)
                                        | _ => (EndOfInstruction ())
                                        (pure op))
                                    else
                                      (do
                                        if ((b__0 == (0b0010000#7 : (BitVec 7))) : Bool)
                                        then
                                          (do
                                            if ((! (← (HaveRASExt ()))) : Bool)
                                            then (EndOfInstruction ())
                                            else (pure ())
                                            (pure SystemHintOp_ESB))
                                        else
                                          (do
                                            if ((b__0 == (0b0010001#7 : (BitVec 7))) : Bool)
                                            then
                                              (do
                                                if ((! (← (HaveStatisticalProfiling ()))) : Bool)
                                                then (EndOfInstruction ())
                                                else (pure ())
                                                (pure SystemHintOp_PSB))
                                            else
                                              (do
                                                if ((b__0 == (0b0010010#7 : (BitVec 7))) : Bool)
                                                then
                                                  (do
                                                    if ((! (← (HaveSelfHostedTrace ()))) : Bool)
                                                    then (EndOfInstruction ())
                                                    else (pure ())
                                                    (pure SystemHintOp_TSB))
                                                else
                                                  (do
                                                    if ((b__0 == (0b0010011#7 : (BitVec 7))) : Bool)
                                                    then
                                                      (do
                                                        if ((! (← (IsFeatureImplemented FEAT_GCS))) : Bool)
                                                        then (EndOfInstruction ())
                                                        else (pure ())
                                                        (pure SystemHintOp_GCSB))
                                                    else
                                                      (do
                                                        if ((b__0 == (0b0010100#7 : (BitVec 7))) : Bool)
                                                        then (pure SystemHintOp_CSDB)
                                                        else
                                                          (do
                                                            if ((b__0 == (0b0010110#7 : (BitVec 7))) : Bool)
                                                            then
                                                              (do
                                                                if ((! (← (HaveFeatCLRBHB ()))) : Bool)
                                                                then (EndOfInstruction ())
                                                                else (pure ())
                                                                (pure SystemHintOp_CLRBHB))
                                                            else
                                                              (do
                                                                if (((Sail.BitVec.extractLsb b__0 6 3) == (0x3#4 : (BitVec 4))) : Bool)
                                                                then
                                                                  (do
                                                                    match (op2 : BitVec 3) with
                                                                    | 0b000 => (sailThrow ((Error_See "PACIAZ")) : SailM Unit)
                                                                    | 0b001 => (sailThrow ((Error_See "PACIASP")) : SailM Unit)
                                                                    | 0b010 => (sailThrow ((Error_See "PACIBZ")) : SailM Unit)
                                                                    | 0b011 => (sailThrow ((Error_See "PACIBSP")) : SailM Unit)
                                                                    | 0b100 => (sailThrow ((Error_See "AUTIAZ")) : SailM Unit)
                                                                    | 0b101 => (sailThrow ((Error_See "AUTIASP")) : SailM Unit)
                                                                    | 0b110 => (sailThrow ((Error_See "AUTIBZ")) : SailM Unit)
                                                                    | _ => (sailThrow ((Error_See "AUTIBSP")) : SailM Unit)
                                                                    (pure op))
                                                                else
                                                                  (do
                                                                    if ((((Sail.BitVec.extractLsb b__0 6 3) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                                                    then
                                                                      (do
                                                                        let op : SystemHintOp := SystemHintOp_BTI
                                                                        (SetBTypeCompatible (← (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1))))
                                                                        (pure op))
                                                                    else
                                                                      (do
                                                                        if ((b__0 == (0b0101000#7 : (BitVec 7))) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((! (← (IsFeatureImplemented FEAT_CHK))) : Bool)
                                                                            then (EndOfInstruction ())
                                                                            else (pure ())
                                                                            (pure SystemHintOp_CHKFEAT))
                                                                        else
                                                                          (do
                                                                            (EndOfInstruction ())
                                                                            (pure op))))))))))))))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)

def decode_sevl_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp ()) ) : SailM SystemHintOp )
  let op ← (( do
    let b__0 := (CRm +++ op2)
    if ((b__0 == (0b0000000#7 : (BitVec 7))) : Bool)
    then (pure SystemHintOp_NOP)
    else
      (do
        if ((b__0 == (0b0000001#7 : (BitVec 7))) : Bool)
        then (pure SystemHintOp_YIELD)
        else
          (do
            if ((b__0 == (0b0000010#7 : (BitVec 7))) : Bool)
            then (pure SystemHintOp_WFE)
            else
              (do
                if ((b__0 == (0b0000011#7 : (BitVec 7))) : Bool)
                then (pure SystemHintOp_WFI)
                else
                  (do
                    if ((b__0 == (0b0000100#7 : (BitVec 7))) : Bool)
                    then (pure SystemHintOp_SEV)
                    else
                      (do
                        if ((b__0 == (0b0000101#7 : (BitVec 7))) : Bool)
                        then (pure SystemHintOp_SEVL)
                        else
                          (do
                            if ((b__0 == (0b0000110#7 : (BitVec 7))) : Bool)
                            then
                              (do
                                if ((! (← (HaveDGHExt ()))) : Bool)
                                then (EndOfInstruction ())
                                else (pure ())
                                (pure SystemHintOp_DGH))
                            else
                              (do
                                if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                then sailThrow ((Error_See "XPACLRI"))
                                else
                                  (do
                                    if (((Sail.BitVec.extractLsb b__0 6 3) == (0x1#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        match (op2 : BitVec 3) with
                                        | 0b000 => (sailThrow ((Error_See "PACIA1716")) : SailM Unit)
                                        | 0b010 => (sailThrow ((Error_See "PACIB1716")) : SailM Unit)
                                        | 0b100 => (sailThrow ((Error_See "AUTIA1716")) : SailM Unit)
                                        | 0b110 => (sailThrow ((Error_See "AUTIB1716")) : SailM Unit)
                                        | _ => (EndOfInstruction ())
                                        (pure op))
                                    else
                                      (do
                                        if ((b__0 == (0b0010000#7 : (BitVec 7))) : Bool)
                                        then
                                          (do
                                            if ((! (← (HaveRASExt ()))) : Bool)
                                            then (EndOfInstruction ())
                                            else (pure ())
                                            (pure SystemHintOp_ESB))
                                        else
                                          (do
                                            if ((b__0 == (0b0010001#7 : (BitVec 7))) : Bool)
                                            then
                                              (do
                                                if ((! (← (HaveStatisticalProfiling ()))) : Bool)
                                                then (EndOfInstruction ())
                                                else (pure ())
                                                (pure SystemHintOp_PSB))
                                            else
                                              (do
                                                if ((b__0 == (0b0010010#7 : (BitVec 7))) : Bool)
                                                then
                                                  (do
                                                    if ((! (← (HaveSelfHostedTrace ()))) : Bool)
                                                    then (EndOfInstruction ())
                                                    else (pure ())
                                                    (pure SystemHintOp_TSB))
                                                else
                                                  (do
                                                    if ((b__0 == (0b0010011#7 : (BitVec 7))) : Bool)
                                                    then
                                                      (do
                                                        if ((! (← (IsFeatureImplemented FEAT_GCS))) : Bool)
                                                        then (EndOfInstruction ())
                                                        else (pure ())
                                                        (pure SystemHintOp_GCSB))
                                                    else
                                                      (do
                                                        if ((b__0 == (0b0010100#7 : (BitVec 7))) : Bool)
                                                        then (pure SystemHintOp_CSDB)
                                                        else
                                                          (do
                                                            if ((b__0 == (0b0010110#7 : (BitVec 7))) : Bool)
                                                            then
                                                              (do
                                                                if ((! (← (HaveFeatCLRBHB ()))) : Bool)
                                                                then (EndOfInstruction ())
                                                                else (pure ())
                                                                (pure SystemHintOp_CLRBHB))
                                                            else
                                                              (do
                                                                if (((Sail.BitVec.extractLsb b__0 6 3) == (0x3#4 : (BitVec 4))) : Bool)
                                                                then
                                                                  (do
                                                                    match (op2 : BitVec 3) with
                                                                    | 0b000 => (sailThrow ((Error_See "PACIAZ")) : SailM Unit)
                                                                    | 0b001 => (sailThrow ((Error_See "PACIASP")) : SailM Unit)
                                                                    | 0b010 => (sailThrow ((Error_See "PACIBZ")) : SailM Unit)
                                                                    | 0b011 => (sailThrow ((Error_See "PACIBSP")) : SailM Unit)
                                                                    | 0b100 => (sailThrow ((Error_See "AUTIAZ")) : SailM Unit)
                                                                    | 0b101 => (sailThrow ((Error_See "AUTIASP")) : SailM Unit)
                                                                    | 0b110 => (sailThrow ((Error_See "AUTIBZ")) : SailM Unit)
                                                                    | _ => (sailThrow ((Error_See "AUTIBSP")) : SailM Unit)
                                                                    (pure op))
                                                                else
                                                                  (do
                                                                    if ((((Sail.BitVec.extractLsb b__0 6 3) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                                                    then
                                                                      (do
                                                                        let op : SystemHintOp := SystemHintOp_BTI
                                                                        (SetBTypeCompatible (← (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1))))
                                                                        (pure op))
                                                                    else
                                                                      (do
                                                                        if ((b__0 == (0b0101000#7 : (BitVec 7))) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((! (← (IsFeatureImplemented FEAT_CHK))) : Bool)
                                                                            then (EndOfInstruction ())
                                                                            else (pure ())
                                                                            (pure SystemHintOp_CHKFEAT))
                                                                        else
                                                                          (do
                                                                            (EndOfInstruction ())
                                                                            (pure op))))))))))))))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)

def decode_tsb_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp ()) ) : SailM SystemHintOp )
  let op ← (( do
    let b__0 := (CRm +++ op2)
    if ((b__0 == (0b0000000#7 : (BitVec 7))) : Bool)
    then (pure SystemHintOp_NOP)
    else
      (do
        if ((b__0 == (0b0000001#7 : (BitVec 7))) : Bool)
        then (pure SystemHintOp_YIELD)
        else
          (do
            if ((b__0 == (0b0000010#7 : (BitVec 7))) : Bool)
            then (pure SystemHintOp_WFE)
            else
              (do
                if ((b__0 == (0b0000011#7 : (BitVec 7))) : Bool)
                then (pure SystemHintOp_WFI)
                else
                  (do
                    if ((b__0 == (0b0000100#7 : (BitVec 7))) : Bool)
                    then (pure SystemHintOp_SEV)
                    else
                      (do
                        if ((b__0 == (0b0000101#7 : (BitVec 7))) : Bool)
                        then (pure SystemHintOp_SEVL)
                        else
                          (do
                            if ((b__0 == (0b0000110#7 : (BitVec 7))) : Bool)
                            then
                              (do
                                if ((! (← (HaveDGHExt ()))) : Bool)
                                then (EndOfInstruction ())
                                else (pure ())
                                (pure SystemHintOp_DGH))
                            else
                              (do
                                if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                then sailThrow ((Error_See "XPACLRI"))
                                else
                                  (do
                                    if (((Sail.BitVec.extractLsb b__0 6 3) == (0x1#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        match (op2 : BitVec 3) with
                                        | 0b000 => (sailThrow ((Error_See "PACIA1716")) : SailM Unit)
                                        | 0b010 => (sailThrow ((Error_See "PACIB1716")) : SailM Unit)
                                        | 0b100 => (sailThrow ((Error_See "AUTIA1716")) : SailM Unit)
                                        | 0b110 => (sailThrow ((Error_See "AUTIB1716")) : SailM Unit)
                                        | _ => (EndOfInstruction ())
                                        (pure op))
                                    else
                                      (do
                                        if ((b__0 == (0b0010000#7 : (BitVec 7))) : Bool)
                                        then
                                          (do
                                            if ((! (← (HaveRASExt ()))) : Bool)
                                            then (EndOfInstruction ())
                                            else (pure ())
                                            (pure SystemHintOp_ESB))
                                        else
                                          (do
                                            if ((b__0 == (0b0010001#7 : (BitVec 7))) : Bool)
                                            then
                                              (do
                                                if ((! (← (HaveStatisticalProfiling ()))) : Bool)
                                                then (EndOfInstruction ())
                                                else (pure ())
                                                (pure SystemHintOp_PSB))
                                            else
                                              (do
                                                if ((b__0 == (0b0010010#7 : (BitVec 7))) : Bool)
                                                then
                                                  (do
                                                    if ((! (← (HaveSelfHostedTrace ()))) : Bool)
                                                    then (EndOfInstruction ())
                                                    else (pure ())
                                                    (pure SystemHintOp_TSB))
                                                else
                                                  (do
                                                    if ((b__0 == (0b0010011#7 : (BitVec 7))) : Bool)
                                                    then
                                                      (do
                                                        if ((! (← (IsFeatureImplemented FEAT_GCS))) : Bool)
                                                        then (EndOfInstruction ())
                                                        else (pure ())
                                                        (pure SystemHintOp_GCSB))
                                                    else
                                                      (do
                                                        if ((b__0 == (0b0010100#7 : (BitVec 7))) : Bool)
                                                        then (pure SystemHintOp_CSDB)
                                                        else
                                                          (do
                                                            if ((b__0 == (0b0010110#7 : (BitVec 7))) : Bool)
                                                            then
                                                              (do
                                                                if ((! (← (HaveFeatCLRBHB ()))) : Bool)
                                                                then (EndOfInstruction ())
                                                                else (pure ())
                                                                (pure SystemHintOp_CLRBHB))
                                                            else
                                                              (do
                                                                if (((Sail.BitVec.extractLsb b__0 6 3) == (0x3#4 : (BitVec 4))) : Bool)
                                                                then
                                                                  (do
                                                                    match (op2 : BitVec 3) with
                                                                    | 0b000 => (sailThrow ((Error_See "PACIAZ")) : SailM Unit)
                                                                    | 0b001 => (sailThrow ((Error_See "PACIASP")) : SailM Unit)
                                                                    | 0b010 => (sailThrow ((Error_See "PACIBZ")) : SailM Unit)
                                                                    | 0b011 => (sailThrow ((Error_See "PACIBSP")) : SailM Unit)
                                                                    | 0b100 => (sailThrow ((Error_See "AUTIAZ")) : SailM Unit)
                                                                    | 0b101 => (sailThrow ((Error_See "AUTIASP")) : SailM Unit)
                                                                    | 0b110 => (sailThrow ((Error_See "AUTIBZ")) : SailM Unit)
                                                                    | _ => (sailThrow ((Error_See "AUTIBSP")) : SailM Unit)
                                                                    (pure op))
                                                                else
                                                                  (do
                                                                    if ((((Sail.BitVec.extractLsb b__0 6 3) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                                                    then
                                                                      (do
                                                                        let op : SystemHintOp := SystemHintOp_BTI
                                                                        (SetBTypeCompatible (← (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1))))
                                                                        (pure op))
                                                                    else
                                                                      (do
                                                                        if ((b__0 == (0b0101000#7 : (BitVec 7))) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((! (← (IsFeatureImplemented FEAT_CHK))) : Bool)
                                                                            then (EndOfInstruction ())
                                                                            else (pure ())
                                                                            (pure SystemHintOp_CHKFEAT))
                                                                        else
                                                                          (do
                                                                            (EndOfInstruction ())
                                                                            (pure op))))))))))))))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)

def decode_wfe_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp ()) ) : SailM SystemHintOp )
  let op ← (( do
    let b__0 := (CRm +++ op2)
    if ((b__0 == (0b0000000#7 : (BitVec 7))) : Bool)
    then (pure SystemHintOp_NOP)
    else
      (do
        if ((b__0 == (0b0000001#7 : (BitVec 7))) : Bool)
        then (pure SystemHintOp_YIELD)
        else
          (do
            if ((b__0 == (0b0000010#7 : (BitVec 7))) : Bool)
            then (pure SystemHintOp_WFE)
            else
              (do
                if ((b__0 == (0b0000011#7 : (BitVec 7))) : Bool)
                then (pure SystemHintOp_WFI)
                else
                  (do
                    if ((b__0 == (0b0000100#7 : (BitVec 7))) : Bool)
                    then (pure SystemHintOp_SEV)
                    else
                      (do
                        if ((b__0 == (0b0000101#7 : (BitVec 7))) : Bool)
                        then (pure SystemHintOp_SEVL)
                        else
                          (do
                            if ((b__0 == (0b0000110#7 : (BitVec 7))) : Bool)
                            then
                              (do
                                if ((! (← (HaveDGHExt ()))) : Bool)
                                then (EndOfInstruction ())
                                else (pure ())
                                (pure SystemHintOp_DGH))
                            else
                              (do
                                if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                then sailThrow ((Error_See "XPACLRI"))
                                else
                                  (do
                                    if (((Sail.BitVec.extractLsb b__0 6 3) == (0x1#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        match (op2 : BitVec 3) with
                                        | 0b000 => (sailThrow ((Error_See "PACIA1716")) : SailM Unit)
                                        | 0b010 => (sailThrow ((Error_See "PACIB1716")) : SailM Unit)
                                        | 0b100 => (sailThrow ((Error_See "AUTIA1716")) : SailM Unit)
                                        | 0b110 => (sailThrow ((Error_See "AUTIB1716")) : SailM Unit)
                                        | _ => (EndOfInstruction ())
                                        (pure op))
                                    else
                                      (do
                                        if ((b__0 == (0b0010000#7 : (BitVec 7))) : Bool)
                                        then
                                          (do
                                            if ((! (← (HaveRASExt ()))) : Bool)
                                            then (EndOfInstruction ())
                                            else (pure ())
                                            (pure SystemHintOp_ESB))
                                        else
                                          (do
                                            if ((b__0 == (0b0010001#7 : (BitVec 7))) : Bool)
                                            then
                                              (do
                                                if ((! (← (HaveStatisticalProfiling ()))) : Bool)
                                                then (EndOfInstruction ())
                                                else (pure ())
                                                (pure SystemHintOp_PSB))
                                            else
                                              (do
                                                if ((b__0 == (0b0010010#7 : (BitVec 7))) : Bool)
                                                then
                                                  (do
                                                    if ((! (← (HaveSelfHostedTrace ()))) : Bool)
                                                    then (EndOfInstruction ())
                                                    else (pure ())
                                                    (pure SystemHintOp_TSB))
                                                else
                                                  (do
                                                    if ((b__0 == (0b0010011#7 : (BitVec 7))) : Bool)
                                                    then
                                                      (do
                                                        if ((! (← (IsFeatureImplemented FEAT_GCS))) : Bool)
                                                        then (EndOfInstruction ())
                                                        else (pure ())
                                                        (pure SystemHintOp_GCSB))
                                                    else
                                                      (do
                                                        if ((b__0 == (0b0010100#7 : (BitVec 7))) : Bool)
                                                        then (pure SystemHintOp_CSDB)
                                                        else
                                                          (do
                                                            if ((b__0 == (0b0010110#7 : (BitVec 7))) : Bool)
                                                            then
                                                              (do
                                                                if ((! (← (HaveFeatCLRBHB ()))) : Bool)
                                                                then (EndOfInstruction ())
                                                                else (pure ())
                                                                (pure SystemHintOp_CLRBHB))
                                                            else
                                                              (do
                                                                if (((Sail.BitVec.extractLsb b__0 6 3) == (0x3#4 : (BitVec 4))) : Bool)
                                                                then
                                                                  (do
                                                                    match (op2 : BitVec 3) with
                                                                    | 0b000 => (sailThrow ((Error_See "PACIAZ")) : SailM Unit)
                                                                    | 0b001 => (sailThrow ((Error_See "PACIASP")) : SailM Unit)
                                                                    | 0b010 => (sailThrow ((Error_See "PACIBZ")) : SailM Unit)
                                                                    | 0b011 => (sailThrow ((Error_See "PACIBSP")) : SailM Unit)
                                                                    | 0b100 => (sailThrow ((Error_See "AUTIAZ")) : SailM Unit)
                                                                    | 0b101 => (sailThrow ((Error_See "AUTIASP")) : SailM Unit)
                                                                    | 0b110 => (sailThrow ((Error_See "AUTIBZ")) : SailM Unit)
                                                                    | _ => (sailThrow ((Error_See "AUTIBSP")) : SailM Unit)
                                                                    (pure op))
                                                                else
                                                                  (do
                                                                    if ((((Sail.BitVec.extractLsb b__0 6 3) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                                                    then
                                                                      (do
                                                                        let op : SystemHintOp := SystemHintOp_BTI
                                                                        (SetBTypeCompatible (← (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1))))
                                                                        (pure op))
                                                                    else
                                                                      (do
                                                                        if ((b__0 == (0b0101000#7 : (BitVec 7))) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((! (← (IsFeatureImplemented FEAT_CHK))) : Bool)
                                                                            then (EndOfInstruction ())
                                                                            else (pure ())
                                                                            (pure SystemHintOp_CHKFEAT))
                                                                        else
                                                                          (do
                                                                            (EndOfInstruction ())
                                                                            (pure op))))))))))))))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)

def decode_wfi_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp ()) ) : SailM SystemHintOp )
  let op ← (( do
    let b__0 := (CRm +++ op2)
    if ((b__0 == (0b0000000#7 : (BitVec 7))) : Bool)
    then (pure SystemHintOp_NOP)
    else
      (do
        if ((b__0 == (0b0000001#7 : (BitVec 7))) : Bool)
        then (pure SystemHintOp_YIELD)
        else
          (do
            if ((b__0 == (0b0000010#7 : (BitVec 7))) : Bool)
            then (pure SystemHintOp_WFE)
            else
              (do
                if ((b__0 == (0b0000011#7 : (BitVec 7))) : Bool)
                then (pure SystemHintOp_WFI)
                else
                  (do
                    if ((b__0 == (0b0000100#7 : (BitVec 7))) : Bool)
                    then (pure SystemHintOp_SEV)
                    else
                      (do
                        if ((b__0 == (0b0000101#7 : (BitVec 7))) : Bool)
                        then (pure SystemHintOp_SEVL)
                        else
                          (do
                            if ((b__0 == (0b0000110#7 : (BitVec 7))) : Bool)
                            then
                              (do
                                if ((! (← (HaveDGHExt ()))) : Bool)
                                then (EndOfInstruction ())
                                else (pure ())
                                (pure SystemHintOp_DGH))
                            else
                              (do
                                if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                then sailThrow ((Error_See "XPACLRI"))
                                else
                                  (do
                                    if (((Sail.BitVec.extractLsb b__0 6 3) == (0x1#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        match (op2 : BitVec 3) with
                                        | 0b000 => (sailThrow ((Error_See "PACIA1716")) : SailM Unit)
                                        | 0b010 => (sailThrow ((Error_See "PACIB1716")) : SailM Unit)
                                        | 0b100 => (sailThrow ((Error_See "AUTIA1716")) : SailM Unit)
                                        | 0b110 => (sailThrow ((Error_See "AUTIB1716")) : SailM Unit)
                                        | _ => (EndOfInstruction ())
                                        (pure op))
                                    else
                                      (do
                                        if ((b__0 == (0b0010000#7 : (BitVec 7))) : Bool)
                                        then
                                          (do
                                            if ((! (← (HaveRASExt ()))) : Bool)
                                            then (EndOfInstruction ())
                                            else (pure ())
                                            (pure SystemHintOp_ESB))
                                        else
                                          (do
                                            if ((b__0 == (0b0010001#7 : (BitVec 7))) : Bool)
                                            then
                                              (do
                                                if ((! (← (HaveStatisticalProfiling ()))) : Bool)
                                                then (EndOfInstruction ())
                                                else (pure ())
                                                (pure SystemHintOp_PSB))
                                            else
                                              (do
                                                if ((b__0 == (0b0010010#7 : (BitVec 7))) : Bool)
                                                then
                                                  (do
                                                    if ((! (← (HaveSelfHostedTrace ()))) : Bool)
                                                    then (EndOfInstruction ())
                                                    else (pure ())
                                                    (pure SystemHintOp_TSB))
                                                else
                                                  (do
                                                    if ((b__0 == (0b0010011#7 : (BitVec 7))) : Bool)
                                                    then
                                                      (do
                                                        if ((! (← (IsFeatureImplemented FEAT_GCS))) : Bool)
                                                        then (EndOfInstruction ())
                                                        else (pure ())
                                                        (pure SystemHintOp_GCSB))
                                                    else
                                                      (do
                                                        if ((b__0 == (0b0010100#7 : (BitVec 7))) : Bool)
                                                        then (pure SystemHintOp_CSDB)
                                                        else
                                                          (do
                                                            if ((b__0 == (0b0010110#7 : (BitVec 7))) : Bool)
                                                            then
                                                              (do
                                                                if ((! (← (HaveFeatCLRBHB ()))) : Bool)
                                                                then (EndOfInstruction ())
                                                                else (pure ())
                                                                (pure SystemHintOp_CLRBHB))
                                                            else
                                                              (do
                                                                if (((Sail.BitVec.extractLsb b__0 6 3) == (0x3#4 : (BitVec 4))) : Bool)
                                                                then
                                                                  (do
                                                                    match (op2 : BitVec 3) with
                                                                    | 0b000 => (sailThrow ((Error_See "PACIAZ")) : SailM Unit)
                                                                    | 0b001 => (sailThrow ((Error_See "PACIASP")) : SailM Unit)
                                                                    | 0b010 => (sailThrow ((Error_See "PACIBZ")) : SailM Unit)
                                                                    | 0b011 => (sailThrow ((Error_See "PACIBSP")) : SailM Unit)
                                                                    | 0b100 => (sailThrow ((Error_See "AUTIAZ")) : SailM Unit)
                                                                    | 0b101 => (sailThrow ((Error_See "AUTIASP")) : SailM Unit)
                                                                    | 0b110 => (sailThrow ((Error_See "AUTIBZ")) : SailM Unit)
                                                                    | _ => (sailThrow ((Error_See "AUTIBSP")) : SailM Unit)
                                                                    (pure op))
                                                                else
                                                                  (do
                                                                    if ((((Sail.BitVec.extractLsb b__0 6 3) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                                                    then
                                                                      (do
                                                                        let op : SystemHintOp := SystemHintOp_BTI
                                                                        (SetBTypeCompatible (← (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1))))
                                                                        (pure op))
                                                                    else
                                                                      (do
                                                                        if ((b__0 == (0b0101000#7 : (BitVec 7))) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((! (← (IsFeatureImplemented FEAT_CHK))) : Bool)
                                                                            then (EndOfInstruction ())
                                                                            else (pure ())
                                                                            (pure SystemHintOp_CHKFEAT))
                                                                        else
                                                                          (do
                                                                            (EndOfInstruction ())
                                                                            (pure op))))))))))))))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)

def decode_yield_aarch64_instrs_system_hints (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let op ← (( do (undefined_SystemHintOp ()) ) : SailM SystemHintOp )
  let op ← (( do
    let b__0 := (CRm +++ op2)
    if ((b__0 == (0b0000000#7 : (BitVec 7))) : Bool)
    then (pure SystemHintOp_NOP)
    else
      (do
        if ((b__0 == (0b0000001#7 : (BitVec 7))) : Bool)
        then (pure SystemHintOp_YIELD)
        else
          (do
            if ((b__0 == (0b0000010#7 : (BitVec 7))) : Bool)
            then (pure SystemHintOp_WFE)
            else
              (do
                if ((b__0 == (0b0000011#7 : (BitVec 7))) : Bool)
                then (pure SystemHintOp_WFI)
                else
                  (do
                    if ((b__0 == (0b0000100#7 : (BitVec 7))) : Bool)
                    then (pure SystemHintOp_SEV)
                    else
                      (do
                        if ((b__0 == (0b0000101#7 : (BitVec 7))) : Bool)
                        then (pure SystemHintOp_SEVL)
                        else
                          (do
                            if ((b__0 == (0b0000110#7 : (BitVec 7))) : Bool)
                            then
                              (do
                                if ((! (← (HaveDGHExt ()))) : Bool)
                                then (EndOfInstruction ())
                                else (pure ())
                                (pure SystemHintOp_DGH))
                            else
                              (do
                                if ((b__0 == (0b0000111#7 : (BitVec 7))) : Bool)
                                then sailThrow ((Error_See "XPACLRI"))
                                else
                                  (do
                                    if (((Sail.BitVec.extractLsb b__0 6 3) == (0x1#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        match (op2 : BitVec 3) with
                                        | 0b000 => (sailThrow ((Error_See "PACIA1716")) : SailM Unit)
                                        | 0b010 => (sailThrow ((Error_See "PACIB1716")) : SailM Unit)
                                        | 0b100 => (sailThrow ((Error_See "AUTIA1716")) : SailM Unit)
                                        | 0b110 => (sailThrow ((Error_See "AUTIB1716")) : SailM Unit)
                                        | _ => (EndOfInstruction ())
                                        (pure op))
                                    else
                                      (do
                                        if ((b__0 == (0b0010000#7 : (BitVec 7))) : Bool)
                                        then
                                          (do
                                            if ((! (← (HaveRASExt ()))) : Bool)
                                            then (EndOfInstruction ())
                                            else (pure ())
                                            (pure SystemHintOp_ESB))
                                        else
                                          (do
                                            if ((b__0 == (0b0010001#7 : (BitVec 7))) : Bool)
                                            then
                                              (do
                                                if ((! (← (HaveStatisticalProfiling ()))) : Bool)
                                                then (EndOfInstruction ())
                                                else (pure ())
                                                (pure SystemHintOp_PSB))
                                            else
                                              (do
                                                if ((b__0 == (0b0010010#7 : (BitVec 7))) : Bool)
                                                then
                                                  (do
                                                    if ((! (← (HaveSelfHostedTrace ()))) : Bool)
                                                    then (EndOfInstruction ())
                                                    else (pure ())
                                                    (pure SystemHintOp_TSB))
                                                else
                                                  (do
                                                    if ((b__0 == (0b0010011#7 : (BitVec 7))) : Bool)
                                                    then
                                                      (do
                                                        if ((! (← (IsFeatureImplemented FEAT_GCS))) : Bool)
                                                        then (EndOfInstruction ())
                                                        else (pure ())
                                                        (pure SystemHintOp_GCSB))
                                                    else
                                                      (do
                                                        if ((b__0 == (0b0010100#7 : (BitVec 7))) : Bool)
                                                        then (pure SystemHintOp_CSDB)
                                                        else
                                                          (do
                                                            if ((b__0 == (0b0010110#7 : (BitVec 7))) : Bool)
                                                            then
                                                              (do
                                                                if ((! (← (HaveFeatCLRBHB ()))) : Bool)
                                                                then (EndOfInstruction ())
                                                                else (pure ())
                                                                (pure SystemHintOp_CLRBHB))
                                                            else
                                                              (do
                                                                if (((Sail.BitVec.extractLsb b__0 6 3) == (0x3#4 : (BitVec 4))) : Bool)
                                                                then
                                                                  (do
                                                                    match (op2 : BitVec 3) with
                                                                    | 0b000 => (sailThrow ((Error_See "PACIAZ")) : SailM Unit)
                                                                    | 0b001 => (sailThrow ((Error_See "PACIASP")) : SailM Unit)
                                                                    | 0b010 => (sailThrow ((Error_See "PACIBZ")) : SailM Unit)
                                                                    | 0b011 => (sailThrow ((Error_See "PACIBSP")) : SailM Unit)
                                                                    | 0b100 => (sailThrow ((Error_See "AUTIAZ")) : SailM Unit)
                                                                    | 0b101 => (sailThrow ((Error_See "AUTIASP")) : SailM Unit)
                                                                    | 0b110 => (sailThrow ((Error_See "AUTIBZ")) : SailM Unit)
                                                                    | _ => (sailThrow ((Error_See "AUTIBSP")) : SailM Unit)
                                                                    (pure op))
                                                                else
                                                                  (do
                                                                    if ((((Sail.BitVec.extractLsb b__0 6 3) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                                                    then
                                                                      (do
                                                                        let op : SystemHintOp := SystemHintOp_BTI
                                                                        (SetBTypeCompatible (← (BTypeCompatible_BTI (Sail.BitVec.extractLsb op2 2 1))))
                                                                        (pure op))
                                                                    else
                                                                      (do
                                                                        if ((b__0 == (0b0101000#7 : (BitVec 7))) : Bool)
                                                                        then
                                                                          (do
                                                                            if ((! (← (IsFeatureImplemented FEAT_CHK))) : Bool)
                                                                            then (EndOfInstruction ())
                                                                            else (pure ())
                                                                            (pure SystemHintOp_CHKFEAT))
                                                                        else
                                                                          (do
                                                                            (EndOfInstruction ())
                                                                            (pure op))))))))))))))))))) ) : SailM SystemHintOp )
  (execute_aarch64_instrs_system_hints op)

def decode_cas_aarch64_instrs_memory_atomicops_cas_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveAtomicExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let s := (BitVec.toNat Rs)
  let datasize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := (L == 1#1)
  let release : Bool := (o0 == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_cas_single acquire datasize n regsize release s t tagchecked)

def decode_casb_aarch64_instrs_memory_atomicops_cas_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveAtomicExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let s := (BitVec.toNat Rs)
  let datasize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := (L == 1#1)
  let release : Bool := (o0 == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_cas_single acquire datasize n regsize release s t tagchecked)

def decode_cash_aarch64_instrs_memory_atomicops_cas_single (Rt : (BitVec 5)) (Rn : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveAtomicExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let s := (BitVec.toNat Rs)
  let datasize := (Int.shiftl 8 (BitVec.toNat size))
  let regsize :=
    if ((datasize == 64) : Bool)
    then 64
    else 32
  let acquire : Bool := (L == 1#1)
  let release : Bool := (o0 == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_cas_single acquire datasize n regsize release s t tagchecked)

def decode_casp_aarch64_instrs_memory_atomicops_cas_pair (Rt : (BitVec 5)) (Rn : (BitVec 5)) (Rt2 : (BitVec 5)) (o0 : (BitVec 1)) (Rs : (BitVec 5)) (L : (BitVec 1)) (sz : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveAtomicExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access Rs 0)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let t := (BitVec.toNat Rt)
  let s := (BitVec.toNat Rs)
  let datasize := (Int.shiftl 32 (BitVec.toNat sz))
  let regsize := datasize
  let acquire : Bool := (L == 1#1)
  let release : Bool := (o0 == 1#1)
  let tagchecked : Bool := (n != 31)
  (execute_aarch64_instrs_memory_atomicops_cas_pair acquire datasize n release s t tagchecked)

def decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let condition : (BitVec 4) := cond
  let flags : (BitVec 4) := nzcv
  (execute_aarch64_instrs_integer_conditional_compare_register condition datasize flags m n sub_op)

def decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let condition : (BitVec 4) := cond
  let flags : (BitVec 4) := nzcv
  (execute_aarch64_instrs_integer_conditional_compare_register condition datasize flags m n sub_op)

def decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (imm5 : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let condition : (BitVec 4) := cond
  let flags : (BitVec 4) := nzcv
  let imm : (BitVec datasize) := (Sail.BitVec.zeroExtend imm5 datasize)
  (execute_aarch64_instrs_integer_conditional_compare_immediate condition datasize flags imm n sub_op)

def decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (imm5 : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let condition : (BitVec 4) := cond
  let flags : (BitVec 4) := nzcv
  let imm : (BitVec datasize) := (Sail.BitVec.zeroExtend imm5 datasize)
  (execute_aarch64_instrs_integer_conditional_compare_immediate condition datasize flags imm n sub_op)

def decode_cfinv_aarch64_instrs_integer_flags_cfinv (CRm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveFlagManipulateExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_integer_flags_cfinv ())

def decode_clrex_aarch64_instrs_system_monitors (CRm : (BitVec 4)) : Unit :=
  (execute_aarch64_instrs_system_monitors ())

def decode_cls_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let elements := (Int.ediv datasize esize)
  let countop : CountOp :=
    if ((U == 1#1) : Bool)
    then CountOp_CLZ
    else CountOp_CLS
  (execute_aarch64_instrs_vector_arithmetic_unary_clsz countop d datasize elements esize n)

def decode_clz_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let elements := (Int.ediv datasize esize)
  let countop : CountOp :=
    if ((U == 1#1) : Bool)
    then CountOp_CLZ
    else CountOp_CLS
  (execute_aarch64_instrs_vector_arithmetic_unary_clsz countop d datasize elements esize n)

def decode_cls_int_aarch64_instrs_integer_arithmetic_cnt (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let opcode : CountOp :=
    if ((op == 0#1) : Bool)
    then CountOp_CLZ
    else CountOp_CLS
  (execute_aarch64_instrs_integer_arithmetic_cnt d datasize n opcode)

def decode_clz_int_aarch64_instrs_integer_arithmetic_cnt (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let opcode : CountOp :=
    if ((op == 0#1) : Bool)
    then CountOp_CLZ
    else CountOp_CLS
  (execute_aarch64_instrs_integer_arithmetic_cnt d datasize n opcode)

def decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison d datasize elements esize n)

def decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison d datasize elements esize n)

def decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison d datasize elements esize n)

def decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison d datasize elements esize n)

def decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison d datasize elements esize n)

def decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison d datasize elements esize n)

def decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison d datasize elements esize n)

def decode_cmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison d datasize elements esize n)

def decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let and_test : Bool := (U == 0#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd and_test d datasize elements esize m n)

def decode_cmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let and_test : Bool := (U == 0#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd and_test d datasize elements esize m n)

def decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let and_test : Bool := (U == 0#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd and_test d datasize elements esize m n)

def decode_cmtst_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let and_test : Bool := (U == 0#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_bitwise_sisd and_test d datasize elements esize m n)

def decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  let cmp_eq : Bool := (eq == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq d datasize elements esize m n is_unsigned)

def decode_cmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp_eq : Bool := (eq == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq d datasize elements esize m n is_unsigned)

def decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  let cmp_eq : Bool := (eq == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq d datasize elements esize m n is_unsigned)

def decode_cmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp_eq : Bool := (eq == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq d datasize elements esize m n is_unsigned)

def decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  let cmp_eq : Bool := (eq == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq d datasize elements esize m n is_unsigned)

def decode_cmhi_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp_eq : Bool := (eq == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq d datasize elements esize m n is_unsigned)

def decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let is_unsigned : Bool := (U == 1#1)
  let cmp_eq : Bool := (eq == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq d datasize elements esize m n is_unsigned)

def decode_cmhs_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp_eq : Bool := (eq == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_int_sisd cmp_eq d datasize elements esize m n is_unsigned)

def decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let datasize := esize
  let elements := 1
  let comparison : CompareOp := CompareOp_LT
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd comparison d datasize elements esize n)

def decode_cmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
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
  let comparison : CompareOp := CompareOp_LT
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_lessthan_sisd comparison d datasize elements esize n)

def decode_cnt_aarch64_instrs_integer_arithmetic_unary_cnt (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveCSSC ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let d := (BitVec.toNat Rd)
  (execute_aarch64_instrs_integer_arithmetic_unary_cnt d datasize n)

def decode_cnt_advsimd_aarch64_instrs_vector_arithmetic_unary_cnt (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((size != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize 8)
  (execute_aarch64_instrs_vector_arithmetic_unary_cnt d datasize elements esize n)

def decode_cpyp_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:8037.58-8037.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpy d n options_name s stage)

def decode_cpypn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:8094.58-8094.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpy d n options_name s stage)

def decode_cpyprn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:8151.58-8151.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpy d n options_name s stage)

def decode_cpyprt_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:8208.58-8208.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpy d n options_name s stage)

def decode_cpyprtn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:8265.58-8265.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpy d n options_name s stage)

def decode_cpyprtrn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:8322.58-8322.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpy d n options_name s stage)

def decode_cpyprtwn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:8379.58-8379.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpy d n options_name s stage)

def decode_cpypt_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:8436.58-8436.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpy d n options_name s stage)

def decode_cpyptn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:8493.58-8493.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpy d n options_name s stage)

def decode_cpyptrn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:8550.58-8550.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpy d n options_name s stage)

def decode_cpyptwn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:8607.58-8607.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpy d n options_name s stage)

def decode_cpypwn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:8664.58-8664.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpy d n options_name s stage)

def decode_cpypwt_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:8721.58-8721.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpy d n options_name s stage)

def decode_cpypwtn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:8778.58-8778.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpy d n options_name s stage)

def decode_cpypwtrn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:8835.58-8835.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpy d n options_name s stage)

def decode_cpypwtwn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:8892.58-8892.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpy d n options_name s stage)

def decode_cpyfp_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:9092.58-9092.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpyf d n options_name s stage)

def decode_cpyfpn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:9149.58-9149.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpyf d n options_name s stage)

def decode_cpyfprn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:9206.58-9206.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpyf d n options_name s stage)

def decode_cpyfprt_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:9263.58-9263.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpyf d n options_name s stage)

def decode_cpyfprtn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:9320.58-9320.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpyf d n options_name s stage)

def decode_cpyfprtrn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:9377.58-9377.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpyf d n options_name s stage)

def decode_cpyfprtwn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:9434.58-9434.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpyf d n options_name s stage)

def decode_cpyfpt_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:9491.58-9491.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpyf d n options_name s stage)

def decode_cpyfptn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:9548.58-9548.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpyf d n options_name s stage)

def decode_cpyfptrn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:9605.58-9605.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpyf d n options_name s stage)

def decode_cpyfptwn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:9662.58-9662.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpyf d n options_name s stage)

def decode_cpyfpwn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:9719.58-9719.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpyf d n options_name s stage)

def decode_cpyfpwt_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:9776.58-9776.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpyf d n options_name s stage)

def decode_cpyfpwtn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:9833.58-9833.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpyf d n options_name s stage)

def decode_cpyfpwtrn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:9890.58-9890.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpyf d n options_name s stage)

def decode_cpyfpwtwn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatMOPS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((sz != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let s := (BitVec.toNat Rs)
  let n := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage ()) ) : SailM MOPSStage )
  let stage ← (( do
    match (op1 : BitVec 2) with
    | 0b00 => (pure MOPSStage_Prologue)
    | 0b01 => (pure MOPSStage_Main)
    | 0b10 => (pure MOPSStage_Epilogue)
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs64.sail:9947.58-9947.59"
      match c with
      | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
      | .Constraint_NOP => (EndOfInstruction ())
      | _ => (pure ()))
  else (pure ())
  (execute_aarch64_instrs_memory_mcpymset_cpyf d n options_name s stage)

def decode_crc32_aarch64_instrs_integer_crc (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 2)) (C : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveCRCExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((sf == 1#1) && (sz != 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((sf == 0#1) && (sz == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let size := (Int.shiftl 8 (BitVec.toNat sz))
  let crc32c : Bool := (C == 1#1)
  (execute_aarch64_instrs_integer_crc crc32c d m n size)

def decode_crc32c_aarch64_instrs_integer_crc (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 2)) (C : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveCRCExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((sf == 1#1) && (sz != 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((sf == 0#1) && (sz == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let size := (Int.shiftl 8 (BitVec.toNat sz))
  let crc32c : Bool := (C == 1#1)
  (execute_aarch64_instrs_integer_crc crc32c d m n size)

def decode_ctz_aarch64_instrs_integer_arithmetic_unary_ctz (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveCSSC ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize := (Int.shiftl 32 (BitVec.toNat sf))
  let n := (BitVec.toNat Rn)
  let d := (BitVec.toNat Rd)
  (execute_aarch64_instrs_integer_arithmetic_unary_ctz d datasize n)

def decode_dcps1_aarch64_instrs_system_exceptions_debug_exception (LL : (BitVec 2)) (imm16 : (BitVec 16)) : SailM Unit := do
  let target_level : (BitVec 2) := LL
  if ((LL == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((! (← (Halted ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_system_exceptions_debug_exception target_level)

def decode_dcps2_aarch64_instrs_system_exceptions_debug_exception (LL : (BitVec 2)) (imm16 : (BitVec 16)) : SailM Unit := do
  let target_level : (BitVec 2) := LL
  if ((LL == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((! (← (Halted ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_system_exceptions_debug_exception target_level)

def decode_dcps3_aarch64_instrs_system_exceptions_debug_exception (LL : (BitVec 2)) (imm16 : (BitVec 16)) : SailM Unit := do
  let target_level : (BitVec 2) := LL
  if ((LL == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((! (← (Halted ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_system_exceptions_debug_exception target_level)

def decode_dmb_aarch64_instrs_system_barriers_dmb (opc : (BitVec 2)) (CRm : (BitVec 4)) : SailM Unit := do
  let domain ← (( do (undefined_MBReqDomain ()) ) : SailM MBReqDomain )
  let types ← (( do (undefined_MBReqTypes ()) ) : SailM MBReqTypes )
  let domain : MBReqDomain :=
    match ((Sail.BitVec.extractLsb CRm 3 2) : BitVec 2) with
    | 0b00 => MBReqDomain_OuterShareable
    | 0b01 => MBReqDomain_Nonshareable
    | 0b10 => MBReqDomain_InnerShareable
    | _ => MBReqDomain_FullSystem
  let (domain, types) : (MBReqDomain × MBReqTypes) :=
    match ((Sail.BitVec.extractLsb CRm 1 0) : BitVec 2) with
    | 0b00 =>
      (let types : MBReqTypes := MBReqTypes_All
      let domain : MBReqDomain := MBReqDomain_FullSystem
      (domain, types))
    | 0b01 =>
      (let types : MBReqTypes := MBReqTypes_Reads
      (domain, types))
    | 0b10 =>
      (let types : MBReqTypes := MBReqTypes_Writes
      (domain, types))
    | _ =>
      (let types : MBReqTypes := MBReqTypes_All
      (domain, types))
  let types := types
  (execute_aarch64_instrs_system_barriers_dmb domain types)

def decode_drps_aarch64_instrs_branch_unconditional_dret (_ : Unit) : SailM Unit := do
  if ((←((pure (! (← (Halted ())))) <||> (do
       (pure ((← readReg PSTATE).EL == EL0))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_branch_unconditional_dret ())

def decode_dsb_aarch64_instrs_system_barriers_dsb (opc : (BitVec 2)) (CRm : (BitVec 4)) : SailM Unit := do
  let nXS : Bool := false
  let alias' ← (( do (undefined_DSBAlias ()) ) : SailM DSBAlias )
  let alias' : DSBAlias :=
    match (CRm : BitVec 4) with
    | 0b0000 => DSBAlias_SSBB
    | 0b0100 => DSBAlias_PSSBB
    | _ => DSBAlias_DSB
  let alias' := alias'
  let domain ← (( do (undefined_MBReqDomain ()) ) : SailM MBReqDomain )
  let domain : MBReqDomain :=
    match ((Sail.BitVec.extractLsb CRm 3 2) : BitVec 2) with
    | 0b00 => MBReqDomain_OuterShareable
    | 0b01 => MBReqDomain_Nonshareable
    | 0b10 => MBReqDomain_InnerShareable
    | _ => MBReqDomain_FullSystem
  let types ← (( do (undefined_MBReqTypes ()) ) : SailM MBReqTypes )
  let (domain, types) : (MBReqDomain × MBReqTypes) :=
    match ((Sail.BitVec.extractLsb CRm 1 0) : BitVec 2) with
    | 0b00 =>
      (let types : MBReqTypes := MBReqTypes_All
      let domain : MBReqDomain := MBReqDomain_FullSystem
      (domain, types))
    | 0b01 =>
      (let types : MBReqTypes := MBReqTypes_Reads
      (domain, types))
    | 0b10 =>
      (let types : MBReqTypes := MBReqTypes_Writes
      (domain, types))
    | _ =>
      (let types : MBReqTypes := MBReqTypes_All
      (domain, types))
  (execute_aarch64_instrs_system_barriers_dsb alias' domain nXS types)

def decode_dsb_aarch64_instrs_system_barriers_dsb_nxs (imm2 : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFeatXS ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let types : MBReqTypes := MBReqTypes_All
  let nXS : Bool := true
  let alias' : DSBAlias := DSBAlias_DSB
  let domain ← (( do (undefined_MBReqDomain ()) ) : SailM MBReqDomain )
  let domain : MBReqDomain :=
    match (imm2 : BitVec 2) with
    | 0b00 => MBReqDomain_OuterShareable
    | 0b01 => MBReqDomain_Nonshareable
    | 0b10 => MBReqDomain_InnerShareable
    | _ => MBReqDomain_FullSystem
  let domain := domain
  (execute_aarch64_instrs_system_barriers_dsb alias' domain nXS types)

def decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let size := (LowestSetBit imm5)
  if ((size >b 3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  sail_assert (0 ≤b (size +i 1)) "src/instrs64.sail:10486.37-10486.38"
  let index := (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 (size +i 1)))
  let idxdsize :=
    if (((BitVec.join1 [(BitVec.access imm5 4)]) == 1#1) : Bool)
    then 128
    else 64
  let esize := (_shl_int_general 8 size)
  let datasize := esize
  let elements := 1
  sail_assert (((((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) || (esize == 128)) || (esize == 256)) && ((((((datasize == 8) || (datasize == 16)) || (datasize == 32)) || (datasize == 64)) || (datasize == 128)) || (datasize == 256))) "src/instrs64.sail:10492.101-10492.102"
  (execute_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd d datasize elements esize idxdsize index n)

def decode_dup_advsimd_elt_aarch64_instrs_vector_transfer_vector_cpy_dup_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let size := (LowestSetBit imm5)
  if ((size >b 3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  sail_assert (0 ≤b (size +i 1)) "src/instrs64.sail:10513.37-10513.38"
  let index := (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 (size +i 1)))
  let idxdsize :=
    if (((BitVec.join1 [(BitVec.access imm5 4)]) == 1#1) : Bool)
    then 128
    else 64
  if (((size == 3) && (Q == 0#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 size)
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (fdiv_int datasize esize)
  sail_assert ((((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) || (esize == 128)) || (esize == 256)) "src/instrs64.sail:10522.58-10522.59"
  (execute_aarch64_instrs_vector_transfer_vector_cpy_dup_sisd d datasize elements esize idxdsize index n)

def decode_dup_advsimd_gen_aarch64_instrs_vector_transfer_integer_dup (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm5 : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let size := (LowestSetBit imm5)
  if ((size >b 3) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size == 3) && (Q == 0#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (_shl_int_general 8 size)
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (fdiv_int datasize esize)
  sail_assert ((((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) || (esize == 128)) || (esize == 256)) "src/instrs64.sail:10565.58-10565.59"
  (execute_aarch64_instrs_vector_transfer_integer_dup d datasize elements esize n)

def decode_eor3_advsimd_aarch64_instrs_vector_crypto_sha3_eor3 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (← (HaveSHA3Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let a := (BitVec.toNat Ra)
  (execute_aarch64_instrs_vector_crypto_sha3_eor3 a d m n)

def decode_eret_aarch64_instrs_branch_unconditional_eret (op4 : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) : SailM Unit := do
  if (((← readReg PSTATE).EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let pac : Bool := (A == 1#1)
  let use_key_a : Bool := (M == 0#1)
  if (((! pac) && (op4 != 0b00000#5)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure pac) <&&> (do
           (pure ((! (← (HavePACExt ()))) || (op4 != 0b11111#5)))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ()))
  if ((Rn != 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_branch_unconditional_eret pac use_key_a)

def decode_ereta_aarch64_instrs_branch_unconditional_eret (op4 : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) : SailM Unit := do
  if (((← readReg PSTATE).EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let pac : Bool := (A == 1#1)
  let use_key_a : Bool := (M == 0#1)
  if (((! pac) && (op4 != 0b00000#5)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((←((pure pac) <&&> (do
           (pure ((! (← (HavePACExt ()))) || (op4 != 0b11111#5)))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ()))
  if ((Rn != 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch64_instrs_branch_unconditional_eret pac use_key_a)

def decode_ext_advsimd_aarch64_instrs_vector_transfer_vector_extract (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm4 : (BitVec 4)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if (((Q == 0#1) && ((BitVec.join1 [(BitVec.access imm4 3)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let position := (Int.shiftl (BitVec.toNat imm4) 3)
  (execute_aarch64_instrs_vector_transfer_vector_extract d datasize m n position)

def decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  if ((N != sf) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((sf == 0#1) && ((BitVec.join1 [(BitVec.access imms 5)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let lsb := (BitVec.toNat imms)
  (execute_aarch64_instrs_integer_ins_ext_extract_immediate d datasize lsb m n)

def decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 16
  let datasize := esize
  let elements := 1
  let abs : Bool := true
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd abs d datasize elements esize m n)

def decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let abs : Bool := true
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd abs d datasize elements esize m n)

def decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd abs d datasize elements esize m n)

def decode_fabd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_sub_fp16_sisd abs d datasize elements esize m n)

def decode_fabs_float_aarch64_instrs_float_arithmetic_unary (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
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
  let fpop ← (( do (undefined_FPUnaryOp ()) ) : SailM FPUnaryOp )
  let fpop : FPUnaryOp :=
    match (opc : BitVec 2) with
    | 0b00 => FPUnaryOp_MOV
    | 0b01 => FPUnaryOp_ABS
    | 0b10 => FPUnaryOp_NEG
    | _ => FPUnaryOp_SQRT
  let fpop := fpop
  (execute_aarch64_instrs_float_arithmetic_unary d esize fpop n)

def decode_fmov_float_aarch64_instrs_float_arithmetic_unary (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
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
  let fpop ← (( do (undefined_FPUnaryOp ()) ) : SailM FPUnaryOp )
  let fpop : FPUnaryOp :=
    match (opc : BitVec 2) with
    | 0b00 => FPUnaryOp_MOV
    | 0b01 => FPUnaryOp_ABS
    | 0b10 => FPUnaryOp_NEG
    | _ => FPUnaryOp_SQRT
  let fpop := fpop
  (execute_aarch64_instrs_float_arithmetic_unary d esize fpop n)

def decode_fneg_float_aarch64_instrs_float_arithmetic_unary (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
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
  let fpop ← (( do (undefined_FPUnaryOp ()) ) : SailM FPUnaryOp )
  let fpop : FPUnaryOp :=
    match (opc : BitVec 2) with
    | 0b00 => FPUnaryOp_MOV
    | 0b01 => FPUnaryOp_ABS
    | 0b10 => FPUnaryOp_NEG
    | _ => FPUnaryOp_SQRT
  let fpop := fpop
  (execute_aarch64_instrs_float_arithmetic_unary d esize fpop n)

def decode_fsqrt_float_aarch64_instrs_float_arithmetic_unary (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
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
  let fpop ← (( do (undefined_FPUnaryOp ()) ) : SailM FPUnaryOp )
  let fpop : FPUnaryOp :=
    match (opc : BitVec 2) with
    | 0b00 => FPUnaryOp_MOV
    | 0b01 => FPUnaryOp_ABS
    | 0b10 => FPUnaryOp_NEG
    | _ => FPUnaryOp_SQRT
  let fpop := fpop
  (execute_aarch64_instrs_float_arithmetic_unary d esize fpop n)

def decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 d datasize elements esize n neg)

def decode_fabs_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 d datasize elements esize n neg)

def decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 d datasize elements esize n neg)

def decode_fneg_advsimd_aarch64_instrs_vector_arithmetic_unary_diff_neg_float (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let neg : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_diff_neg_fp16 d datasize elements esize n neg)

def decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 16
  let datasize := esize
  let elements := 1
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_facge_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 16
  let datasize := esize
  let elements := 1
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_facgt_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 16
  let datasize := esize
  let elements := 1
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_fcmeq_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 16
  let datasize := esize
  let elements := 1
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_fcmge_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 16
  let datasize := esize
  let elements := 1
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_fcmgt_advsimd_reg_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (ac : (BitVec 1)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (E : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let cmp ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let abs ← (( do (undefined_bool ()) ) : SailM Bool )
  let (abs, cmp) ← (( do
    match (((E +++ U) +++ ac) : BitVec 3) with
    | 0b000 =>
      (let cmp : CompareOp := CompareOp_EQ
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b010 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b011 =>
      (let cmp : CompareOp := CompareOp_GE
      let abs : Bool := true
      (pure (abs, cmp)))
    | 0b110 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := false
      (pure (abs, cmp)))
    | 0b111 =>
      (let cmp : CompareOp := CompareOp_GT
      let abs : Bool := true
      (pure (abs, cmp)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × CompareOp) )
  let abs := abs
  let cmp := cmp
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_cmp_fp16_sisd abs cmp d datasize elements esize m n)

def decode_fadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 d datasize elements esize m n pair)

def decode_fadd_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 d datasize elements esize m n pair)

def decode_faddp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 d datasize elements esize m n pair)

def decode_faddp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp16 d datasize elements esize m n pair)

def decode_fadd_float_aarch64_instrs_float_arithmetic_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
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
  let sub_op : Bool := (op == 1#1)
  (execute_aarch64_instrs_float_arithmetic_add_sub d esize m n sub_op)

def decode_fsub_float_aarch64_instrs_float_arithmetic_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
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
  let sub_op : Bool := (op == 1#1)
  (execute_aarch64_instrs_float_arithmetic_add_sub d esize m n sub_op)

def decode_faddp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_add_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  if ((sz == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize := (esize *i 2)
  let elements := 2
  let op : ReduceOp := ReduceOp_FADD
  (execute_aarch64_instrs_vector_reduce_fp16_add_sisd d datasize esize n op)

def decode_faddp_advsimd_pair_aarch64_instrs_vector_reduce_fp_add_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := (esize *i 2)
  let elements := 2
  let op : ReduceOp := ReduceOp_FADD
  (execute_aarch64_instrs_vector_reduce_fp16_add_sisd d datasize esize n op)

def decode_fcadd_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp_complex (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rot : (BitVec 1)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveFCADDExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 0#1) && (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_add_fp_complex d datasize elements esize m n rot)

def decode_fccmp_float_aarch64_instrs_float_compare_cond (nzcv : (BitVec 4)) (op : (BitVec 1)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize : Nat := 16
  let datasize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let datasize := datasize
  let signal_all_nans : Bool := (op == 1#1)
  let condition : (BitVec 4) := cond
  let flags : (BitVec 4) := nzcv
  (execute_aarch64_instrs_float_compare_cond condition datasize flags m n signal_all_nans)

def decode_fccmpe_float_aarch64_instrs_float_compare_cond (nzcv : (BitVec 4)) (op : (BitVec 1)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize : Nat := 16
  let datasize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let datasize := datasize
  let signal_all_nans : Bool := (op == 1#1)
  let condition : (BitVec 4) := cond
  let flags : (BitVec 4) := nzcv
  (execute_aarch64_instrs_float_compare_cond condition datasize flags m n signal_all_nans)

def decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d datasize elements esize n)

def decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d datasize elements esize n)

def decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d datasize elements esize n)

def decode_fcmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d datasize elements esize n)

def decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d datasize elements esize n)

def decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d datasize elements esize n)

def decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d datasize elements esize n)

def decode_fcmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d datasize elements esize n)

def decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d datasize elements esize n)

def decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d datasize elements esize n)

def decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d datasize elements esize n)

def decode_fcmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d datasize elements esize n)

def decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d datasize elements esize n)

def decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d datasize elements esize n)

def decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d datasize elements esize n)

def decode_fcmle_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let comparison ← (( do (undefined_CompareOp ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match ((op +++ U) : BitVec 2) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_bulk_sisd comparison d datasize elements esize n)

def decode_fcmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_complex (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rot : (BitVec 2)) (Rm : (BitVec 5)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveFCADDExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 0#1) && (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_complex d datasize elements esize m n rot)

def decode_fcmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_complex (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (rot : (BitVec 2)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (size : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveFCADDExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (M +++ Rm))
  let index ← (( do (undefined_int ()) ) : SailM Int )
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let index : Int :=
    if ((size == 0b01#2) : Bool)
    then (BitVec.toNat (H +++ L))
    else index
  let index : Int :=
    if ((size == 0b10#2) : Bool)
    then (BitVec.toNat H)
    else index
  let index := index
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  if (((size == 0b10#2) && ((L == 1#1) || (Q == 0#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((size == 0b01#2) && (H == 1#1)) && (Q == 0#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  sail_assert ((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) "src/instrs64.sail:13687.45-13687.46"
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_complex d datasize elements esize index m n rot)

def decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let comparison : CompareOp := CompareOp_LT
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd comparison d datasize elements esize n)

def decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let comparison : CompareOp := CompareOp_LT
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd comparison d datasize elements esize n)

def decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
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
  let comparison : CompareOp := CompareOp_LT
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd comparison d datasize elements esize n)

def decode_fcmlt_advsimd_aarch64_instrs_vector_arithmetic_unary_cmp_float_lessthan_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let comparison : CompareOp := CompareOp_LT
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_fp16_lessthan_sisd comparison d datasize elements esize n)

def decode_fcmp_float_aarch64_instrs_float_compare_uncond (opc : (BitVec 2)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize : Nat := 16
  let datasize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let datasize := datasize
  let signal_all_nans : Bool := ((BitVec.join1 [(BitVec.access opc 1)]) == 1#1)
  let cmp_with_zero : Bool := ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)
  (execute_aarch64_instrs_float_compare_uncond cmp_with_zero datasize m n signal_all_nans)

def decode_fcmpe_float_aarch64_instrs_float_compare_uncond (opc : (BitVec 2)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize : Nat := 16
  let datasize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let datasize := datasize
  let signal_all_nans : Bool := ((BitVec.join1 [(BitVec.access opc 1)]) == 1#1)
  let cmp_with_zero : Bool := ((BitVec.join1 [(BitVec.access opc 0)]) == 1#1)
  (execute_aarch64_instrs_float_compare_uncond cmp_with_zero datasize m n signal_all_nans)

def decode_fcsel_float_aarch64_instrs_float_move_fp_select (Rd : (BitVec 5)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let datasize : Nat := 16
  let datasize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let datasize := datasize
  let condition : (BitVec 4) := cond
  (execute_aarch64_instrs_float_move_fp_select condition d datasize m n)

def decode_fcvt_float_aarch64_instrs_float_convert_fp (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let srcsize : Nat := 16
  let dstsize : Nat := 16
  if ((ftype == opc) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let srcsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ => (pure 16) ) : SailM Int )
  let srcsize := srcsize
  let dstsize ← (( do
    match (opc : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ => (pure 16) ) : SailM Int )
  let dstsize := dstsize
  (execute_aarch64_instrs_float_convert_fp d dstsize n srcsize)

def decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtas_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtau_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_tieaway_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding : FPRounding := FPRounding_TIEAWAY
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_tieaway_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtas_float_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let part : Nat := 0
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 =>
      (do
        if ((((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) != 0b1101#4) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 128))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
    let (fltsize, is_unsigned, op, part, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding rmode)
          let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure (fltsize, is_unsigned, op, part, rounding)))
      else
        (do
          let (fltsize, is_unsigned, op, part, rounding) ← (( do
            if ((b__0 == (0x4#4 : (BitVec 4))) : Bool)
            then
              (do
                let rounding ← (FPRoundingMode (← (FPCR_read ())))
                let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_ItoF
                (pure (fltsize, is_unsigned, op, part, rounding)))
            else
              (do
                let (fltsize, is_unsigned, op, part, rounding) ← (( do
                  if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (let rounding : FPRounding := FPRounding_TIEAWAY
                    let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                    let op : FPConvOp := FPConvOp_CVT_FtoI
                    (pure (fltsize, is_unsigned, op, part, rounding)))
                  else
                    (do
                      let (fltsize, is_unsigned, op, part, rounding) ← (( do
                        if ((b__0 == (0xC#4 : (BitVec 4))) : Bool)
                        then
                          (do
                            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
                            then (sailThrow ((Error_Undefined ())) : SailM Unit)
                            else (pure ())
                            let op : FPConvOp :=
                              if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                              then FPConvOp_MOV_ItoF
                              else FPConvOp_MOV_FtoI
                            let part : Nat := 0
                            (pure (fltsize, is_unsigned, op, part, rounding)))
                        else
                          (do
                            let (fltsize, is_unsigned, op, part, rounding) ← (( do
                              if ((b__0 == (0xD#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (pure ())
                                  let op : FPConvOp :=
                                    if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                                    then FPConvOp_MOV_ItoF
                                    else FPConvOp_MOV_FtoI
                                  let part : Nat := 1
                                  let fltsize : Nat := 64
                                  (pure (fltsize, is_unsigned, op, part, rounding)))
                              else
                                (do
                                  let (is_unsigned, op, rounding) ← (( do
                                    if ((b__0 == (0xF#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        if ((! (← (HaveFJCVTZSExt ()))) : Bool)
                                        then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                        else (pure ())
                                        let rounding : FPRounding := FPRounding_ZERO
                                        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                                        let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                                        (pure (is_unsigned, op, rounding)))
                                    else sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
                                  (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                            (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                      (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
          (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
    (pure (fltsize, is_unsigned, op, part, rounding)) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part := part
  let fltsize := fltsize
  match fltsize with
  | 16 => (execute_aarch64_instrs_float_convert_int d 16 intsize n op part rounding is_unsigned)
  | 32 => (execute_aarch64_instrs_float_convert_int d 32 intsize n op part rounding is_unsigned)
  | 64 => (execute_aarch64_instrs_float_convert_int d 64 intsize n op part rounding is_unsigned)
  | 128 => (execute_aarch64_instrs_float_convert_int d 128 intsize n op part rounding is_unsigned)
  | _ => sail_assert false "src/instrs64.sail:14400.22-14400.23"

def decode_fcvtau_float_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let part : Nat := 0
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 =>
      (do
        if ((((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) != 0b1101#4) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 128))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
    let (fltsize, is_unsigned, op, part, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding rmode)
          let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure (fltsize, is_unsigned, op, part, rounding)))
      else
        (do
          let (fltsize, is_unsigned, op, part, rounding) ← (( do
            if ((b__0 == (0x4#4 : (BitVec 4))) : Bool)
            then
              (do
                let rounding ← (FPRoundingMode (← (FPCR_read ())))
                let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_ItoF
                (pure (fltsize, is_unsigned, op, part, rounding)))
            else
              (do
                let (fltsize, is_unsigned, op, part, rounding) ← (( do
                  if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (let rounding : FPRounding := FPRounding_TIEAWAY
                    let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                    let op : FPConvOp := FPConvOp_CVT_FtoI
                    (pure (fltsize, is_unsigned, op, part, rounding)))
                  else
                    (do
                      let (fltsize, is_unsigned, op, part, rounding) ← (( do
                        if ((b__0 == (0xC#4 : (BitVec 4))) : Bool)
                        then
                          (do
                            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
                            then (sailThrow ((Error_Undefined ())) : SailM Unit)
                            else (pure ())
                            let op : FPConvOp :=
                              if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                              then FPConvOp_MOV_ItoF
                              else FPConvOp_MOV_FtoI
                            let part : Nat := 0
                            (pure (fltsize, is_unsigned, op, part, rounding)))
                        else
                          (do
                            let (fltsize, is_unsigned, op, part, rounding) ← (( do
                              if ((b__0 == (0xD#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (pure ())
                                  let op : FPConvOp :=
                                    if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                                    then FPConvOp_MOV_ItoF
                                    else FPConvOp_MOV_FtoI
                                  let part : Nat := 1
                                  let fltsize : Nat := 64
                                  (pure (fltsize, is_unsigned, op, part, rounding)))
                              else
                                (do
                                  let (is_unsigned, op, rounding) ← (( do
                                    if ((b__0 == (0xF#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        if ((! (← (HaveFJCVTZSExt ()))) : Bool)
                                        then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                        else (pure ())
                                        let rounding : FPRounding := FPRounding_ZERO
                                        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                                        let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                                        (pure (is_unsigned, op, rounding)))
                                    else sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
                                  (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                            (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                      (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
          (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
    (pure (fltsize, is_unsigned, op, part, rounding)) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part := part
  let fltsize := fltsize
  match fltsize with
  | 16 => (execute_aarch64_instrs_float_convert_int d 16 intsize n op part rounding is_unsigned)
  | 32 => (execute_aarch64_instrs_float_convert_int d 32 intsize n op part rounding is_unsigned)
  | 64 => (execute_aarch64_instrs_float_convert_int d 64 intsize n op part rounding is_unsigned)
  | 128 => (execute_aarch64_instrs_float_convert_int d 128 intsize n op part rounding is_unsigned)
  | _ => sail_assert false "src/instrs64.sail:14510.22-14510.23"

def decode_fcvtms_float_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let part : Nat := 0
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 =>
      (do
        if ((((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) != 0b1101#4) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 128))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
    let (fltsize, is_unsigned, op, part, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding rmode)
          let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure (fltsize, is_unsigned, op, part, rounding)))
      else
        (do
          let (fltsize, is_unsigned, op, part, rounding) ← (( do
            if ((b__0 == (0x4#4 : (BitVec 4))) : Bool)
            then
              (do
                let rounding ← (FPRoundingMode (← (FPCR_read ())))
                let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_ItoF
                (pure (fltsize, is_unsigned, op, part, rounding)))
            else
              (do
                let (fltsize, is_unsigned, op, part, rounding) ← (( do
                  if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (let rounding : FPRounding := FPRounding_TIEAWAY
                    let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                    let op : FPConvOp := FPConvOp_CVT_FtoI
                    (pure (fltsize, is_unsigned, op, part, rounding)))
                  else
                    (do
                      let (fltsize, is_unsigned, op, part, rounding) ← (( do
                        if ((b__0 == (0xC#4 : (BitVec 4))) : Bool)
                        then
                          (do
                            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
                            then (sailThrow ((Error_Undefined ())) : SailM Unit)
                            else (pure ())
                            let op : FPConvOp :=
                              if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                              then FPConvOp_MOV_ItoF
                              else FPConvOp_MOV_FtoI
                            let part : Nat := 0
                            (pure (fltsize, is_unsigned, op, part, rounding)))
                        else
                          (do
                            let (fltsize, is_unsigned, op, part, rounding) ← (( do
                              if ((b__0 == (0xD#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (pure ())
                                  let op : FPConvOp :=
                                    if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                                    then FPConvOp_MOV_ItoF
                                    else FPConvOp_MOV_FtoI
                                  let part : Nat := 1
                                  let fltsize : Nat := 64
                                  (pure (fltsize, is_unsigned, op, part, rounding)))
                              else
                                (do
                                  let (is_unsigned, op, rounding) ← (( do
                                    if ((b__0 == (0xF#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        if ((! (← (HaveFJCVTZSExt ()))) : Bool)
                                        then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                        else (pure ())
                                        let rounding : FPRounding := FPRounding_ZERO
                                        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                                        let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                                        (pure (is_unsigned, op, rounding)))
                                    else sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
                                  (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                            (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                      (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
          (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
    (pure (fltsize, is_unsigned, op, part, rounding)) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part := part
  let fltsize := fltsize
  match fltsize with
  | 16 => (execute_aarch64_instrs_float_convert_int d 16 intsize n op part rounding is_unsigned)
  | 32 => (execute_aarch64_instrs_float_convert_int d 32 intsize n op part rounding is_unsigned)
  | 64 => (execute_aarch64_instrs_float_convert_int d 64 intsize n op part rounding is_unsigned)
  | 128 => (execute_aarch64_instrs_float_convert_int d 128 intsize n op part rounding is_unsigned)
  | _ => sail_assert false "src/instrs64.sail:14620.22-14620.23"

def decode_fcvtmu_float_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let part : Nat := 0
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 =>
      (do
        if ((((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) != 0b1101#4) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 128))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
    let (fltsize, is_unsigned, op, part, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding rmode)
          let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure (fltsize, is_unsigned, op, part, rounding)))
      else
        (do
          let (fltsize, is_unsigned, op, part, rounding) ← (( do
            if ((b__0 == (0x4#4 : (BitVec 4))) : Bool)
            then
              (do
                let rounding ← (FPRoundingMode (← (FPCR_read ())))
                let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_ItoF
                (pure (fltsize, is_unsigned, op, part, rounding)))
            else
              (do
                let (fltsize, is_unsigned, op, part, rounding) ← (( do
                  if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (let rounding : FPRounding := FPRounding_TIEAWAY
                    let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                    let op : FPConvOp := FPConvOp_CVT_FtoI
                    (pure (fltsize, is_unsigned, op, part, rounding)))
                  else
                    (do
                      let (fltsize, is_unsigned, op, part, rounding) ← (( do
                        if ((b__0 == (0xC#4 : (BitVec 4))) : Bool)
                        then
                          (do
                            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
                            then (sailThrow ((Error_Undefined ())) : SailM Unit)
                            else (pure ())
                            let op : FPConvOp :=
                              if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                              then FPConvOp_MOV_ItoF
                              else FPConvOp_MOV_FtoI
                            let part : Nat := 0
                            (pure (fltsize, is_unsigned, op, part, rounding)))
                        else
                          (do
                            let (fltsize, is_unsigned, op, part, rounding) ← (( do
                              if ((b__0 == (0xD#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (pure ())
                                  let op : FPConvOp :=
                                    if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                                    then FPConvOp_MOV_ItoF
                                    else FPConvOp_MOV_FtoI
                                  let part : Nat := 1
                                  let fltsize : Nat := 64
                                  (pure (fltsize, is_unsigned, op, part, rounding)))
                              else
                                (do
                                  let (is_unsigned, op, rounding) ← (( do
                                    if ((b__0 == (0xF#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        if ((! (← (HaveFJCVTZSExt ()))) : Bool)
                                        then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                        else (pure ())
                                        let rounding : FPRounding := FPRounding_ZERO
                                        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                                        let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                                        (pure (is_unsigned, op, rounding)))
                                    else sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
                                  (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                            (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                      (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
          (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
    (pure (fltsize, is_unsigned, op, part, rounding)) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part := part
  let fltsize := fltsize
  match fltsize with
  | 16 => (execute_aarch64_instrs_float_convert_int d 16 intsize n op part rounding is_unsigned)
  | 32 => (execute_aarch64_instrs_float_convert_int d 32 intsize n op part rounding is_unsigned)
  | 64 => (execute_aarch64_instrs_float_convert_int d 64 intsize n op part rounding is_unsigned)
  | 128 => (execute_aarch64_instrs_float_convert_int d 128 intsize n op part rounding is_unsigned)
  | _ => sail_assert false "src/instrs64.sail:14730.22-14730.23"

def decode_fcvtns_float_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let part : Nat := 0
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 =>
      (do
        if ((((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) != 0b1101#4) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 128))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
    let (fltsize, is_unsigned, op, part, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding rmode)
          let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure (fltsize, is_unsigned, op, part, rounding)))
      else
        (do
          let (fltsize, is_unsigned, op, part, rounding) ← (( do
            if ((b__0 == (0x4#4 : (BitVec 4))) : Bool)
            then
              (do
                let rounding ← (FPRoundingMode (← (FPCR_read ())))
                let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_ItoF
                (pure (fltsize, is_unsigned, op, part, rounding)))
            else
              (do
                let (fltsize, is_unsigned, op, part, rounding) ← (( do
                  if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (let rounding : FPRounding := FPRounding_TIEAWAY
                    let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                    let op : FPConvOp := FPConvOp_CVT_FtoI
                    (pure (fltsize, is_unsigned, op, part, rounding)))
                  else
                    (do
                      let (fltsize, is_unsigned, op, part, rounding) ← (( do
                        if ((b__0 == (0xC#4 : (BitVec 4))) : Bool)
                        then
                          (do
                            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
                            then (sailThrow ((Error_Undefined ())) : SailM Unit)
                            else (pure ())
                            let op : FPConvOp :=
                              if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                              then FPConvOp_MOV_ItoF
                              else FPConvOp_MOV_FtoI
                            let part : Nat := 0
                            (pure (fltsize, is_unsigned, op, part, rounding)))
                        else
                          (do
                            let (fltsize, is_unsigned, op, part, rounding) ← (( do
                              if ((b__0 == (0xD#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (pure ())
                                  let op : FPConvOp :=
                                    if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                                    then FPConvOp_MOV_ItoF
                                    else FPConvOp_MOV_FtoI
                                  let part : Nat := 1
                                  let fltsize : Nat := 64
                                  (pure (fltsize, is_unsigned, op, part, rounding)))
                              else
                                (do
                                  let (is_unsigned, op, rounding) ← (( do
                                    if ((b__0 == (0xF#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        if ((! (← (HaveFJCVTZSExt ()))) : Bool)
                                        then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                        else (pure ())
                                        let rounding : FPRounding := FPRounding_ZERO
                                        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                                        let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                                        (pure (is_unsigned, op, rounding)))
                                    else sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
                                  (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                            (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                      (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
          (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
    (pure (fltsize, is_unsigned, op, part, rounding)) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part := part
  let fltsize := fltsize
  match fltsize with
  | 16 => (execute_aarch64_instrs_float_convert_int d 16 intsize n op part rounding is_unsigned)
  | 32 => (execute_aarch64_instrs_float_convert_int d 32 intsize n op part rounding is_unsigned)
  | 64 => (execute_aarch64_instrs_float_convert_int d 64 intsize n op part rounding is_unsigned)
  | 128 => (execute_aarch64_instrs_float_convert_int d 128 intsize n op part rounding is_unsigned)
  | _ => sail_assert false "src/instrs64.sail:14840.22-14840.23"

def decode_fcvtnu_float_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let part : Nat := 0
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 =>
      (do
        if ((((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) != 0b1101#4) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 128))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
    let (fltsize, is_unsigned, op, part, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding rmode)
          let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure (fltsize, is_unsigned, op, part, rounding)))
      else
        (do
          let (fltsize, is_unsigned, op, part, rounding) ← (( do
            if ((b__0 == (0x4#4 : (BitVec 4))) : Bool)
            then
              (do
                let rounding ← (FPRoundingMode (← (FPCR_read ())))
                let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_ItoF
                (pure (fltsize, is_unsigned, op, part, rounding)))
            else
              (do
                let (fltsize, is_unsigned, op, part, rounding) ← (( do
                  if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (let rounding : FPRounding := FPRounding_TIEAWAY
                    let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                    let op : FPConvOp := FPConvOp_CVT_FtoI
                    (pure (fltsize, is_unsigned, op, part, rounding)))
                  else
                    (do
                      let (fltsize, is_unsigned, op, part, rounding) ← (( do
                        if ((b__0 == (0xC#4 : (BitVec 4))) : Bool)
                        then
                          (do
                            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
                            then (sailThrow ((Error_Undefined ())) : SailM Unit)
                            else (pure ())
                            let op : FPConvOp :=
                              if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                              then FPConvOp_MOV_ItoF
                              else FPConvOp_MOV_FtoI
                            let part : Nat := 0
                            (pure (fltsize, is_unsigned, op, part, rounding)))
                        else
                          (do
                            let (fltsize, is_unsigned, op, part, rounding) ← (( do
                              if ((b__0 == (0xD#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (pure ())
                                  let op : FPConvOp :=
                                    if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                                    then FPConvOp_MOV_ItoF
                                    else FPConvOp_MOV_FtoI
                                  let part : Nat := 1
                                  let fltsize : Nat := 64
                                  (pure (fltsize, is_unsigned, op, part, rounding)))
                              else
                                (do
                                  let (is_unsigned, op, rounding) ← (( do
                                    if ((b__0 == (0xF#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        if ((! (← (HaveFJCVTZSExt ()))) : Bool)
                                        then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                        else (pure ())
                                        let rounding : FPRounding := FPRounding_ZERO
                                        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                                        let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                                        (pure (is_unsigned, op, rounding)))
                                    else sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
                                  (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                            (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                      (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
          (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
    (pure (fltsize, is_unsigned, op, part, rounding)) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part := part
  let fltsize := fltsize
  match fltsize with
  | 16 => (execute_aarch64_instrs_float_convert_int d 16 intsize n op part rounding is_unsigned)
  | 32 => (execute_aarch64_instrs_float_convert_int d 32 intsize n op part rounding is_unsigned)
  | 64 => (execute_aarch64_instrs_float_convert_int d 64 intsize n op part rounding is_unsigned)
  | 128 => (execute_aarch64_instrs_float_convert_int d 128 intsize n op part rounding is_unsigned)
  | _ => sail_assert false "src/instrs64.sail:14950.22-14950.23"

def decode_fcvtps_float_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let part : Nat := 0
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 =>
      (do
        if ((((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) != 0b1101#4) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 128))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
    let (fltsize, is_unsigned, op, part, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding rmode)
          let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure (fltsize, is_unsigned, op, part, rounding)))
      else
        (do
          let (fltsize, is_unsigned, op, part, rounding) ← (( do
            if ((b__0 == (0x4#4 : (BitVec 4))) : Bool)
            then
              (do
                let rounding ← (FPRoundingMode (← (FPCR_read ())))
                let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_ItoF
                (pure (fltsize, is_unsigned, op, part, rounding)))
            else
              (do
                let (fltsize, is_unsigned, op, part, rounding) ← (( do
                  if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (let rounding : FPRounding := FPRounding_TIEAWAY
                    let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                    let op : FPConvOp := FPConvOp_CVT_FtoI
                    (pure (fltsize, is_unsigned, op, part, rounding)))
                  else
                    (do
                      let (fltsize, is_unsigned, op, part, rounding) ← (( do
                        if ((b__0 == (0xC#4 : (BitVec 4))) : Bool)
                        then
                          (do
                            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
                            then (sailThrow ((Error_Undefined ())) : SailM Unit)
                            else (pure ())
                            let op : FPConvOp :=
                              if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                              then FPConvOp_MOV_ItoF
                              else FPConvOp_MOV_FtoI
                            let part : Nat := 0
                            (pure (fltsize, is_unsigned, op, part, rounding)))
                        else
                          (do
                            let (fltsize, is_unsigned, op, part, rounding) ← (( do
                              if ((b__0 == (0xD#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (pure ())
                                  let op : FPConvOp :=
                                    if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                                    then FPConvOp_MOV_ItoF
                                    else FPConvOp_MOV_FtoI
                                  let part : Nat := 1
                                  let fltsize : Nat := 64
                                  (pure (fltsize, is_unsigned, op, part, rounding)))
                              else
                                (do
                                  let (is_unsigned, op, rounding) ← (( do
                                    if ((b__0 == (0xF#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        if ((! (← (HaveFJCVTZSExt ()))) : Bool)
                                        then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                        else (pure ())
                                        let rounding : FPRounding := FPRounding_ZERO
                                        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                                        let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                                        (pure (is_unsigned, op, rounding)))
                                    else sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
                                  (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                            (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                      (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
          (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
    (pure (fltsize, is_unsigned, op, part, rounding)) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part := part
  let fltsize := fltsize
  match fltsize with
  | 16 => (execute_aarch64_instrs_float_convert_int d 16 intsize n op part rounding is_unsigned)
  | 32 => (execute_aarch64_instrs_float_convert_int d 32 intsize n op part rounding is_unsigned)
  | 64 => (execute_aarch64_instrs_float_convert_int d 64 intsize n op part rounding is_unsigned)
  | 128 => (execute_aarch64_instrs_float_convert_int d 128 intsize n op part rounding is_unsigned)
  | _ => sail_assert false "src/instrs64.sail:15060.22-15060.23"

def decode_fcvtpu_float_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let part : Nat := 0
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 =>
      (do
        if ((((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) != 0b1101#4) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 128))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
    let (fltsize, is_unsigned, op, part, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding rmode)
          let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure (fltsize, is_unsigned, op, part, rounding)))
      else
        (do
          let (fltsize, is_unsigned, op, part, rounding) ← (( do
            if ((b__0 == (0x4#4 : (BitVec 4))) : Bool)
            then
              (do
                let rounding ← (FPRoundingMode (← (FPCR_read ())))
                let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_ItoF
                (pure (fltsize, is_unsigned, op, part, rounding)))
            else
              (do
                let (fltsize, is_unsigned, op, part, rounding) ← (( do
                  if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (let rounding : FPRounding := FPRounding_TIEAWAY
                    let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                    let op : FPConvOp := FPConvOp_CVT_FtoI
                    (pure (fltsize, is_unsigned, op, part, rounding)))
                  else
                    (do
                      let (fltsize, is_unsigned, op, part, rounding) ← (( do
                        if ((b__0 == (0xC#4 : (BitVec 4))) : Bool)
                        then
                          (do
                            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
                            then (sailThrow ((Error_Undefined ())) : SailM Unit)
                            else (pure ())
                            let op : FPConvOp :=
                              if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                              then FPConvOp_MOV_ItoF
                              else FPConvOp_MOV_FtoI
                            let part : Nat := 0
                            (pure (fltsize, is_unsigned, op, part, rounding)))
                        else
                          (do
                            let (fltsize, is_unsigned, op, part, rounding) ← (( do
                              if ((b__0 == (0xD#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (pure ())
                                  let op : FPConvOp :=
                                    if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                                    then FPConvOp_MOV_ItoF
                                    else FPConvOp_MOV_FtoI
                                  let part : Nat := 1
                                  let fltsize : Nat := 64
                                  (pure (fltsize, is_unsigned, op, part, rounding)))
                              else
                                (do
                                  let (is_unsigned, op, rounding) ← (( do
                                    if ((b__0 == (0xF#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        if ((! (← (HaveFJCVTZSExt ()))) : Bool)
                                        then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                        else (pure ())
                                        let rounding : FPRounding := FPRounding_ZERO
                                        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                                        let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                                        (pure (is_unsigned, op, rounding)))
                                    else sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
                                  (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                            (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                      (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
          (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
    (pure (fltsize, is_unsigned, op, part, rounding)) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part := part
  let fltsize := fltsize
  match fltsize with
  | 16 => (execute_aarch64_instrs_float_convert_int d 16 intsize n op part rounding is_unsigned)
  | 32 => (execute_aarch64_instrs_float_convert_int d 32 intsize n op part rounding is_unsigned)
  | 64 => (execute_aarch64_instrs_float_convert_int d 64 intsize n op part rounding is_unsigned)
  | 128 => (execute_aarch64_instrs_float_convert_int d 128 intsize n op part rounding is_unsigned)
  | _ => sail_assert false "src/instrs64.sail:15170.22-15170.23"

def decode_fcvtzs_float_int_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let part : Nat := 0
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 =>
      (do
        if ((((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) != 0b1101#4) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 128))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
    let (fltsize, is_unsigned, op, part, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding rmode)
          let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure (fltsize, is_unsigned, op, part, rounding)))
      else
        (do
          let (fltsize, is_unsigned, op, part, rounding) ← (( do
            if ((b__0 == (0x4#4 : (BitVec 4))) : Bool)
            then
              (do
                let rounding ← (FPRoundingMode (← (FPCR_read ())))
                let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_ItoF
                (pure (fltsize, is_unsigned, op, part, rounding)))
            else
              (do
                let (fltsize, is_unsigned, op, part, rounding) ← (( do
                  if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (let rounding : FPRounding := FPRounding_TIEAWAY
                    let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                    let op : FPConvOp := FPConvOp_CVT_FtoI
                    (pure (fltsize, is_unsigned, op, part, rounding)))
                  else
                    (do
                      let (fltsize, is_unsigned, op, part, rounding) ← (( do
                        if ((b__0 == (0xC#4 : (BitVec 4))) : Bool)
                        then
                          (do
                            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
                            then (sailThrow ((Error_Undefined ())) : SailM Unit)
                            else (pure ())
                            let op : FPConvOp :=
                              if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                              then FPConvOp_MOV_ItoF
                              else FPConvOp_MOV_FtoI
                            let part : Nat := 0
                            (pure (fltsize, is_unsigned, op, part, rounding)))
                        else
                          (do
                            let (fltsize, is_unsigned, op, part, rounding) ← (( do
                              if ((b__0 == (0xD#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (pure ())
                                  let op : FPConvOp :=
                                    if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                                    then FPConvOp_MOV_ItoF
                                    else FPConvOp_MOV_FtoI
                                  let part : Nat := 1
                                  let fltsize : Nat := 64
                                  (pure (fltsize, is_unsigned, op, part, rounding)))
                              else
                                (do
                                  let (is_unsigned, op, rounding) ← (( do
                                    if ((b__0 == (0xF#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        if ((! (← (HaveFJCVTZSExt ()))) : Bool)
                                        then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                        else (pure ())
                                        let rounding : FPRounding := FPRounding_ZERO
                                        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                                        let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                                        (pure (is_unsigned, op, rounding)))
                                    else sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
                                  (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                            (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                      (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
          (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
    (pure (fltsize, is_unsigned, op, part, rounding)) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part := part
  let fltsize := fltsize
  match fltsize with
  | 16 => (execute_aarch64_instrs_float_convert_int d 16 intsize n op part rounding is_unsigned)
  | 32 => (execute_aarch64_instrs_float_convert_int d 32 intsize n op part rounding is_unsigned)
  | 64 => (execute_aarch64_instrs_float_convert_int d 64 intsize n op part rounding is_unsigned)
  | 128 => (execute_aarch64_instrs_float_convert_int d 128 intsize n op part rounding is_unsigned)
  | _ => sail_assert false "src/instrs64.sail:15280.22-15280.23"

def decode_fcvtzu_float_int_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let part : Nat := 0
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 =>
      (do
        if ((((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) != 0b1101#4) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 128))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
    let (fltsize, is_unsigned, op, part, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding rmode)
          let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure (fltsize, is_unsigned, op, part, rounding)))
      else
        (do
          let (fltsize, is_unsigned, op, part, rounding) ← (( do
            if ((b__0 == (0x4#4 : (BitVec 4))) : Bool)
            then
              (do
                let rounding ← (FPRoundingMode (← (FPCR_read ())))
                let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_ItoF
                (pure (fltsize, is_unsigned, op, part, rounding)))
            else
              (do
                let (fltsize, is_unsigned, op, part, rounding) ← (( do
                  if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (let rounding : FPRounding := FPRounding_TIEAWAY
                    let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                    let op : FPConvOp := FPConvOp_CVT_FtoI
                    (pure (fltsize, is_unsigned, op, part, rounding)))
                  else
                    (do
                      let (fltsize, is_unsigned, op, part, rounding) ← (( do
                        if ((b__0 == (0xC#4 : (BitVec 4))) : Bool)
                        then
                          (do
                            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
                            then (sailThrow ((Error_Undefined ())) : SailM Unit)
                            else (pure ())
                            let op : FPConvOp :=
                              if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                              then FPConvOp_MOV_ItoF
                              else FPConvOp_MOV_FtoI
                            let part : Nat := 0
                            (pure (fltsize, is_unsigned, op, part, rounding)))
                        else
                          (do
                            let (fltsize, is_unsigned, op, part, rounding) ← (( do
                              if ((b__0 == (0xD#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (pure ())
                                  let op : FPConvOp :=
                                    if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                                    then FPConvOp_MOV_ItoF
                                    else FPConvOp_MOV_FtoI
                                  let part : Nat := 1
                                  let fltsize : Nat := 64
                                  (pure (fltsize, is_unsigned, op, part, rounding)))
                              else
                                (do
                                  let (is_unsigned, op, rounding) ← (( do
                                    if ((b__0 == (0xF#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        if ((! (← (HaveFJCVTZSExt ()))) : Bool)
                                        then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                        else (pure ())
                                        let rounding : FPRounding := FPRounding_ZERO
                                        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                                        let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                                        (pure (is_unsigned, op, rounding)))
                                    else sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
                                  (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                            (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                      (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
          (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
    (pure (fltsize, is_unsigned, op, part, rounding)) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part := part
  let fltsize := fltsize
  match fltsize with
  | 16 => (execute_aarch64_instrs_float_convert_int d 16 intsize n op part rounding is_unsigned)
  | 32 => (execute_aarch64_instrs_float_convert_int d 32 intsize n op part rounding is_unsigned)
  | 64 => (execute_aarch64_instrs_float_convert_int d 64 intsize n op part rounding is_unsigned)
  | 128 => (execute_aarch64_instrs_float_convert_int d 128 intsize n op part rounding is_unsigned)
  | _ => sail_assert false "src/instrs64.sail:15390.22-15390.23"

def decode_fjcvtzs_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let part : Nat := 0
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 =>
      (do
        if ((((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) != 0b1101#4) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 128))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
    let (fltsize, is_unsigned, op, part, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding rmode)
          let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure (fltsize, is_unsigned, op, part, rounding)))
      else
        (do
          let (fltsize, is_unsigned, op, part, rounding) ← (( do
            if ((b__0 == (0x4#4 : (BitVec 4))) : Bool)
            then
              (do
                let rounding ← (FPRoundingMode (← (FPCR_read ())))
                let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_ItoF
                (pure (fltsize, is_unsigned, op, part, rounding)))
            else
              (do
                let (fltsize, is_unsigned, op, part, rounding) ← (( do
                  if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (let rounding : FPRounding := FPRounding_TIEAWAY
                    let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                    let op : FPConvOp := FPConvOp_CVT_FtoI
                    (pure (fltsize, is_unsigned, op, part, rounding)))
                  else
                    (do
                      let (fltsize, is_unsigned, op, part, rounding) ← (( do
                        if ((b__0 == (0xC#4 : (BitVec 4))) : Bool)
                        then
                          (do
                            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
                            then (sailThrow ((Error_Undefined ())) : SailM Unit)
                            else (pure ())
                            let op : FPConvOp :=
                              if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                              then FPConvOp_MOV_ItoF
                              else FPConvOp_MOV_FtoI
                            let part : Nat := 0
                            (pure (fltsize, is_unsigned, op, part, rounding)))
                        else
                          (do
                            let (fltsize, is_unsigned, op, part, rounding) ← (( do
                              if ((b__0 == (0xD#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (pure ())
                                  let op : FPConvOp :=
                                    if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                                    then FPConvOp_MOV_ItoF
                                    else FPConvOp_MOV_FtoI
                                  let part : Nat := 1
                                  let fltsize : Nat := 64
                                  (pure (fltsize, is_unsigned, op, part, rounding)))
                              else
                                (do
                                  let (is_unsigned, op, rounding) ← (( do
                                    if ((b__0 == (0xF#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        if ((! (← (HaveFJCVTZSExt ()))) : Bool)
                                        then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                        else (pure ())
                                        let rounding : FPRounding := FPRounding_ZERO
                                        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                                        let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                                        (pure (is_unsigned, op, rounding)))
                                    else sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
                                  (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                            (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                      (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
          (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
    (pure (fltsize, is_unsigned, op, part, rounding)) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part := part
  let fltsize := fltsize
  match fltsize with
  | 16 => (execute_aarch64_instrs_float_convert_int d 16 intsize n op part rounding is_unsigned)
  | 32 => (execute_aarch64_instrs_float_convert_int d 32 intsize n op part rounding is_unsigned)
  | 64 => (execute_aarch64_instrs_float_convert_int d 64 intsize n op part rounding is_unsigned)
  | 128 => (execute_aarch64_instrs_float_convert_int d 128 intsize n op part rounding is_unsigned)
  | _ => sail_assert false "src/instrs64.sail:15500.22-15500.23"

def decode_fmov_float_gen_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let part : Nat := 0
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 =>
      (do
        if ((((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) != 0b1101#4) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 128))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
    let (fltsize, is_unsigned, op, part, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding rmode)
          let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure (fltsize, is_unsigned, op, part, rounding)))
      else
        (do
          let (fltsize, is_unsigned, op, part, rounding) ← (( do
            if ((b__0 == (0x4#4 : (BitVec 4))) : Bool)
            then
              (do
                let rounding ← (FPRoundingMode (← (FPCR_read ())))
                let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_ItoF
                (pure (fltsize, is_unsigned, op, part, rounding)))
            else
              (do
                let (fltsize, is_unsigned, op, part, rounding) ← (( do
                  if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (let rounding : FPRounding := FPRounding_TIEAWAY
                    let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                    let op : FPConvOp := FPConvOp_CVT_FtoI
                    (pure (fltsize, is_unsigned, op, part, rounding)))
                  else
                    (do
                      let (fltsize, is_unsigned, op, part, rounding) ← (( do
                        if ((b__0 == (0xC#4 : (BitVec 4))) : Bool)
                        then
                          (do
                            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
                            then (sailThrow ((Error_Undefined ())) : SailM Unit)
                            else (pure ())
                            let op : FPConvOp :=
                              if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                              then FPConvOp_MOV_ItoF
                              else FPConvOp_MOV_FtoI
                            let part : Nat := 0
                            (pure (fltsize, is_unsigned, op, part, rounding)))
                        else
                          (do
                            let (fltsize, is_unsigned, op, part, rounding) ← (( do
                              if ((b__0 == (0xD#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (pure ())
                                  let op : FPConvOp :=
                                    if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                                    then FPConvOp_MOV_ItoF
                                    else FPConvOp_MOV_FtoI
                                  let part : Nat := 1
                                  let fltsize : Nat := 64
                                  (pure (fltsize, is_unsigned, op, part, rounding)))
                              else
                                (do
                                  let (is_unsigned, op, rounding) ← (( do
                                    if ((b__0 == (0xF#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        if ((! (← (HaveFJCVTZSExt ()))) : Bool)
                                        then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                        else (pure ())
                                        let rounding : FPRounding := FPRounding_ZERO
                                        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                                        let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                                        (pure (is_unsigned, op, rounding)))
                                    else sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
                                  (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                            (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                      (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
          (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
    (pure (fltsize, is_unsigned, op, part, rounding)) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part := part
  let fltsize := fltsize
  match fltsize with
  | 16 => (execute_aarch64_instrs_float_convert_int d 16 intsize n op part rounding is_unsigned)
  | 32 => (execute_aarch64_instrs_float_convert_int d 32 intsize n op part rounding is_unsigned)
  | 64 => (execute_aarch64_instrs_float_convert_int d 64 intsize n op part rounding is_unsigned)
  | 128 => (execute_aarch64_instrs_float_convert_int d 128 intsize n op part rounding is_unsigned)
  | _ => sail_assert false "src/instrs64.sail:15610.22-15610.23"

def decode_scvtf_float_int_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let part : Nat := 0
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 =>
      (do
        if ((((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) != 0b1101#4) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 128))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
    let (fltsize, is_unsigned, op, part, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding rmode)
          let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure (fltsize, is_unsigned, op, part, rounding)))
      else
        (do
          let (fltsize, is_unsigned, op, part, rounding) ← (( do
            if ((b__0 == (0x4#4 : (BitVec 4))) : Bool)
            then
              (do
                let rounding ← (FPRoundingMode (← (FPCR_read ())))
                let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_ItoF
                (pure (fltsize, is_unsigned, op, part, rounding)))
            else
              (do
                let (fltsize, is_unsigned, op, part, rounding) ← (( do
                  if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (let rounding : FPRounding := FPRounding_TIEAWAY
                    let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                    let op : FPConvOp := FPConvOp_CVT_FtoI
                    (pure (fltsize, is_unsigned, op, part, rounding)))
                  else
                    (do
                      let (fltsize, is_unsigned, op, part, rounding) ← (( do
                        if ((b__0 == (0xC#4 : (BitVec 4))) : Bool)
                        then
                          (do
                            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
                            then (sailThrow ((Error_Undefined ())) : SailM Unit)
                            else (pure ())
                            let op : FPConvOp :=
                              if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                              then FPConvOp_MOV_ItoF
                              else FPConvOp_MOV_FtoI
                            let part : Nat := 0
                            (pure (fltsize, is_unsigned, op, part, rounding)))
                        else
                          (do
                            let (fltsize, is_unsigned, op, part, rounding) ← (( do
                              if ((b__0 == (0xD#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (pure ())
                                  let op : FPConvOp :=
                                    if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                                    then FPConvOp_MOV_ItoF
                                    else FPConvOp_MOV_FtoI
                                  let part : Nat := 1
                                  let fltsize : Nat := 64
                                  (pure (fltsize, is_unsigned, op, part, rounding)))
                              else
                                (do
                                  let (is_unsigned, op, rounding) ← (( do
                                    if ((b__0 == (0xF#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        if ((! (← (HaveFJCVTZSExt ()))) : Bool)
                                        then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                        else (pure ())
                                        let rounding : FPRounding := FPRounding_ZERO
                                        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                                        let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                                        (pure (is_unsigned, op, rounding)))
                                    else sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
                                  (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                            (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                      (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
          (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
    (pure (fltsize, is_unsigned, op, part, rounding)) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part := part
  let fltsize := fltsize
  match fltsize with
  | 16 => (execute_aarch64_instrs_float_convert_int d 16 intsize n op part rounding is_unsigned)
  | 32 => (execute_aarch64_instrs_float_convert_int d 32 intsize n op part rounding is_unsigned)
  | 64 => (execute_aarch64_instrs_float_convert_int d 64 intsize n op part rounding is_unsigned)
  | 128 => (execute_aarch64_instrs_float_convert_int d 128 intsize n op part rounding is_unsigned)
  | _ => sail_assert false "src/instrs64.sail:15720.22-15720.23"

def decode_ucvtf_float_int_aarch64_instrs_float_convert_int (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let part : Nat := 0
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 =>
      (do
        if ((((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) != 0b1101#4) : Bool)
        then (sailThrow ((Error_Undefined ())) : SailM Unit)
        else (pure ())
        (pure 128))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let (fltsize, is_unsigned, op, part, rounding) ← (( do
    let b__0 := ((Sail.BitVec.extractLsb opcode 2 1) +++ rmode)
    let (fltsize, is_unsigned, op, part, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 3 2) == (0b00#2 : (BitVec 2))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding rmode)
          let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
          let op : FPConvOp := FPConvOp_CVT_FtoI
          (pure (fltsize, is_unsigned, op, part, rounding)))
      else
        (do
          let (fltsize, is_unsigned, op, part, rounding) ← (( do
            if ((b__0 == (0x4#4 : (BitVec 4))) : Bool)
            then
              (do
                let rounding ← (FPRoundingMode (← (FPCR_read ())))
                let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                let op : FPConvOp := FPConvOp_CVT_ItoF
                (pure (fltsize, is_unsigned, op, part, rounding)))
            else
              (do
                let (fltsize, is_unsigned, op, part, rounding) ← (( do
                  if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                  then
                    (let rounding : FPRounding := FPRounding_TIEAWAY
                    let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                    let op : FPConvOp := FPConvOp_CVT_FtoI
                    (pure (fltsize, is_unsigned, op, part, rounding)))
                  else
                    (do
                      let (fltsize, is_unsigned, op, part, rounding) ← (( do
                        if ((b__0 == (0xC#4 : (BitVec 4))) : Bool)
                        then
                          (do
                            if (((fltsize != 16) && ((fltsize != intsize) : Bool)) : Bool)
                            then (sailThrow ((Error_Undefined ())) : SailM Unit)
                            else (pure ())
                            let op : FPConvOp :=
                              if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                              then FPConvOp_MOV_ItoF
                              else FPConvOp_MOV_FtoI
                            let part : Nat := 0
                            (pure (fltsize, is_unsigned, op, part, rounding)))
                        else
                          (do
                            let (fltsize, is_unsigned, op, part, rounding) ← (( do
                              if ((b__0 == (0xD#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if (((intsize != 64) || ((fltsize != 128) : Bool)) : Bool)
                                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                  else (pure ())
                                  let op : FPConvOp :=
                                    if (((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1) : Bool)
                                    then FPConvOp_MOV_ItoF
                                    else FPConvOp_MOV_FtoI
                                  let part : Nat := 1
                                  let fltsize : Nat := 64
                                  (pure (fltsize, is_unsigned, op, part, rounding)))
                              else
                                (do
                                  let (is_unsigned, op, rounding) ← (( do
                                    if ((b__0 == (0xF#4 : (BitVec 4))) : Bool)
                                    then
                                      (do
                                        if ((! (← (HaveFJCVTZSExt ()))) : Bool)
                                        then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                        else (pure ())
                                        let rounding : FPRounding := FPRounding_ZERO
                                        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
                                        let op : FPConvOp := FPConvOp_CVT_FtoI_JS
                                        (pure (is_unsigned, op, rounding)))
                                    else sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
                                  (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                            (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                      (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
                (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
          (pure (fltsize, is_unsigned, op, part, rounding))) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
    (pure (fltsize, is_unsigned, op, part, rounding)) ) : SailM (Int × Bool × FPConvOp × Int × FPRounding) )
  let op := op
  let part := part
  let fltsize := fltsize
  match fltsize with
  | 16 => (execute_aarch64_instrs_float_convert_int d 16 intsize n op part rounding is_unsigned)
  | 32 => (execute_aarch64_instrs_float_convert_int d 32 intsize n op part rounding is_unsigned)
  | 64 => (execute_aarch64_instrs_float_convert_int d 64 intsize n op part rounding is_unsigned)
  | 128 => (execute_aarch64_instrs_float_convert_int d 128 intsize n op part rounding is_unsigned)
  | _ => sail_assert false "src/instrs64.sail:15830.22-15830.23"

def decode_fcvtl_advsimd_aarch64_instrs_vector_arithmetic_unary_float_widen (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 16 (BitVec.toNat sz))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (fdiv_int datasize esize)
  sail_assert ((esize == 16) || (esize == 32)) "src/instrs64.sail:15869.41-15869.42"
  (execute_aarch64_instrs_vector_arithmetic_unary_float_widen d datasize elements esize n part)

def decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtms_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtmu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtns_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtnu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtps_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtpu_advsimd_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtzs_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtzu_advsimd_int_aarch64_instrs_vector_arithmetic_unary_float_conv_float_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding ← (( do (FPDecodeRounding (o1 +++ o2)) ) : SailM FPRounding )
  let is_unsigned : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd d datasize elements esize n rounding is_unsigned)

def decode_fcvtn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_narrow (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 16 (BitVec.toNat sz))
  let datasize := 64
  let part := (BitVec.toNat Q)
  let elements := (fdiv_int datasize esize)
  sail_assert ((esize == 16) || (esize == 32)) "src/instrs64.sail:16763.41-16763.42"
  (execute_aarch64_instrs_vector_arithmetic_unary_float_narrow d datasize elements esize n part)

def decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((sz == 0#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let datasize := esize
  let elements := 1
  let part := 0
  (execute_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd d datasize elements esize n part)

def decode_fcvtxn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_xtn_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if ((sz == 0#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let datasize := 64
  let elements := 2
  let part := (BitVec.toNat Q)
  (execute_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd d datasize elements esize n part)

def decode_fcvtzs_float_fix_aarch64_instrs_float_convert_fix (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let fltsize := fltsize
  if (((sf == 0#1) && ((BitVec.join1 [(BitVec.access scale 5)]) == 0#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let fracbits := (64 -i (BitVec.toNat scale))
  let (is_unsigned, op, rounding) ← (( do
    match (((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) : BitVec 4) with
    | 0b0011 =>
      (let rounding : FPRounding := FPRounding_ZERO
      let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
      let op : FPConvOp := FPConvOp_CVT_FtoI
      (pure (is_unsigned, op, rounding)))
    | 0b0100 =>
      (do
        let rounding ← (FPRoundingMode (← (FPCR_read ())))
        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_ItoF
        (pure (is_unsigned, op, rounding)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
  (execute_aarch64_instrs_float_convert_fix d fltsize fracbits intsize n op rounding is_unsigned)

def decode_fcvtzu_float_fix_aarch64_instrs_float_convert_fix (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let fltsize := fltsize
  if (((sf == 0#1) && ((BitVec.join1 [(BitVec.access scale 5)]) == 0#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let fracbits := (64 -i (BitVec.toNat scale))
  let (is_unsigned, op, rounding) ← (( do
    match (((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) : BitVec 4) with
    | 0b0011 =>
      (let rounding : FPRounding := FPRounding_ZERO
      let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
      let op : FPConvOp := FPConvOp_CVT_FtoI
      (pure (is_unsigned, op, rounding)))
    | 0b0100 =>
      (do
        let rounding ← (FPRoundingMode (← (FPCR_read ())))
        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_ItoF
        (pure (is_unsigned, op, rounding)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
  (execute_aarch64_instrs_float_convert_fix d fltsize fracbits intsize n op rounding is_unsigned)

def decode_scvtf_float_fix_aarch64_instrs_float_convert_fix (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let fltsize := fltsize
  if (((sf == 0#1) && ((BitVec.join1 [(BitVec.access scale 5)]) == 0#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let fracbits := (64 -i (BitVec.toNat scale))
  let (is_unsigned, op, rounding) ← (( do
    match (((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) : BitVec 4) with
    | 0b0011 =>
      (let rounding : FPRounding := FPRounding_ZERO
      let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
      let op : FPConvOp := FPConvOp_CVT_FtoI
      (pure (is_unsigned, op, rounding)))
    | 0b0100 =>
      (do
        let rounding ← (FPRoundingMode (← (FPCR_read ())))
        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_ItoF
        (pure (is_unsigned, op, rounding)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
  (execute_aarch64_instrs_float_convert_fix d fltsize fracbits intsize n op rounding is_unsigned)

def decode_ucvtf_float_fix_aarch64_instrs_float_convert_fix (Rd : (BitVec 5)) (Rn : (BitVec 5)) (scale : (BitVec 6)) (opcode : (BitVec 3)) (rmode : (BitVec 2)) (ftype : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let intsize :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let fltsize : Nat := 16
  let op ← (( do (undefined_FPConvOp ()) ) : SailM FPConvOp )
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let fltsize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let fltsize := fltsize
  if (((sf == 0#1) && ((BitVec.join1 [(BitVec.access scale 5)]) == 0#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let fracbits := (64 -i (BitVec.toNat scale))
  let (is_unsigned, op, rounding) ← (( do
    match (((Sail.BitVec.extractLsb opcode 2 1) +++ rmode) : BitVec 4) with
    | 0b0011 =>
      (let rounding : FPRounding := FPRounding_ZERO
      let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
      let op : FPConvOp := FPConvOp_CVT_FtoI
      (pure (is_unsigned, op, rounding)))
    | 0b0100 =>
      (do
        let rounding ← (FPRoundingMode (← (FPCR_read ())))
        let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opcode 0)]) == 1#1)
        let op : FPConvOp := FPConvOp_CVT_ItoF
        (pure (is_unsigned, op, rounding)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × FPConvOp × FPRounding) )
  (execute_aarch64_instrs_float_convert_fix d fltsize fracbits intsize n op rounding is_unsigned)

def decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
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
  let rounding : FPRounding := FPRounding_ZERO
  (execute_aarch64_instrs_vector_shift_conv_float_sisd d datasize elements esize fracbits n rounding is_unsigned)

def decode_fcvtzs_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding : FPRounding := FPRounding_ZERO
  (execute_aarch64_instrs_vector_shift_conv_float_sisd d datasize elements esize fracbits n rounding is_unsigned)

def decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
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
  let rounding : FPRounding := FPRounding_ZERO
  (execute_aarch64_instrs_vector_shift_conv_float_sisd d datasize elements esize fracbits n rounding is_unsigned)

def decode_fcvtzu_advsimd_fix_aarch64_instrs_vector_shift_conv_float_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (immb : (BitVec 3)) (immh : (BitVec 4)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let rounding : FPRounding := FPRounding_ZERO
  (execute_aarch64_instrs_vector_shift_conv_float_sisd d datasize elements esize fracbits n rounding is_unsigned)

def decode_fdiv_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16 d datasize elements esize m n)

def decode_fdiv_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_div (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_div_fp16 d datasize elements esize m n)

def decode_fdiv_float_aarch64_instrs_float_arithmetic_div (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
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
  (execute_aarch64_instrs_float_arithmetic_div d esize m n)

def decode_fmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (o1 : (BitVec 1)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let a := (BitVec.toNat Ra)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
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
  let opa_neg : Bool := (o1 == 1#1)
  let op1_neg : Bool := (o0 != o1)
  (execute_aarch64_instrs_float_arithmetic_mul_add_sub a d esize m n op1_neg opa_neg)

def decode_fmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (o1 : (BitVec 1)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let a := (BitVec.toNat Ra)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
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
  let opa_neg : Bool := (o1 == 1#1)
  let op1_neg : Bool := (o0 != o1)
  (execute_aarch64_instrs_float_arithmetic_mul_add_sub a d esize m n op1_neg opa_neg)

def decode_fnmadd_float_aarch64_instrs_float_arithmetic_mul_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (o1 : (BitVec 1)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let a := (BitVec.toNat Ra)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
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
  let opa_neg : Bool := (o1 == 1#1)
  let op1_neg : Bool := (o0 != o1)
  (execute_aarch64_instrs_float_arithmetic_mul_add_sub a d esize m n op1_neg opa_neg)

def decode_fnmsub_float_aarch64_instrs_float_arithmetic_mul_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (o1 : (BitVec 1)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let a := (BitVec.toNat Ra)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
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
  let opa_neg : Bool := (o1 == 1#1)
  let op1_neg : Bool := (o0 != o1)
  (execute_aarch64_instrs_float_arithmetic_mul_add_sub a d esize m n op1_neg opa_neg)

def decode_fmax_float_aarch64_instrs_float_arithmetic_max_min (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
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
  let operation ← (( do (undefined_FPMaxMinOp ()) ) : SailM FPMaxMinOp )
  let operation : FPMaxMinOp :=
    match (op : BitVec 2) with
    | 0b00 => FPMaxMinOp_MAX
    | 0b01 => FPMaxMinOp_MIN
    | 0b10 => FPMaxMinOp_MAXNUM
    | _ => FPMaxMinOp_MINNUM
  let operation := operation
  (execute_aarch64_instrs_float_arithmetic_max_min d esize m n operation)

def decode_fmaxnm_float_aarch64_instrs_float_arithmetic_max_min (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
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
  let operation ← (( do (undefined_FPMaxMinOp ()) ) : SailM FPMaxMinOp )
  let operation : FPMaxMinOp :=
    match (op : BitVec 2) with
    | 0b00 => FPMaxMinOp_MAX
    | 0b01 => FPMaxMinOp_MIN
    | 0b10 => FPMaxMinOp_MAXNUM
    | _ => FPMaxMinOp_MINNUM
  let operation := operation
  (execute_aarch64_instrs_float_arithmetic_max_min d esize m n operation)

def decode_fmin_float_aarch64_instrs_float_arithmetic_max_min (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
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
  let operation ← (( do (undefined_FPMaxMinOp ()) ) : SailM FPMaxMinOp )
  let operation : FPMaxMinOp :=
    match (op : BitVec 2) with
    | 0b00 => FPMaxMinOp_MAX
    | 0b01 => FPMaxMinOp_MIN
    | 0b10 => FPMaxMinOp_MAXNUM
    | _ => FPMaxMinOp_MINNUM
  let operation := operation
  (execute_aarch64_instrs_float_arithmetic_max_min d esize m n operation)

def decode_fminnm_float_aarch64_instrs_float_arithmetic_max_min (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
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
  let operation ← (( do (undefined_FPMaxMinOp ()) ) : SailM FPMaxMinOp )
  let operation : FPMaxMinOp :=
    match (op : BitVec 2) with
    | 0b00 => FPMaxMinOp_MAX
    | 0b01 => FPMaxMinOp_MIN
    | 0b10 => FPMaxMinOp_MAXNUM
    | _ => FPMaxMinOp_MINNUM
  let operation := operation
  (execute_aarch64_instrs_float_arithmetic_max_min d esize m n operation)

def decode_fmax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (o1 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 d datasize elements esize m minimum n pair)

def decode_fmax_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 d datasize elements esize m minimum n pair)

def decode_fmaxp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (o1 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 d datasize elements esize m minimum n pair)

def decode_fmaxp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 d datasize elements esize m minimum n pair)

def decode_fmin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (o1 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 d datasize elements esize m minimum n pair)

def decode_fmin_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 d datasize elements esize m minimum n pair)

def decode_fminp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (o1 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 d datasize elements esize m minimum n pair)

def decode_fminp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_1985 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_1985 d datasize elements esize m minimum n pair)

def decode_fmaxnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (a : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (a == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 d datasize elements esize m minimum n pair)

def decode_fmaxnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 d datasize elements esize m minimum n pair)

def decode_fmaxnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (a : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (a == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 d datasize elements esize m minimum n pair)

def decode_fmaxnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 d datasize elements esize m minimum n pair)

def decode_fminnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (a : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (a == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 d datasize elements esize m minimum n pair)

def decode_fminnm_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 d datasize elements esize m minimum n pair)

def decode_fminnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (a : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (a == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 d datasize elements esize m minimum n pair)

def decode_fminnmp_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp_2008 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let pair : Bool := (U == 1#1)
  let minimum : Bool := (o1 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_max_min_fp16_2008 d datasize elements esize m minimum n pair)

def decode_fmaxnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_maxnm_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  if ((sz == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize := (esize *i 2)
  let elements := 2
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMINNUM
    else ReduceOp_FMAXNUM
  (execute_aarch64_instrs_vector_reduce_fp16_maxnm_sisd d datasize esize n op)

def decode_fmaxnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp_maxnm_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := (esize *i 2)
  let elements := 2
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMINNUM
    else ReduceOp_FMAXNUM
  (execute_aarch64_instrs_vector_reduce_fp16_maxnm_sisd d datasize esize n op)

def decode_fminnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_maxnm_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  if ((sz == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize := (esize *i 2)
  let elements := 2
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMINNUM
    else ReduceOp_FMAXNUM
  (execute_aarch64_instrs_vector_reduce_fp16_maxnm_sisd d datasize esize n op)

def decode_fminnmp_advsimd_pair_aarch64_instrs_vector_reduce_fp_maxnm_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := (esize *i 2)
  let elements := 2
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMINNUM
    else ReduceOp_FMAXNUM
  (execute_aarch64_instrs_vector_reduce_fp16_maxnm_sisd d datasize esize n op)

def decode_fmaxnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMINNUM
    else ReduceOp_FMAXNUM
  (execute_aarch64_instrs_vector_reduce_fp16_maxnm_simd d datasize esize n op)

def decode_fmaxnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((sz +++ Q) != 0b01#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMINNUM
    else ReduceOp_FMAXNUM
  (execute_aarch64_instrs_vector_reduce_fp16_maxnm_simd d datasize esize n op)

def decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp16_maxnm_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMINNUM
    else ReduceOp_FMAXNUM
  (execute_aarch64_instrs_vector_reduce_fp16_maxnm_simd d datasize esize n op)

def decode_fminnmv_advsimd_aarch64_instrs_vector_reduce_fp_maxnm_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((sz +++ Q) != 0b01#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMINNUM
    else ReduceOp_FMAXNUM
  (execute_aarch64_instrs_vector_reduce_fp16_maxnm_simd d datasize esize n op)

def decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  if ((sz == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize := (esize *i 2)
  let elements := 2
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMIN
    else ReduceOp_FMAX
  (execute_aarch64_instrs_vector_reduce_fp16_max_sisd d datasize esize n op)

def decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := (esize *i 2)
  let elements := 2
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMIN
    else ReduceOp_FMAX
  (execute_aarch64_instrs_vector_reduce_fp16_max_sisd d datasize esize n op)

def decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  if ((sz == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let datasize := (esize *i 2)
  let elements := 2
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMIN
    else ReduceOp_FMAX
  (execute_aarch64_instrs_vector_reduce_fp16_max_sisd d datasize esize n op)

def decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := (esize *i 2)
  let elements := 2
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMIN
    else ReduceOp_FMAX
  (execute_aarch64_instrs_vector_reduce_fp16_max_sisd d datasize esize n op)

def decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMIN
    else ReduceOp_FMAX
  (execute_aarch64_instrs_vector_reduce_fp16_max_simd d datasize esize n op)

def decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((sz +++ Q) != 0b01#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMIN
    else ReduceOp_FMAX
  (execute_aarch64_instrs_vector_reduce_fp16_max_simd d datasize esize n op)

def decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMIN
    else ReduceOp_FMAX
  (execute_aarch64_instrs_vector_reduce_fp16_max_simd d datasize esize n op)

def decode_fminv_advsimd_aarch64_instrs_vector_reduce_fp_max_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  if (((sz +++ Q) != 0b01#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMIN
    else ReduceOp_FMAX
  (execute_aarch64_instrs_vector_reduce_fp16_max_simd d datasize esize n op)

def decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  let index := (BitVec.toNat ((H +++ L) +++ M))
  let esize := 16
  let datasize := esize
  let elements := 1
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd d datasize elements esize idxdsize index m n sub_op)

def decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 3) ) : SailM Nat )
  let Rmhi : (BitVec 1) := M
  let index ← (( do
    let b__0 := (sz +++ L)
    if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
    then (pure (BitVec.toNat (H +++ L)))
    else
      (do
        if ((b__0 == (0b10#2 : (BitVec 2))) : Bool)
        then (pure (BitVec.toNat H))
        else sailThrow ((Error_Undefined ()))) ) : SailM Nat )
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd d datasize elements esize idxdsize index m n sub_op)

def decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  let index := (BitVec.toNat ((H +++ L) +++ M))
  let esize := 16
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd d datasize elements esize idxdsize index m n sub_op)

def decode_fmla_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 3) ) : SailM Nat )
  let Rmhi : (BitVec 1) := M
  let index ← (( do
    let b__0 := (sz +++ L)
    if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
    then (pure (BitVec.toNat (H +++ L)))
    else
      (do
        if ((b__0 == (0b10#2 : (BitVec 2))) : Bool)
        then (pure (BitVec.toNat H))
        else sailThrow ((Error_Undefined ()))) ) : SailM Nat )
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  if (((sz +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd d datasize elements esize idxdsize index m n sub_op)

def decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  let index := (BitVec.toNat ((H +++ L) +++ M))
  let esize := 16
  let datasize := esize
  let elements := 1
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd d datasize elements esize idxdsize index m n sub_op)

def decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 3) ) : SailM Nat )
  let Rmhi : (BitVec 1) := M
  let index ← (( do
    let b__0 := (sz +++ L)
    if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
    then (pure (BitVec.toNat (H +++ L)))
    else
      (do
        if ((b__0 == (0b10#2 : (BitVec 2))) : Bool)
        then (pure (BitVec.toNat H))
        else sailThrow ((Error_Undefined ()))) ) : SailM Nat )
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd d datasize elements esize idxdsize index m n sub_op)

def decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  let index := (BitVec.toNat ((H +++ L) +++ M))
  let esize := 16
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd d datasize elements esize idxdsize index m n sub_op)

def decode_fmls_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (o2 : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 3) ) : SailM Nat )
  let Rmhi : (BitVec 1) := M
  let index ← (( do
    let b__0 := (sz +++ L)
    if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
    then (pure (BitVec.toNat (H +++ L)))
    else
      (do
        if ((b__0 == (0b10#2 : (BitVec 2))) : Bool)
        then (pure (BitVec.toNat H))
        else sailThrow ((Error_Undefined ()))) ) : SailM Nat )
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  if (((sz +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_fp16_sisd d datasize elements esize idxdsize index m n sub_op)

def decode_fmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (a : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let sub_op : Bool := (a == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused d datasize elements esize m n sub_op)

def decode_fmla_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let sub_op : Bool := (op == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused d datasize elements esize m n sub_op)

def decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (a : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let sub_op : Bool := (a == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused d datasize elements esize m n sub_op)

def decode_fmls_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_fused (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let sub_op : Bool := (op == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_fused d datasize elements esize m n sub_op)

def decode_fmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_lower (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveFP16MulNoRoundingToFP32Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (0#1 +++ Rm))
  if ((sz == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let index := (BitVec.toNat ((H +++ L) +++ M))
  let esize := 32
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (S == 1#1)
  let part := 0
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_lower d datasize elements esize index m n part sub_op)

def decode_fmlal_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_upper (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveFP16MulNoRoundingToFP32Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (0#1 +++ Rm))
  if ((sz == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let index := (BitVec.toNat ((H +++ L) +++ M))
  let esize := 32
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (S == 1#1)
  let part := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_lower d datasize elements esize index m n part sub_op)

def decode_fmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_lower (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveFP16MulNoRoundingToFP32Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (0#1 +++ Rm))
  if ((sz == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let index := (BitVec.toNat ((H +++ L) +++ M))
  let esize := 32
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (S == 1#1)
  let part := 0
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_lower d datasize elements esize index m n part sub_op)

def decode_fmlsl_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_upper (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (S : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveFP16MulNoRoundingToFP32Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (0#1 +++ Rm))
  if ((sz == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let index := (BitVec.toNat ((H +++ L) +++ M))
  let esize := 32
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (S == 1#1)
  let part := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_acc_mul_norounding_i_lower d datasize elements esize index m n part sub_op)

def decode_fmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (S : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveFP16MulNoRoundingToFP32Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((sz == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (S == 1#1)
  let part := 0
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower d datasize elements esize m n part sub_op)

def decode_fmlal_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_upper (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (S : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveFP16MulNoRoundingToFP32Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((sz == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (S == 1#1)
  let part := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower d datasize elements esize m n part sub_op)

def decode_fmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (S : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveFP16MulNoRoundingToFP32Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((sz == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (S == 1#1)
  let part := 0
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower d datasize elements esize m n part sub_op)

def decode_fmlsl_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_upper (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (S : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveFP16MulNoRoundingToFP32Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  if ((sz == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let sub_op : Bool := (S == 1#1)
  let part := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower d datasize elements esize m n part sub_op)

def decode_fmov_advsimd_aarch64_instrs_vector_fp16_movi (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let rd := (BitVec.toNat Rd)
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let imm8 : (BitVec 8) := (((((((a +++ b) +++ c) +++ d) +++ e) +++ f) +++ g) +++ h)
  let imm16 : (BitVec 16) := (((((BitVec.join1 [(BitVec.access imm8 7)]) +++ (Complement.complement (BitVec.join1 [(BitVec.access imm8 6)]))) +++ (BitVec.replicateBits (BitVec.join1 [(BitVec.access imm8 6)]) 2)) +++ (Sail.BitVec.extractLsb imm8 5 0)) +++ (Zeros (n := 6)))
  let imm : (BitVec datasize) := (BitVec.replicateBits imm16 (Int.ediv datasize 16))
  (execute_aarch64_instrs_vector_fp16_movi datasize imm rd)

def decode_fmov_advsimd_aarch64_instrs_vector_logical (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let rd := (BitVec.toNat Rd)
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let operation ← (( do (undefined_ImmediateOp ()) ) : SailM ImmediateOp )
  let operation ← (( do
    let b__0 := (cmode +++ op)
    if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
    then (pure ImmediateOp_MOVI)
    else
      (do
        if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b01#2 : (BitVec 2)))) : Bool)
        then (pure ImmediateOp_MVNI)
        else
          (do
            if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b10#2 : (BitVec 2)))) : Bool)
            then (pure ImmediateOp_ORR)
            else
              (do
                if ((((Sail.BitVec.extractLsb b__0 4 4) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
                then (pure ImmediateOp_BIC)
                else
                  (do
                    if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
                    then (pure ImmediateOp_MOVI)
                    else
                      (do
                        if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b01#2 : (BitVec 2)))) : Bool)
                        then (pure ImmediateOp_MVNI)
                        else
                          (do
                            if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b10#2 : (BitVec 2)))) : Bool)
                            then (pure ImmediateOp_ORR)
                            else
                              (do
                                if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b11#2 : (BitVec 2)))) : Bool)
                                then (pure ImmediateOp_BIC)
                                else
                                  (do
                                    if ((((Sail.BitVec.extractLsb b__0 4 2) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
                                    then (pure ImmediateOp_MOVI)
                                    else
                                      (do
                                        if ((((Sail.BitVec.extractLsb b__0 4 2) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb b__0 0 0) == (1#1 : (BitVec 1)))) : Bool)
                                        then (pure ImmediateOp_MVNI)
                                        else
                                          (do
                                            if (((Sail.BitVec.extractLsb b__0 4 1) == (0xE#4 : (BitVec 4))) : Bool)
                                            then (pure ImmediateOp_MOVI)
                                            else
                                              (do
                                                if ((b__0 == (0b11110#5 : (BitVec 5))) : Bool)
                                                then (pure ImmediateOp_MOVI)
                                                else
                                                  (do
                                                    if ((Q == 0#1) : Bool)
                                                    then (sailThrow ((Error_Undefined ())) : SailM Unit)
                                                    else (pure ())
                                                    (pure ImmediateOp_MOVI))))))))))))) ) : SailM ImmediateOp )
  let operation := operation
  let imm64 ← (( do (AdvSIMDExpandImm op cmode (((((((a +++ b) +++ c) +++ d) +++ e) +++ f) +++ g) +++ h)) ) : SailM (BitVec 64) )
  let imm : (BitVec datasize) := (BitVec.replicateBits imm64 (Int.ediv datasize 64))
  (execute_aarch64_instrs_vector_fp16_movi datasize imm rd)

def decode_fmov_float_imm_aarch64_instrs_float_move_fp_imm (Rd : (BitVec 5)) (imm8 : (BitVec 8)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let datasize : Nat := 16
  let datasize ← (( do
    match (ftype : BitVec 2) with
    | 0b00 => (pure 32)
    | 0b01 => (pure 64)
    | 0b10 => sailThrow ((Error_Undefined ()))
    | _ =>
      (do
        if ((HaveFP16Ext ()) : Bool)
        then (pure 16)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let datasize := datasize
  let imm ← (( do (VFPExpandImm imm8 datasize) ) : SailM (BitVec datasize) )
  (execute_aarch64_instrs_float_move_fp_imm d datasize imm)

def decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product d datasize elements esize m n)

def decode_fmul_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_product d datasize elements esize m n)

def decode_fmul_float_aarch64_instrs_float_arithmetic_mul_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
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
  let negated : Bool := (op == 1#1)
  (execute_aarch64_instrs_float_arithmetic_mul_product d esize m n negated)

def decode_fnmul_float_aarch64_instrs_float_arithmetic_mul_product (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (Rm : (BitVec 5)) (ftype : (BitVec 2)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
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
  let negated : Bool := (op == 1#1)
  (execute_aarch64_instrs_float_arithmetic_mul_product d esize m n negated)

def decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  let index := (BitVec.toNat ((H +++ L) +++ M))
  let esize := 16
  let datasize := esize
  let elements := 1
  let mulx_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd d datasize elements esize idxdsize index m mulx_op n)

def decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 3) ) : SailM Nat )
  let Rmhi : (BitVec 1) := M
  let index ← (( do
    let b__0 := (sz +++ L)
    if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
    then (pure (BitVec.toNat (H +++ L)))
    else
      (do
        if ((b__0 == (0b10#2 : (BitVec 2))) : Bool)
        then (pure (BitVec.toNat H))
        else sailThrow ((Error_Undefined ()))) ) : SailM Nat )
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let mulx_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd d datasize elements esize idxdsize index m mulx_op n)

def decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  let index := (BitVec.toNat ((H +++ L) +++ M))
  let esize := 16
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let mulx_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd d datasize elements esize idxdsize index m mulx_op n)

def decode_fmul_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 3) ) : SailM Nat )
  let Rmhi : (BitVec 1) := M
  let index ← (( do
    let b__0 := (sz +++ L)
    if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
    then (pure (BitVec.toNat (H +++ L)))
    else
      (do
        if ((b__0 == (0b10#2 : (BitVec 2))) : Bool)
        then (pure (BitVec.toNat H))
        else sailThrow ((Error_Undefined ()))) ) : SailM Nat )
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  if (((sz +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let mulx_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd d datasize elements esize idxdsize index m mulx_op n)

def decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  let index := (BitVec.toNat ((H +++ L) +++ M))
  let esize := 16
  let datasize := esize
  let elements := 1
  let mulx_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd d datasize elements esize idxdsize index m mulx_op n)

def decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 3) ) : SailM Nat )
  let Rmhi : (BitVec 1) := M
  let index ← (( do
    let b__0 := (sz +++ L)
    if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
    then (pure (BitVec.toNat (H +++ L)))
    else
      (do
        if ((b__0 == (0b10#2 : (BitVec 2))) : Bool)
        then (pure (BitVec.toNat H))
        else sailThrow ((Error_Undefined ()))) ) : SailM Nat )
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  let mulx_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd d datasize elements esize idxdsize index m mulx_op n)

def decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Rd)
  let index := (BitVec.toNat ((H +++ L) +++ M))
  let esize := 16
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let mulx_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd d datasize elements esize idxdsize index m mulx_op n)

def decode_fmulx_advsimd_elt_aarch64_instrs_vector_arithmetic_binary_element_mul_fp_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (H : (BitVec 1)) (Rm : (BitVec 4)) (M : (BitVec 1)) (L : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let idxdsize :=
    if ((H == 1#1) : Bool)
    then 128
    else 64
  let index ← (( do (undefined_range 0 3) ) : SailM Nat )
  let Rmhi : (BitVec 1) := M
  let index ← (( do
    let b__0 := (sz +++ L)
    if (((Sail.BitVec.extractLsb b__0 1 1) == (0#1 : (BitVec 1))) : Bool)
    then (pure (BitVec.toNat (H +++ L)))
    else
      (do
        if ((b__0 == (0b10#2 : (BitVec 2))) : Bool)
        then (pure (BitVec.toNat H))
        else sailThrow ((Error_Undefined ()))) ) : SailM Nat )
  let index := index
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat (Rmhi +++ Rm))
  if (((sz +++ Q) == 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements := (Int.ediv datasize esize)
  let mulx_op : Bool := (U == 1#1)
  (execute_aarch64_instrs_vector_arithmetic_binary_element_mul_fp16_sisd d datasize elements esize idxdsize index m mulx_op n)

def decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 16
  let datasize := esize
  let elements := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd d datasize elements esize m n)

def decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd d datasize elements esize m n)

def decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd d datasize elements esize m n)

def decode_fmulx_advsimd_vec_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp_extended_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_mul_fp16_extended_sisd d datasize elements esize m n)

def decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  let datasize := esize
  let elements := 1
  (execute_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd d datasize elements esize n)

def decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  (execute_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd d datasize elements esize n)

def decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd d datasize elements esize n)

def decode_frecpe_advsimd_aarch64_instrs_vector_arithmetic_unary_special_recip_float_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd d datasize elements esize n)

def decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := 16
  let datasize := esize
  let elements := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd d datasize elements esize m n)

def decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize := esize
  let elements := 1
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd d datasize elements esize m n)

def decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd d datasize elements esize m n)

def decode_frecps_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_recps_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sz : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_recps_fp16_sisd d datasize elements esize m n)

def decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16 (Rd : (BitVec 5)) (Rn : (BitVec 5)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := 16
  (execute_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16 d esize n)

def decode_frecpx_advsimd_aarch64_instrs_vector_arithmetic_unary_special_frecpx (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  (execute_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16 d esize n)

def decode_frint32x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveFrintExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
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
  let intsize :=
    if ((op == 0#1) : Bool)
    then 32
    else 64
  let rounding ← (( do
    if ((U == 0#1) : Bool)
    then (pure FPRounding_ZERO)
    else (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  (execute_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 d datasize elements esize intsize n rounding)

def decode_frint32z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveFrintExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
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
  let intsize :=
    if ((op == 0#1) : Bool)
    then 32
    else 64
  let rounding ← (( do
    if ((U == 0#1) : Bool)
    then (pure FPRounding_ZERO)
    else (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  (execute_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 d datasize elements esize intsize n rounding)

def decode_frint64x_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveFrintExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
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
  let intsize :=
    if ((op == 0#1) : Bool)
    then 32
    else 64
  let rounding ← (( do
    if ((U == 0#1) : Bool)
    then (pure FPRounding_ZERO)
    else (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  (execute_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 d datasize elements esize intsize n rounding)

def decode_frint64z_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sz : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (← (HaveFrintExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
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
  let intsize :=
    if ((op == 0#1) : Bool)
    then 32
    else 64
  let rounding ← (( do
    if ((U == 0#1) : Bool)
    then (pure FPRounding_ZERO)
    else (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  (execute_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 d datasize elements esize intsize n rounding)

def decode_frint32x_float_aarch64_instrs_float_arithmetic_round_frint_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFrintExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize : Nat := 32
  let esize ← (( do
    let b__0 := ftype
    if ((b__0 == (0b00#2 : (BitVec 2))) : Bool)
    then (pure 32)
    else
      (do
        if ((b__0 == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 64)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let esize := esize
  let intsize :=
    if (((BitVec.join1 [(BitVec.access op 1)]) == 0#1) : Bool)
    then 32
    else 64
  let rounding ← (( do
    if (((BitVec.join1 [(BitVec.access op 0)]) == 0#1) : Bool)
    then (pure FPRounding_ZERO)
    else (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  (execute_aarch64_instrs_float_arithmetic_round_frint_32_64 d esize intsize n rounding)

def decode_frint32z_float_aarch64_instrs_float_arithmetic_round_frint_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFrintExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize : Nat := 32
  let esize ← (( do
    let b__0 := ftype
    if ((b__0 == (0b00#2 : (BitVec 2))) : Bool)
    then (pure 32)
    else
      (do
        if ((b__0 == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 64)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let esize := esize
  let intsize :=
    if (((BitVec.join1 [(BitVec.access op 1)]) == 0#1) : Bool)
    then 32
    else 64
  let rounding ← (( do
    if (((BitVec.join1 [(BitVec.access op 0)]) == 0#1) : Bool)
    then (pure FPRounding_ZERO)
    else (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  (execute_aarch64_instrs_float_arithmetic_round_frint_32_64 d esize intsize n rounding)

def decode_frint64x_float_aarch64_instrs_float_arithmetic_round_frint_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFrintExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize : Nat := 32
  let esize ← (( do
    let b__0 := ftype
    if ((b__0 == (0b00#2 : (BitVec 2))) : Bool)
    then (pure 32)
    else
      (do
        if ((b__0 == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 64)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let esize := esize
  let intsize :=
    if (((BitVec.join1 [(BitVec.access op 1)]) == 0#1) : Bool)
    then 32
    else 64
  let rounding ← (( do
    if (((BitVec.join1 [(BitVec.access op 0)]) == 0#1) : Bool)
    then (pure FPRounding_ZERO)
    else (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  (execute_aarch64_instrs_float_arithmetic_round_frint_32_64 d esize intsize n rounding)

def decode_frint64z_float_aarch64_instrs_float_arithmetic_round_frint_32_64 (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 2)) (ftype : (BitVec 2)) : SailM Unit := do
  if ((! (← (HaveFrintExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat Rd)
  let n := (BitVec.toNat Rn)
  let esize : Nat := 32
  let esize ← (( do
    let b__0 := ftype
    if ((b__0 == (0b00#2 : (BitVec 2))) : Bool)
    then (pure 32)
    else
      (do
        if ((b__0 == (0b01#2 : (BitVec 2))) : Bool)
        then (pure 64)
        else sailThrow ((Error_Undefined ()))) ) : SailM Int )
  let esize := esize
  let intsize :=
    if (((BitVec.join1 [(BitVec.access op 1)]) == 0#1) : Bool)
    then 32
    else 64
  let rounding ← (( do
    if (((BitVec.join1 [(BitVec.access op 0)]) == 0#1) : Bool)
    then (pure FPRounding_ZERO)
    else (FPRoundingMode (← (FPCR_read ()))) ) : SailM FPRounding )
  (execute_aarch64_instrs_float_arithmetic_round_frint_32_64 d esize intsize n rounding)

def decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let (exact, rounding) ← (( do
    let b__0 := ((U +++ o1) +++ o2)
    let (exact, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding (o1 +++ o2))
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
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round d datasize elements esize exact n rounding)

def decode_frinta_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let (exact, rounding) ← (( do
    let b__0 := ((U +++ o1) +++ o2)
    let (exact, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding (o1 +++ o2))
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
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round d datasize elements esize exact n rounding)

def decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let (exact, rounding) ← (( do
    let b__0 := ((U +++ o1) +++ o2)
    let (exact, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding (o1 +++ o2))
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
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round d datasize elements esize exact n rounding)

def decode_frinti_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let (exact, rounding) ← (( do
    let b__0 := ((U +++ o1) +++ o2)
    let (exact, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding (o1 +++ o2))
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
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round d datasize elements esize exact n rounding)

def decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let (exact, rounding) ← (( do
    let b__0 := ((U +++ o1) +++ o2)
    let (exact, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding (o1 +++ o2))
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
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round d datasize elements esize exact n rounding)

def decode_frintm_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let (exact, rounding) ← (( do
    let b__0 := ((U +++ o1) +++ o2)
    let (exact, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding (o1 +++ o2))
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
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round d datasize elements esize exact n rounding)

def decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let (exact, rounding) ← (( do
    let b__0 := ((U +++ o1) +++ o2)
    let (exact, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding (o1 +++ o2))
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
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round d datasize elements esize exact n rounding)

def decode_frintn_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let (exact, rounding) ← (( do
    let b__0 := ((U +++ o1) +++ o2)
    let (exact, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding (o1 +++ o2))
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
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round d datasize elements esize exact n rounding)

def decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let (exact, rounding) ← (( do
    let b__0 := ((U +++ o1) +++ o2)
    let (exact, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding (o1 +++ o2))
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
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round d datasize elements esize exact n rounding)

def decode_frintp_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let (exact, rounding) ← (( do
    let b__0 := ((U +++ o1) +++ o2)
    let (exact, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding (o1 +++ o2))
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
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round d datasize elements esize exact n rounding)

def decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let (exact, rounding) ← (( do
    let b__0 := ((U +++ o1) +++ o2)
    let (exact, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding (o1 +++ o2))
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
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round d datasize elements esize exact n rounding)

def decode_frintx_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let (exact, rounding) ← (( do
    let b__0 := ((U +++ o1) +++ o2)
    let (exact, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding (o1 +++ o2))
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
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round d datasize elements esize exact n rounding)

def decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_fp16_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let (exact, rounding) ← (( do
    let b__0 := ((U +++ o1) +++ o2)
    let (exact, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding (o1 +++ o2))
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
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round d datasize elements esize exact n rounding)

def decode_frintz_advsimd_aarch64_instrs_vector_arithmetic_unary_float_round (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (sz : (BitVec 1)) (o2 : (BitVec 1)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
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
  let exact : Bool := false
  let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
  let (exact, rounding) ← (( do
    let b__0 := ((U +++ o1) +++ o2)
    let (exact, rounding) ← (( do
      if (((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) : Bool)
      then
        (do
          let rounding ← (FPDecodeRounding (o1 +++ o2))
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
  (execute_aarch64_instrs_vector_arithmetic_unary_fp16_round d datasize elements esize exact n rounding)

def decode_frinta_float_aarch64_instrs_float_arithmetic_round_frint (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) : SailM Unit := do
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

def decode_frinti_float_aarch64_instrs_float_arithmetic_round_frint (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) : SailM Unit := do
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

def decode_frintm_float_aarch64_instrs_float_arithmetic_round_frint (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) : SailM Unit := do
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

def decode_frintn_float_aarch64_instrs_float_arithmetic_round_frint (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) : SailM Unit := do
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

def decode_frintp_float_aarch64_instrs_float_arithmetic_round_frint (Rd : (BitVec 5)) (Rn : (BitVec 5)) (rmode : (BitVec 3)) (ftype : (BitVec 2)) : SailM Unit := do
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


