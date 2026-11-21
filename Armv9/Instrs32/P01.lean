import Armv9.Armv9
import Armv9.Flow
import Armv9.Arith
import Armv9.Vector
import Armv9.Prelude
import Armv9.Builtins
import Armv9.V8Base
import Armv9.Stubs
import Armv9.Interrupts
import Armv9.Impdefs
import Armv9.Sysregs
import Armv9.Instrs32.P00

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

def decode_aarch32_instrs_LDRB_r_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rt == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "PLD")) : SailM Unit)
      else (pure ())
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRB (literal)")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if ((m == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRB_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_LDRBT_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:4246.29-4246.30"
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      if ((((t == 15) || (n == 15)) || (n == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      let m := m
      (execute_aarch32_instrs_LDRBT_Op_A_txt add imm32 m n postindex register_form shift_n shift_t t))
  else (pure ())

def decode_aarch32_instrs_LDRBT_A2enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:4281.29-4281.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := true
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((((t == 15) || (n == 15)) || (n == t)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_LDRBT_Op_A_txt add imm32 m n postindex register_form shift_n shift_t t))
  else (pure ())

def decode_aarch32_instrs_LDRBT_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRB (literal)")) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      let m := m
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let postindex : Bool := false
      let add : Bool := true
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRBT_Op_A_txt add imm32 m n postindex register_form shift_n shift_t t))
  else (pure ())

def decode_aarch32_instrs_LDRD_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:4383.29-4383.30"
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRD (literal)")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let t2 := (t +i 1)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((n == t) || (n == t2))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((t2 == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRD_i_Op_A_txt add imm32 index n t t2 wback))
  else (pure ())

def decode_aarch32_instrs_LDRD_i_T1enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rt2 : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((P == 0#1) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRD (literal)")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let t2 := (BitVec.toNat Rt2)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if ((wback && ((n == t) || (n == t2))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((((t == 15) || (t2 == 15)) || (t == t2)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRD_i_Op_A_txt add imm32 index n t t2 wback))
  else (pure ())

def decode_aarch32_instrs_LDRD_l_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:4491.29-4491.30"
      if (((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let t2 := (t +i 1)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let add : Bool := (U == 1#1)
      if ((t2 == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRD_l_Op_A_txt add imm32 t t2))
  else (pure ())

def decode_aarch32_instrs_LDRD_l_T1enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rt : (BitVec 4)) (Rt2 : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((P == 0#1) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let t2 := (BitVec.toNat Rt2)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let add : Bool := (U == 1#1)
      if ((((t == 15) || (t2 == 15)) || (t == t2)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((W == 1#1) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRD_l_Op_A_txt add imm32 t t2))
  else (pure ())

def decode_aarch32_instrs_LDRD_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:4586.29-4586.30"
      if (((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let t2 := (t +i 1)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((((t2 == 15) || (m == 15)) || (m == t)) || (m == t2)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && (((n == 15) || (n == t)) || (n == t2))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRD_r_Op_A_txt add index m n t t2 wback))
  else (pure ())

def decode_aarch32_instrs_LDREX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:4641.29-4641.30"
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Zeros (n := 32))
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDREX_Op_A_txt imm32 n t))
  else (pure ())

def decode_aarch32_instrs_LDREX_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDREX_Op_A_txt imm32 n t))
  else (pure ())

def decode_aarch32_instrs_LDREXB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:4706.29-4706.30"
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDREXB_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_LDREXB_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDREXB_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_LDREXD_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:4772.29-4772.30"
      let t := (BitVec.toNat Rt)
      let t2 := (t +i 1)
      let n := (BitVec.toNat Rn)
      if (((((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1) || (t2 == 15)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDREXD_Op_A_txt n t t2))
  else (pure ())

def decode_aarch32_instrs_LDREXD_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rt2 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let t2 := (BitVec.toNat Rt2)
      let n := (BitVec.toNat Rn)
      if (((((t == 15) || (t2 == 15)) || (t == t2)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDREXD_Op_A_txt n t t2))
  else (pure ())

def decode_aarch32_instrs_LDREXH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:4837.29-4837.30"
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDREXH_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_LDREXH_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDREXH_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_LDRH_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:4907.29-4907.30"
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRH (literal)")) : SailM Unit)
      else (pure ())
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "LDRHT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((t == 15) || (wback && (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRH_i_OpA_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDRH_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm5 +++ 0#1) 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDRH_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDRH_i_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rt == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "PLD (immediate)")) : SailM Unit)
      else (pure ())
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRH (literal)")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDRH_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDRH_i_T3enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRH (literal)")) : SailM Unit)
      else (pure ())
      if (((((Rt == 0b1111#4) && (P == 1#1)) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "PLDW (immediate)")) : SailM Unit)
      else (pure ())
      if ((((P == 1#1) && (U == 1#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "LDRHT")) : SailM Unit)
      else (pure ())
      if (((P == 0#1) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if ((((t == 15) && (W == 1#1)) || (wback && (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRH_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDRH_l_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:5069.29-5069.30"
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "LDRHT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((t == 15) || wback) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRH_l_Op_A_txt add imm32 t))
  else (pure ())

def decode_aarch32_instrs_LDRH_l_T1enc_A_txt (U : (BitVec 1)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rt == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "PLD (literal)")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      (execute_aarch32_instrs_LDRH_l_Op_A_txt add imm32 t))
  else (pure ())

def decode_aarch32_instrs_LDRH_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:5143.29-5143.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "LDRHT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if (((t == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRH_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_LDRH_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_LDRH_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_LDRH_r_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRH (literal)")) : SailM Unit)
      else (pure ())
      if ((Rt == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "PLDW (register)")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if ((m == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRH_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_LDRHT_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:5274.29-5274.30"
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      if ((((t == 15) || (n == 15)) || (n == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      let m := m
      (execute_aarch32_instrs_LDRHT_Op_A_txt add imm32 m n postindex register_form t))
  else (pure ())

def decode_aarch32_instrs_LDRHT_A2enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:5310.29-5310.30"
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := true
      if (((((t == 15) || (n == 15)) || (n == t)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      (execute_aarch32_instrs_LDRHT_Op_A_txt add imm32 m n postindex register_form t))
  else (pure ())

def decode_aarch32_instrs_LDRHT_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRH (literal)")) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      let m := m
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let postindex : Bool := false
      let add : Bool := true
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRHT_Op_A_txt add imm32 m n postindex register_form t))
  else (pure ())

def decode_aarch32_instrs_LDR_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:5406.29-5406.30"
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDR (literal)")) : SailM Unit)
      else (pure ())
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "LDRT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if ((wback && (n == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDR_i_OpA_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDR_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm5 +++ 0b00#2) 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDR_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDR_i_T2enc_A_txt (Rt : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := 13
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDR_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDR_i_T3enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDR (literal)")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      if ((←((pure (t == 15)) <&&> (do
           (InITBlock ())) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDR_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDR_i_T4enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDR (literal)")) : SailM Unit)
      else (pure ())
      if ((((P == 1#1) && (U == 1#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "LDRT")) : SailM Unit)
      else (pure ())
      if (((P == 0#1) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if ((←((pure (wback && (n == t))) <||> (do
           (pure (t == 15)) <&&> (do
             (InITBlock ())) <&&> (do
             (pure (! (← (LastInITBlock ())))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDR_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDR_l_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:5602.29-5602.30"
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "LDRT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (wback : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDR_l_Op_A_txt add imm32 t))
  else (pure ())

def decode_aarch32_instrs_LDR_l_T1enc_A_txt (Rt : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let add : Bool := true
      (execute_aarch32_instrs_LDR_l_Op_A_txt add imm32 t))
  else (pure ())

def decode_aarch32_instrs_LDR_l_T2enc_A_txt (U : (BitVec 1)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      if ((←((pure (t == 15)) <&&> (do
           (InITBlock ())) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDR_l_Op_A_txt add imm32 t))
  else (pure ())

def decode_aarch32_instrs_LDR_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:5702.29-5702.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "LDRT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if ((m == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDR_r_OpA_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_LDR_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_LDR_r_OpT_A_txt m n shift_n shift_t t))
  else (pure ())

def decode_aarch32_instrs_LDR_r_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDR (literal)")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if ((m == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((pure (t == 15)) <&&> (do
           (InITBlock ())) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDR_r_OpT_A_txt m n shift_n shift_t t))
  else (pure ())

def decode_aarch32_instrs_LDRSB_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:5844.29-5844.30"
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRSB (literal)")) : SailM Unit)
      else (pure ())
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "LDRSBT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((t == 15) || (wback && (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRSB_i_Op_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDRSB_i_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rt == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "PLI")) : SailM Unit)
      else (pure ())
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRSB (literal)")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDRSB_i_Op_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDRSB_i_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((((Rt == 0b1111#4) && (P == 1#1)) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "PLI")) : SailM Unit)
      else (pure ())
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRSB (literal)")) : SailM Unit)
      else (pure ())
      if ((((P == 1#1) && (U == 1#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "LDRSBT")) : SailM Unit)
      else (pure ())
      if (((P == 0#1) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if ((((t == 15) && (W == 1#1)) || (wback && (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRSB_i_Op_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDRSB_l_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:5964.29-5964.30"
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "LDRSBT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((t == 15) || wback) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRSB_l_Op_A_txt add imm32 t))
  else (pure ())

def decode_aarch32_instrs_LDRSB_l_T1enc_A_txt (U : (BitVec 1)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rt == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "PLI")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      (execute_aarch32_instrs_LDRSB_l_Op_A_txt add imm32 t))
  else (pure ())

def decode_aarch32_instrs_LDRSB_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:6038.29-6038.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "LDRSBT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if (((t == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRSB_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_LDRSB_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_LDRSB_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_LDRSB_r_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rt == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "PLI")) : SailM Unit)
      else (pure ())
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRSB (literal)")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if ((m == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRSB_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_LDRSBT_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:6169.29-6169.30"
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      if ((((t == 15) || (n == 15)) || (n == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      let m := m
      (execute_aarch32_instrs_LDRSBT_Op_A_txt add imm32 m n postindex register_form t))
  else (pure ())

def decode_aarch32_instrs_LDRSBT_A2enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:6205.29-6205.30"
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := true
      if (((((t == 15) || (n == 15)) || (n == t)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      (execute_aarch32_instrs_LDRSBT_Op_A_txt add imm32 m n postindex register_form t))
  else (pure ())

def decode_aarch32_instrs_LDRSBT_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRSB (literal)")) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      let m := m
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let postindex : Bool := false
      let add : Bool := true
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRSBT_Op_A_txt add imm32 m n postindex register_form t))
  else (pure ())

def decode_aarch32_instrs_LDRSH_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:6293.29-6293.30"
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRSH (literal)")) : SailM Unit)
      else (pure ())
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "LDRSHT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((t == 15) || (wback && (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRSH_i_Op_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDRSH_i_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRSH (literal)")) : SailM Unit)
      else (pure ())
      if ((Rt == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "Related instructions")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_LDRSH_i_Op_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDRSH_i_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRSH (literal)")) : SailM Unit)
      else (pure ())
      if (((((Rt == 0b1111#4) && (P == 1#1)) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "Related instructions")) : SailM Unit)
      else (pure ())
      if ((((P == 1#1) && (U == 1#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "LDRSHT")) : SailM Unit)
      else (pure ())
      if (((P == 0#1) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if ((((t == 15) && (W == 1#1)) || (wback && (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRSH_i_Op_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_LDRSH_l_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:6414.29-6414.30"
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "LDRSHT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((t == 15) || wback) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRSH_l_Op_A_txt add imm32 t))
  else (pure ())

def decode_aarch32_instrs_LDRSH_l_T1enc_A_txt (U : (BitVec 1)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rt == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "Related instructions")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      (execute_aarch32_instrs_LDRSH_l_Op_A_txt add imm32 t))
  else (pure ())

def decode_aarch32_instrs_LDRSH_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:6488.29-6488.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "LDRSHT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if (((t == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRSH_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_LDRSH_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_LDRSH_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_LDRSH_r_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRSH (literal)")) : SailM Unit)
      else (pure ())
      if ((Rt == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "Related instructions")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if ((m == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRSH_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_LDRSHT_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:6619.29-6619.30"
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      if ((((t == 15) || (n == 15)) || (n == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      let m := m
      (execute_aarch32_instrs_LDRSHT_Op_A_txt add imm32 m n postindex register_form t))
  else (pure ())

def decode_aarch32_instrs_LDRSHT_A2enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:6655.29-6655.30"
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := true
      if (((((t == 15) || (n == 15)) || (n == t)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      (execute_aarch32_instrs_LDRSHT_Op_A_txt add imm32 m n postindex register_form t))
  else (pure ())

def decode_aarch32_instrs_LDRSHT_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDRSH (literal)")) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      let m := m
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let postindex : Bool := false
      let add : Bool := true
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRSHT_Op_A_txt add imm32 m n postindex register_form t))
  else (pure ())

def decode_aarch32_instrs_LDRT_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:6750.29-6750.30"
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      if ((((t == 15) || (n == 15)) || (n == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      let m := m
      (execute_aarch32_instrs_LDRT_Op_A_txt add imm32 m n postindex register_form shift_n shift_t t))
  else (pure ())

def decode_aarch32_instrs_LDRT_A2enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:6785.29-6785.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := true
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((((t == 15) || (n == 15)) || (n == t)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_LDRT_Op_A_txt add imm32 m n postindex register_form shift_n shift_t t))
  else (pure ())

def decode_aarch32_instrs_LDRT_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "LDR (literal)")) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      let m := m
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let postindex : Bool := false
      let add : Bool := true
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDRT_Op_A_txt add imm32 m n postindex register_form shift_n shift_t t))
  else (pure ())

def decode_aarch32_instrs_LSL_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      if ((imm5 == 0b00000#5) : Bool)
      then (sailThrow ((Error_See "MOV (register)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let shift_n ← (( do
        let (_, __tup_1) ← do (DecodeImmShift 0b00#2 imm5)
        (pure __tup_1) ) : SailM Int )
      let shift_n := shift_n
      (execute_aarch32_instrs_LSL_i_Op_A_txt d m setflags shift_n))
  else (pure ())

def decode_aarch32_instrs_LSL_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rdn)
      let n := (BitVec.toNat Rdn)
      let m := (BitVec.toNat Rm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      (execute_aarch32_instrs_LSL_r_Op_A_txt d m n setflags))
  else (pure ())

def decode_aarch32_instrs_LSL_r_T2enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LSL_r_Op_A_txt d m n setflags))
  else (pure ())

def decode_aarch32_instrs_LSR_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let shift_n ← (( do
        let (_, __tup_1) ← do (DecodeImmShift 0b01#2 imm5)
        (pure __tup_1) ) : SailM Int )
      let shift_n := shift_n
      (execute_aarch32_instrs_LSR_i_Op_A_txt d m setflags shift_n))
  else (pure ())

def decode_aarch32_instrs_LSR_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rdn)
      let n := (BitVec.toNat Rdn)
      let m := (BitVec.toNat Rm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      (execute_aarch32_instrs_LSR_r_Op_A_txt d m n setflags))
  else (pure ())

def decode_aarch32_instrs_MCR_A1enc_A_txt (cond : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (Rt : (BitVec 4)) (coproc : (BitVec 1)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:7065.29-7065.30"
      let t := (BitVec.toNat Rt)
      let cp :=
        if (((BitVec.join1 [(BitVec.access coproc 0)]) == 0#1) : Bool)
        then 14
        else 15
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MCR_Op_A_txt cp t))
  else (pure ())

def decode_aarch32_instrs_MCR_T1enc_A_txt (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (Rt : (BitVec 4)) (coproc : (BitVec 1)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let cp :=
        if (((BitVec.join1 [(BitVec.access coproc 0)]) == 0#1) : Bool)
        then 14
        else 15
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MCR_Op_A_txt cp t))
  else (pure ())

def decode_aarch32_instrs_MCRR_A1enc_A_txt (cond : (BitVec 4)) (Rt2 : (BitVec 4)) (Rt : (BitVec 4)) (coproc : (BitVec 1)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:7125.29-7125.30"
      let t := (BitVec.toNat Rt)
      let t2 := (BitVec.toNat Rt2)
      let cp :=
        if (((BitVec.join1 [(BitVec.access coproc 0)]) == 0#1) : Bool)
        then 14
        else 15
      if (((t == 15) || (t2 == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MCRR_Op_A_txt cp t t2))
  else (pure ())

def decode_aarch32_instrs_MCRR_T1enc_A_txt (Rt2 : (BitVec 4)) (Rt : (BitVec 4)) (coproc : (BitVec 1)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let t2 := (BitVec.toNat Rt2)
      let cp :=
        if (((BitVec.join1 [(BitVec.access coproc 0)]) == 0#1) : Bool)
        then 14
        else 15
      if (((t == 15) || (t2 == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MCRR_Op_A_txt cp t t2))
  else (pure ())

def decode_aarch32_instrs_MLA_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:7194.29-7194.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      let setflags : Bool := (S == 1#1)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MLA_Op_A_txt a d m n setflags))
  else (pure ())

def decode_aarch32_instrs_MLA_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Ra == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "MUL")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      let setflags : Bool := false
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MLA_Op_A_txt a d m n setflags))
  else (pure ())

def decode_aarch32_instrs_MLS_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:7264.29-7264.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MLS_Op_A_txt a d m n))
  else (pure ())

def decode_aarch32_instrs_MLS_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MLS_Op_A_txt a d m n))
  else (pure ())

def decode_aarch32_instrs_MOV_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:7338.29-7338.30"
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let d := (BitVec.toNat Rd)
      let setflags : Bool := (S == 1#1)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (A32ExpandImm_C imm12 (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      (execute_aarch32_instrs_MOV_i_Op_A_txt carry d imm32 setflags))
  else (pure ())

def decode_aarch32_instrs_MOV_i_A2enc_A_txt (cond : (BitVec 4)) (imm4 : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:7366.29-7366.30"
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let d := (BitVec.toNat Rd)
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4 +++ imm12) 32)
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let carry := carry
      (execute_aarch32_instrs_MOV_i_Op_A_txt carry d imm32 setflags))
  else (pure ())

def decode_aarch32_instrs_MOV_i_T1enc_A_txt (Rd : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let carry ← (( do (pure (← readReg PSTATE).C) ) : SailM (BitVec 1) )
      (execute_aarch32_instrs_MOV_i_Op_A_txt carry d imm32 setflags))
  else (pure ())

def decode_aarch32_instrs_MOV_i_T2enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let d := (BitVec.toNat Rd)
      let setflags : Bool := (S == 1#1)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (T32ExpandImm_C ((i +++ imm3) +++ imm8) (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let carry := carry
      (execute_aarch32_instrs_MOV_i_Op_A_txt carry d imm32 setflags))
  else (pure ())

def decode_aarch32_instrs_MOV_i_T3enc_A_txt (i : (BitVec 1)) (imm4 : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let d := (BitVec.toNat Rd)
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (((imm4 +++ i) +++ imm3) +++ imm8) 32)
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let carry := carry
      (execute_aarch32_instrs_MOV_i_Op_A_txt carry d imm32 setflags))
  else (pure ())

def decode_aarch32_instrs_MOV_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:7495.29-7495.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_MOV_r_Op_A_txt d m setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_MOV_r_T1enc_A_txt (D : (BitVec 1)) (Rm : (BitVec 4)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat (D +++ Rd))
      let m := (BitVec.toNat Rm)
      let setflags : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if ((←((pure (d == 15)) <&&> (do
           (InITBlock ())) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_MOV_r_Op_A_txt d m setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_MOV_r_T2enc_A_txt (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := true
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_MOV_r_Op_A_txt d m setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_MOV_r_T3enc_A_txt (S : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_MOV_r_Op_A_txt d m setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_MOV_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:7638.29-7638.30"
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if ((((d == 15) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MOV_rr_Op_A_txt d m s setflags shift_t))
  else (pure ())

def decode_aarch32_instrs_MOV_rr_T1enc_A_txt (op : (BitVec 4)) (Rs : (BitVec 3)) (Rdm : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! ((op == 0b0010#4) || ((op == 0b0011#4) || ((op == 0b0100#4) || (op == 0b0111#4))))) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rdm)
      let m := (BitVec.toNat Rdm)
      let s := (BitVec.toNat Rs)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let shift_t ← (( do (DecodeRegShift ((BitVec.join1 [(BitVec.access op 2)]) +++ (BitVec.join1 [(BitVec.access op 0)]))) ) : SailM SRType )
      (execute_aarch32_instrs_MOV_rr_Op_A_txt d m s setflags shift_t))
  else (pure ())

def decode_aarch32_instrs_MOV_rr_T2enc_A_txt (stype : (BitVec 2)) (S : (BitVec 1)) (Rm : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if ((((d == 15) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MOV_rr_Op_A_txt d m s setflags shift_t))
  else (pure ())

def decode_aarch32_instrs_MOVT_A1enc_A_txt (cond : (BitVec 4)) (imm4 : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:7730.29-7730.30"
      let d := (BitVec.toNat Rd)
      let imm16 : (BitVec 16) := (imm4 +++ imm12)
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MOVT_Op_A_txt d imm16))
  else (pure ())

def decode_aarch32_instrs_MOVT_T1enc_A_txt (i : (BitVec 1)) (imm4 : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let imm16 : (BitVec 16) := (((imm4 +++ i) +++ imm3) +++ imm8)
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MOVT_Op_A_txt d imm16))
  else (pure ())

def decode_aarch32_instrs_MRC_A1enc_A_txt (cond : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (Rt : (BitVec 4)) (coproc : (BitVec 1)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:7790.29-7790.30"
      let t := (BitVec.toNat Rt)
      let cp :=
        if (((BitVec.join1 [(BitVec.access coproc 0)]) == 0#1) : Bool)
        then 14
        else 15
      (execute_aarch32_instrs_MRC_Op_A_txt cp t))
  else (pure ())

def decode_aarch32_instrs_MRC_T1enc_A_txt (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (Rt : (BitVec 4)) (coproc : (BitVec 1)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let cp :=
        if (((BitVec.join1 [(BitVec.access coproc 0)]) == 0#1) : Bool)
        then 14
        else 15
      (execute_aarch32_instrs_MRC_Op_A_txt cp t))
  else (pure ())

def decode_aarch32_instrs_MRRC_A1enc_A_txt (cond : (BitVec 4)) (Rt2 : (BitVec 4)) (Rt : (BitVec 4)) (coproc : (BitVec 1)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:7844.29-7844.30"
      let t := (BitVec.toNat Rt)
      let t2 := (BitVec.toNat Rt2)
      let cp :=
        if (((BitVec.join1 [(BitVec.access coproc 0)]) == 0#1) : Bool)
        then 14
        else 15
      if ((((t == 15) || (t2 == 15)) || (t == t2)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MRRC_Op_A_txt cp t t2))
  else (pure ())

def decode_aarch32_instrs_MRRC_T1enc_A_txt (Rt2 : (BitVec 4)) (Rt : (BitVec 4)) (coproc : (BitVec 1)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let t2 := (BitVec.toNat Rt2)
      let cp :=
        if (((BitVec.join1 [(BitVec.access coproc 0)]) == 0#1) : Bool)
        then 14
        else 15
      if ((((t == 15) || (t2 == 15)) || (t == t2)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MRRC_Op_A_txt cp t t2))
  else (pure ())

def decode_aarch32_instrs_MUL_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:7912.29-7912.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MUL_Op_A_txt d m n setflags))
  else (pure ())

def decode_aarch32_instrs_MUL_T1enc_A_txt (Rn : (BitVec 3)) (Rdm : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rdm)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rdm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      (execute_aarch32_instrs_MUL_Op_A_txt d m n setflags))
  else (pure ())

def decode_aarch32_instrs_MUL_T2enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := false
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MUL_Op_A_txt d m n setflags))
  else (pure ())

def decode_aarch32_instrs_MVN_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:8009.29-8009.30"
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let d := (BitVec.toNat Rd)
      let setflags : Bool := (S == 1#1)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (A32ExpandImm_C imm12 (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      (execute_aarch32_instrs_MVN_i_Op_A_txt carry d imm32 setflags))
  else (pure ())

def decode_aarch32_instrs_MVN_i_T1enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let d := (BitVec.toNat Rd)
      let setflags : Bool := (S == 1#1)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (T32ExpandImm_C ((i +++ imm3) +++ imm8) (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let carry := carry
      (execute_aarch32_instrs_MVN_i_Op_A_txt carry d imm32 setflags))
  else (pure ())

def decode_aarch32_instrs_MVN_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:8092.29-8092.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_MVN_r_Op_A_txt d m setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_MVN_r_T1enc_A_txt (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_MVN_r_Op_A_txt d m setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_MVN_r_T2enc_A_txt (S : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_MVN_r_Op_A_txt d m setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_MVN_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:8202.29-8202.30"
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if ((((d == 15) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MVN_rr_Op_A_txt d m s setflags shift_t))
  else (pure ())

def decode_aarch32_instrs_NOP_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:8241.29-8241.30"
      (pure (execute_aarch32_instrs_NOP_Op_A_txt ())))
  else (pure ())

def decode_aarch32_instrs_NOP_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (pure (execute_aarch32_instrs_NOP_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_NOP_T2enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (pure (execute_aarch32_instrs_NOP_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_ORN_i_T1enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "MVN (immediate)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (T32ExpandImm_C ((i +++ imm3) +++ imm8) (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ORN_i_Op_A_txt carry d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_ORN_r_T1enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "MVN (register)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ORN_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_ORR_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:8420.29-8420.30"
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (A32ExpandImm_C imm12 (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      (execute_aarch32_instrs_ORR_i_Op_A_txt carry d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_ORR_i_T1enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "MOV (immediate)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (T32ExpandImm_C ((i +++ imm3) +++ imm8) (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ORR_i_Op_A_txt carry d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_ORR_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:8504.29-8504.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_ORR_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_ORR_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rdn)
      let n := (BitVec.toNat Rdn)
      let m := (BitVec.toNat Rm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_ORR_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_ORR_r_T2enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ORR_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_ORR_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:8616.29-8616.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if (((((d == 15) || (n == 15)) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ORR_rr_Op_A_txt d m n s setflags shift_t))
  else (pure ())

def decode_aarch32_instrs_PKH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (tb : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:8660.29-8660.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let tbform : Bool := (tb == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift (tb +++ 0#1) imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_PKH_Op_A_txt d m n shift_n shift_t tbform))
  else (pure ())

def decode_aarch32_instrs_PKH_T1enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (tb : (BitVec 1)) (T : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((S == 1#1) || (T == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let tbform : Bool := (tb == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift (tb +++ 0#1) (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_PKH_Op_A_txt d m n shift_n shift_t tbform))
  else (pure ())

def decode_aarch32_instrs_PLD_i_A1enc_A_txt (U : (BitVec 1)) (R : (BitVec 1)) (Rn : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "PLD (literal)")) : SailM Unit)
      else (pure ())
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      let is_pldw : Bool := (R == 0#1)
      (execute_aarch32_instrs_PLD_i_Op_A_txt add imm32 is_pldw n))
  else (pure ())

def decode_aarch32_instrs_PLD_i_T1enc_A_txt (W : (BitVec 1)) (Rn : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "PLD (literal)")) : SailM Unit)
      else (pure ())
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := true
      let is_pldw : Bool := (W == 1#1)
      (execute_aarch32_instrs_PLD_i_Op_A_txt add imm32 is_pldw n))
  else (pure ())

def decode_aarch32_instrs_PLD_i_T2enc_A_txt (W : (BitVec 1)) (Rn : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "PLD (literal)")) : SailM Unit)
      else (pure ())
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let add : Bool := false
      let is_pldw : Bool := (W == 1#1)
      (execute_aarch32_instrs_PLD_i_Op_A_txt add imm32 is_pldw n))
  else (pure ())

def decode_aarch32_instrs_PLD_l_A1enc_A_txt (U : (BitVec 1)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      (execute_aarch32_instrs_PLD_l_Op_A_txt add imm32))
  else (pure ())

def decode_aarch32_instrs_PLD_l_T1enc_A_txt (U : (BitVec 1)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      (execute_aarch32_instrs_PLD_l_Op_A_txt add imm32))
  else (pure ())

def decode_aarch32_instrs_PLD_r_A1enc_A_txt (U : (BitVec 1)) (R : (BitVec 1)) (Rn : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let add : Bool := (U == 1#1)
      let is_pldw : Bool := (R == 0#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((m == 15) || ((n == 15) && is_pldw)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_PLD_r_Op_A_txt add is_pldw m n shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_PLD_r_T1enc_A_txt (W : (BitVec 1)) (Rn : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "PLD (literal)")) : SailM Unit)
      else (pure ())
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let add : Bool := true
      let is_pldw : Bool := (W == 1#1)
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if ((m == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_PLD_r_Op_A_txt add is_pldw m n shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_PLI_i_A1enc_A_txt (U : (BitVec 1)) (Rn : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      (execute_aarch32_instrs_PLI_i_Op_A_txt add imm32 n))
  else (pure ())

def decode_aarch32_instrs_PLI_i_T1enc_A_txt (Rn : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "encoding T3")) : SailM Unit)
      else (pure ())
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := true
      (execute_aarch32_instrs_PLI_i_Op_A_txt add imm32 n))
  else (pure ())

def decode_aarch32_instrs_PLI_i_T2enc_A_txt (Rn : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "encoding T3")) : SailM Unit)
      else (pure ())
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let add : Bool := false
      (execute_aarch32_instrs_PLI_i_Op_A_txt add imm32 n))
  else (pure ())

def decode_aarch32_instrs_PLI_i_T3enc_A_txt (U : (BitVec 1)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := 15
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let add : Bool := (U == 1#1)
      (execute_aarch32_instrs_PLI_i_Op_A_txt add imm32 n))
  else (pure ())

def decode_aarch32_instrs_PLI_r_A1enc_A_txt (U : (BitVec 1)) (Rn : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let add : Bool := (U == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if ((m == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_PLI_r_Op_A_txt add m n shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_PLI_r_T1enc_A_txt (Rn : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "PLI (immediate, literal)")) : SailM Unit)
      else (pure ())
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let add : Bool := true
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if ((m == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_PLI_r_Op_A_txt add m n shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_POP_T1enc_A_txt (P : (BitVec 1)) (register_list : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let registers : (BitVec 16) := ((P +++ 0b0000000#7) +++ register_list)
      let UnalignedAllowed : Bool := false
      if (((BitCount registers) <b 1) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((BitVec.join1 [(BitVec.access registers 15)]) == 1#1)) <&&> (do
           (InITBlock ())) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_POP_Op_A_txt UnalignedAllowed registers))
  else (pure ())

def decode_aarch32_instrs_PUSH_T1enc_A_txt (M : (BitVec 1)) (register_list : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let registers : (BitVec 16) := (((0#1 +++ M) +++ 0b000000#6) +++ register_list)
      let UnalignedAllowed : Bool := false
      if (((BitCount registers) <b 1) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_PUSH_Op_A_txt UnalignedAllowed registers))
  else (pure ())

def decode_aarch32_instrs_QADD16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:9237.29-9237.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QADD16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QADD16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QADD16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QADD8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:9304.29-9304.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QADD8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QADD8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QADD8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QADD_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:9375.29-9375.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QADD_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QADD_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QADD_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QASX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:9438.29-9438.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QASX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QASX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QASX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QDADD_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:9512.29-9512.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QDADD_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QDADD_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QDADD_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QDSUB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:9586.29-9586.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QDSUB_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QDSUB_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QDSUB_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QSAX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:9649.29-9649.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QSAX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QSAX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QSAX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QSUB16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:9712.29-9712.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QSUB16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QSUB16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QSUB16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QSUB8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:9779.29-9779.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QSUB8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QSUB8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QSUB8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QSUB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:9850.29-9850.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QSUB_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_QSUB_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_QSUB_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_RBIT_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:9914.29-9914.30"
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_RBIT_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_RBIT_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let n := (BitVec.toNat Rn)
      if ((((m != n) || (d == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_RBIT_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_REV16_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:9977.29-9977.30"
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_REV16_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_REV16_T1enc_A_txt (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      (execute_aarch32_instrs_REV16_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_REV16_T2enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let n := (BitVec.toNat Rn)
      if ((((m != n) || (d == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_REV16_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_REV_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:10058.29-10058.30"
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_REV_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_REV_T1enc_A_txt (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      (execute_aarch32_instrs_REV_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_REV_T2enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let n := (BitVec.toNat Rn)
      if ((((m != n) || (d == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_REV_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_REVSH_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:10137.29-10137.30"
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_REVSH_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_REVSH_T1enc_A_txt (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      (execute_aarch32_instrs_REVSH_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_REVSH_T2enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let n := (BitVec.toNat Rn)
      if ((((m != n) || (d == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_REVSH_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_ROR_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rdn)
      let n := (BitVec.toNat Rdn)
      let m := (BitVec.toNat Rm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      (execute_aarch32_instrs_ROR_r_Op_A_txt d m n setflags))
  else (pure ())

def decode_aarch32_instrs_RSB_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:10266.29-10266.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_RSB_i_Op_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_RSB_i_T1enc_A_txt (Rn : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let imm32 : (BitVec 32) := (Zeros (n := 32))
      (execute_aarch32_instrs_RSB_i_Op_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_RSB_i_T2enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (T32ExpandImm ((i +++ imm3) +++ imm8)) ) : SailM (BitVec 32) )
      if (((d == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_RSB_i_Op_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_RSB_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:10361.29-10361.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_RSB_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_RSB_r_T1enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_RSB_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_RSB_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:10446.29-10446.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if (((((d == 15) || (n == 15)) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_RSB_rr_Op_A_txt d m n s setflags shift_t))
  else (pure ())

def decode_aarch32_instrs_RSC_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:10500.29-10500.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_RSC_i_Op_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_RSC_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:10548.29-10548.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_RSC_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_RSC_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:10595.29-10595.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if (((((d == 15) || (n == 15)) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_RSC_rr_Op_A_txt d m n s setflags shift_t))
  else (pure ())

def decode_aarch32_instrs_SADD16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:10639.29-10639.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SADD16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SADD16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SADD16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SADD8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:10710.29-10710.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SADD8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SADD8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SADD8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SASX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:10775.29-10775.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SASX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SASX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SASX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SB_A1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (execute_aarch32_instrs_SB_Op_A_txt ())
  else (pure ())

def decode_aarch32_instrs_SB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SB_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_SBC_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:10895.29-10895.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_SBC_i_Op_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_SBC_i_T1enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (T32ExpandImm ((i +++ imm3) +++ imm8)) ) : SailM (BitVec 32) )
      if (((d == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SBC_i_Op_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_SBC_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:10970.29-10970.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_SBC_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_SBC_r_T1enc_A_txt (Rm : (BitVec 3)) (Rdn : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rdn)
      let n := (BitVec.toNat Rdn)
      let m := (BitVec.toNat Rm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_SBC_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_SBC_r_T2enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_SBC_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_SBC_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:11079.29-11079.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if (((((d == 15) || (n == 15)) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SBC_rr_Op_A_txt d m n s setflags shift_t))
  else (pure ())

def decode_aarch32_instrs_SBFX_A1enc_A_txt (cond : (BitVec 4)) (widthm1 : (BitVec 5)) (Rd : (BitVec 4)) (lsb : (BitVec 5)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:11119.29-11119.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let lsbit := (BitVec.toNat lsb)
      let widthminus1 := (BitVec.toNat widthm1)
      let msbit := (lsbit +i widthminus1)
      if (((d == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((msbit >b 31) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SBFX_Op_A_txt d lsbit msbit n))
  else (pure ())

def decode_aarch32_instrs_SBFX_T1enc_A_txt (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (widthm1 : (BitVec 5)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let lsbit := (BitVec.toNat (imm3 +++ imm2))
      let widthminus1 := (BitVec.toNat widthm1)
      let msbit := (lsbit +i widthminus1)
      if (((d == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((msbit >b 31) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SBFX_Op_A_txt d lsbit msbit n))
  else (pure ())

def decode_aarch32_instrs_SDIV_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:11199.29-11199.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a != 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SDIV_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SDIV_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a != 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SDIV_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SEL_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:11274.29-11274.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SEL_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SEL_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SEL_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SETEND_A1enc_A_txt (E : (BitVec 1)) : SailM Unit := do
  let set_bigend : Bool := (E == 1#1)
  (execute_aarch32_instrs_SETEND_Op_A_txt set_bigend)

def decode_aarch32_instrs_SETEND_T1enc_A_txt (E : (BitVec 1)) : SailM Unit := do
  let set_bigend : Bool := (E == 1#1)
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  (execute_aarch32_instrs_SETEND_Op_A_txt set_bigend)

def decode_aarch32_instrs_SEV_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:11377.29-11377.30"
      (pure (execute_aarch32_instrs_SEV_Op_A_txt ())))
  else (pure ())

def decode_aarch32_instrs_SEV_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (pure (execute_aarch32_instrs_SEV_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_SEV_T2enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (pure (execute_aarch32_instrs_SEV_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_SHADD16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:11440.29-11440.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SHADD16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHADD16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SHADD16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHADD8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:11507.29-11507.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SHADD8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHADD8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SHADD8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHASX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:11570.29-11570.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SHASX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHASX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SHASX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHSAX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:11633.29-11633.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SHSAX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHSAX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SHSAX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHSUB16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:11696.29-11696.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SHSUB16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHSUB16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SHSUB16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHSUB8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:11763.29-11763.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SHSUB8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHSUB8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SHSUB8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SMLABB_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (N : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:11832.29-11832.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      let n_high : Bool := (N == 1#1)
      let m_high : Bool := (M == 1#1)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMLABB_Op_A_txt a d m m_high n n_high))
  else (pure ())

def decode_aarch32_instrs_SMLABB_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Ra == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "SMULBB, SMULBT, SMULTB, SMULTT")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      let n_high : Bool := (N == 1#1)
      let m_high : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMLABB_Op_A_txt a d m m_high n n_high))
  else (pure ())

def decode_aarch32_instrs_SMLAD_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:11911.29-11911.30"
      if ((Ra == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "SMUAD")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      let m_swap : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMLAD_Op_A_txt a d m m_swap n))
  else (pure ())

def decode_aarch32_instrs_SMLAD_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Ra == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "SMUAD")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      let m_swap : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMLAD_Op_A_txt a d m m_swap n))
  else (pure ())

def decode_aarch32_instrs_SMLAL_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (RdHi : (BitVec 4)) (RdLo : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:11988.29-11988.30"
      let dLo := (BitVec.toNat RdLo)
      let dHi := (BitVec.toNat RdHi)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((dHi == dLo) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMLAL_Op_A_txt dHi dLo m n setflags))
  else (pure ())

def decode_aarch32_instrs_SMLAL_T1enc_A_txt (Rn : (BitVec 4)) (RdLo : (BitVec 4)) (RdHi : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let dLo := (BitVec.toNat RdLo)
      let dHi := (BitVec.toNat RdHi)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := false
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((dHi == dLo) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMLAL_Op_A_txt dHi dLo m n setflags))
  else (pure ())

def decode_aarch32_instrs_SMLALBB_A1enc_A_txt (cond : (BitVec 4)) (RdHi : (BitVec 4)) (RdLo : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (N : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:12063.29-12063.30"
      let dLo := (BitVec.toNat RdLo)
      let dHi := (BitVec.toNat RdHi)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let n_high : Bool := (N == 1#1)
      let m_high : Bool := (M == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((dHi == dLo) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMLALBB_Op_A_txt dHi dLo m m_high n n_high))
  else (pure ())

def decode_aarch32_instrs_SMLALBB_T1enc_A_txt (Rn : (BitVec 4)) (RdLo : (BitVec 4)) (RdHi : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let dLo := (BitVec.toNat RdLo)
      let dHi := (BitVec.toNat RdHi)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let n_high : Bool := (N == 1#1)
      let m_high : Bool := (M == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((dHi == dLo) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMLALBB_Op_A_txt dHi dLo m m_high n n_high))
  else (pure ())

def decode_aarch32_instrs_SMLALD_A1enc_A_txt (cond : (BitVec 4)) (RdHi : (BitVec 4)) (RdLo : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:12142.29-12142.30"
      let dLo := (BitVec.toNat RdLo)
      let dHi := (BitVec.toNat RdHi)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let m_swap : Bool := (M == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((dHi == dLo) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMLALD_Op_A_txt dHi dLo m m_swap n))
  else (pure ())

def decode_aarch32_instrs_SMLALD_T1enc_A_txt (Rn : (BitVec 4)) (RdLo : (BitVec 4)) (RdHi : (BitVec 4)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let dLo := (BitVec.toNat RdLo)
      let dHi := (BitVec.toNat RdHi)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let m_swap : Bool := (M == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((dHi == dLo) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMLALD_Op_A_txt dHi dLo m m_swap n))
  else (pure ())

def decode_aarch32_instrs_SMLAWB_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:12219.29-12219.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      let m_high : Bool := (M == 1#1)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMLAWB_Op_A_txt a d m m_high n))
  else (pure ())

def decode_aarch32_instrs_SMLAWB_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Ra == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "SMULWB, SMULWT")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      let m_high : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMLAWB_Op_A_txt a d m m_high n))
  else (pure ())

def decode_aarch32_instrs_SMLSD_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:12294.29-12294.30"
      if ((Ra == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "SMUSD")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      let m_swap : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMLSD_Op_A_txt a d m m_swap n))
  else (pure ())

def decode_aarch32_instrs_SMLSD_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Ra == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "SMUSD")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      let m_swap : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMLSD_Op_A_txt a d m m_swap n))
  else (pure ())

def decode_aarch32_instrs_SMLSLD_A1enc_A_txt (cond : (BitVec 4)) (RdHi : (BitVec 4)) (RdLo : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:12369.29-12369.30"
      let dLo := (BitVec.toNat RdLo)
      let dHi := (BitVec.toNat RdHi)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let m_swap : Bool := (M == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((dHi == dLo) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMLSLD_Op_A_txt dHi dLo m m_swap n))
  else (pure ())

def decode_aarch32_instrs_SMLSLD_T1enc_A_txt (Rn : (BitVec 4)) (RdLo : (BitVec 4)) (RdHi : (BitVec 4)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let dLo := (BitVec.toNat RdLo)
      let dHi := (BitVec.toNat RdHi)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let m_swap : Bool := (M == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((dHi == dLo) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMLSLD_Op_A_txt dHi dLo m m_swap n))
  else (pure ())

def decode_aarch32_instrs_SMMLA_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (R : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:12444.29-12444.30"
      if ((Ra == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "SMMUL")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      let round : Bool := (R == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMMLA_Op_A_txt a d m n round))
  else (pure ())

def decode_aarch32_instrs_SMMLA_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (R : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Ra == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "SMMUL")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      let round : Bool := (R == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMMLA_Op_A_txt a d m n round))
  else (pure ())

def decode_aarch32_instrs_SMMLS_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (R : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:12519.29-12519.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      let round : Bool := (R == 1#1)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMMLS_Op_A_txt a d m n round))
  else (pure ())

def decode_aarch32_instrs_SMMLS_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (R : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      let round : Bool := (R == 1#1)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMMLS_Op_A_txt a d m n round))
  else (pure ())

def decode_aarch32_instrs_SMMUL_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) (R : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:12588.29-12588.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let round : Bool := (R == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMMUL_Op_A_txt d m n round))
  else (pure ())

def decode_aarch32_instrs_SMMUL_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (R : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let round : Bool := (R == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMMUL_Op_A_txt d m n round))
  else (pure ())

def decode_aarch32_instrs_SMUAD_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:12656.29-12656.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let m_swap : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMUAD_Op_A_txt d m m_swap n))
  else (pure ())

def decode_aarch32_instrs_SMUAD_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let m_swap : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMUAD_Op_A_txt d m m_swap n))
  else (pure ())

def decode_aarch32_instrs_SMULBB_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (N : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:12721.29-12721.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let n_high : Bool := (N == 1#1)
      let m_high : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMULBB_Op_A_txt d m m_high n n_high))
  else (pure ())

def decode_aarch32_instrs_SMULBB_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let n_high : Bool := (N == 1#1)
      let m_high : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMULBB_Op_A_txt d m m_high n n_high))
  else (pure ())

def decode_aarch32_instrs_SMULL_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (RdHi : (BitVec 4)) (RdLo : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:12796.29-12796.30"
      let dLo := (BitVec.toNat RdLo)
      let dHi := (BitVec.toNat RdHi)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((dHi == dLo) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMULL_Op_A_txt dHi dLo m n setflags))
  else (pure ())

def decode_aarch32_instrs_SMULL_T1enc_A_txt (Rn : (BitVec 4)) (RdLo : (BitVec 4)) (RdHi : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let dLo := (BitVec.toNat RdLo)
      let dHi := (BitVec.toNat RdHi)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := false
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((dHi == dLo) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMULL_Op_A_txt dHi dLo m n setflags))
  else (pure ())

def decode_aarch32_instrs_SMULWB_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:12868.29-12868.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let m_high : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMULWB_Op_A_txt d m m_high n))
  else (pure ())

def decode_aarch32_instrs_SMULWB_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let m_high : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMULWB_Op_A_txt d m m_high n))
  else (pure ())

def decode_aarch32_instrs_SMUSD_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) (M : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:12936.29-12936.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let m_swap : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMUSD_Op_A_txt d m m_swap n))
  else (pure ())

def decode_aarch32_instrs_SMUSD_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (M : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let m_swap : Bool := (M == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMUSD_Op_A_txt d m m_swap n))
  else (pure ())

def decode_aarch32_instrs_SSAT16_A1enc_A_txt (cond : (BitVec 4)) (sat_imm : (BitVec 4)) (Rd : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:13007.29-13007.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let saturate_to := ((BitVec.toNat sat_imm) +i 1)
      if (((d == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SSAT16_Op_A_txt d n saturate_to))
  else (pure ())

def decode_aarch32_instrs_SSAT16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (sat_imm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let saturate_to := ((BitVec.toNat sat_imm) +i 1)
      if (((d == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SSAT16_Op_A_txt d n saturate_to))
  else (pure ())

def decode_aarch32_instrs_SSAT_A1enc_A_txt (cond : (BitVec 4)) (sat_imm : (BitVec 5)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (sh : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:13079.29-13079.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let saturate_to := ((BitVec.toNat sat_imm) +i 1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift (sh +++ 0#1) imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((d == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_SSAT_Op_A_txt d n saturate_to shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_SSAT_T1enc_A_txt (sh : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (sat_imm : (BitVec 5)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((sh == 1#1) && ((imm3 +++ imm2) == 0b00000#5)) : Bool)
      then (sailThrow ((Error_See "SSAT16")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let saturate_to := ((BitVec.toNat sat_imm) +i 1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift (sh +++ 0#1) (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((d == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SSAT_Op_A_txt d n saturate_to shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_SSAX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:13162.29-13162.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SSAX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SSAX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SSAX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SSUB16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:13227.29-13227.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SSUB16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SSUB16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SSUB16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SSUB8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:13298.29-13298.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SSUB8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SSUB8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SSUB8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_STC_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:13365.29-13365.30"
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let n := (BitVec.toNat Rn)
      let cp := 14
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if ((←((pure (n == 15)) <&&> (do
           (pure wback) <||> (do
             (pure (bne (← (CurrentInstrSet ())) InstrSet_A32)))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STC_Op_A_txt add cp imm32 index n wback))
  else (pure ())

def decode_aarch32_instrs_STC_T1enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let n := (BitVec.toNat Rn)
      let cp := 14
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if ((←((pure (n == 15)) <&&> (do
           (pure wback) <||> (do
             (pure (bne (← (CurrentInstrSet ())) InstrSet_A32)))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STC_Op_A_txt add cp imm32 index n wback))
  else (pure ())

def decode_aarch32_instrs_STM_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:13454.29-13454.30"
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STM_Op_A_txt n registers wback))
  else (pure ())

def decode_aarch32_instrs_STM_T1enc_A_txt (Rn : (BitVec 3)) (register_list : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 16) := (0b00000000#8 +++ register_list)
      let wback : Bool := true
      if (((BitCount registers) <b 1) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STM_Op_A_txt n registers wback))
  else (pure ())

def decode_aarch32_instrs_STM_T2enc_A_txt (W : (BitVec 1)) (Rn : (BitVec 4)) (P : (BitVec 1)) (M : (BitVec 1)) (register_list : (BitVec 14)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 16) := ((P +++ M) +++ register_list)
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 2)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access registers 13)]) == 1#1) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access registers 15)]) == 1#1) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STM_Op_A_txt n registers wback))
  else (pure ())

def decode_aarch32_instrs_STMDA_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:13560.29-13560.30"
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STMDA_Op_A_txt n registers wback))
  else (pure ())

def decode_aarch32_instrs_STMDB_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:13610.29-13610.30"
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STMDB_Op_A_txt n registers wback))
  else (pure ())

def decode_aarch32_instrs_STMDB_T1enc_A_txt (W : (BitVec 1)) (Rn : (BitVec 4)) (P : (BitVec 1)) (M : (BitVec 1)) (register_list : (BitVec 14)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 16) := ((P +++ M) +++ register_list)
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 2)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access registers 13)]) == 1#1) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access registers 15)]) == 1#1) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STMDB_Op_A_txt n registers wback))
  else (pure ())

def decode_aarch32_instrs_STMIB_A1enc_A_txt (cond : (BitVec 4)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:13694.29-13694.30"
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let wback : Bool := (W == 1#1)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STMIB_Op_A_txt n registers wback))
  else (pure ())

def decode_aarch32_instrs_STRB_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:13737.29-13737.30"
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "STRBT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STRB_i_OpA_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_STRB_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm5 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_STRB_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_STRB_i_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STRB_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_STRB_i_T3enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((P == 1#1) && (U == 1#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "STRBT")) : SailM Unit)
      else (pure ())
      if (((Rn == 0b1111#4) || ((P == 0#1) && (W == 0#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if (((t == 15) || (wback && (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STRB_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_STRB_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:13898.29-13898.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "STRBT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((t == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STRB_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_STRB_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_STRB_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_STRB_r_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if (((t == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STRB_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_STRBT_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:14027.29-14027.30"
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      if ((((t == 15) || (n == 15)) || (n == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      let m := m
      (execute_aarch32_instrs_STRBT_Op_A_txt add imm32 m n postindex register_form shift_n shift_t t))
  else (pure ())

def decode_aarch32_instrs_STRBT_A2enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:14062.29-14062.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := true
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((((t == 15) || (n == 15)) || (n == t)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_STRBT_Op_A_txt add imm32 m n postindex register_form shift_n shift_t t))
  else (pure ())

def decode_aarch32_instrs_STRBT_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      let m := m
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let postindex : Bool := false
      let add : Bool := true
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STRBT_Op_A_txt add imm32 m n postindex register_form shift_n shift_t t))
  else (pure ())

def decode_aarch32_instrs_STRD_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:14164.29-14164.30"
      if (((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let t2 := (t +i 1)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && (((n == 15) || (n == t)) || (n == t2))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((t2 == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STRD_i_Op_A_txt add imm32 index n t t2 wback))
  else (pure ())

def decode_aarch32_instrs_STRD_i_T1enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rt2 : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((P == 0#1) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let t2 := (BitVec.toNat Rt2)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if ((wback && ((n == t) || (n == t2))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((((n == 15) || (t == 15)) || (t2 == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STRD_i_Op_A_txt add imm32 index n t t2 wback))
  else (pure ())

def decode_aarch32_instrs_STRD_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:14271.29-14271.30"
      if (((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let t2 := (t +i 1)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((t2 == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && (((n == 15) || (n == t)) || (n == t2))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STRD_r_Op_A_txt add index m n t t2 wback))
  else (pure ())

def decode_aarch32_instrs_STREX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:14330.29-14330.30"
      let d := (BitVec.toNat Rd)
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Zeros (n := 32))
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((d == n) || (d == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STREX_Op_A_txt d imm32 n t))
  else (pure ())

def decode_aarch32_instrs_STREX_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((d == n) || (d == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STREX_Op_A_txt d imm32 n t))
  else (pure ())

def decode_aarch32_instrs_STREXB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:14405.29-14405.30"
      let d := (BitVec.toNat Rd)
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((d == n) || (d == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STREXB_Op_A_txt d n t))
  else (pure ())

def decode_aarch32_instrs_STREXB_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rd : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((d == n) || (d == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STREXB_Op_A_txt d n t))
  else (pure ())

def decode_aarch32_instrs_STREXD_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:14485.29-14485.30"
      let d := (BitVec.toNat Rd)
      let t := (BitVec.toNat Rt)
      let t2 := (t +i 1)
      let n := (BitVec.toNat Rn)
      if (((((d == 15) || ((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1)) || (t2 == 15)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((((d == n) || (d == t)) || (d == t2)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STREXD_Op_A_txt d n t t2))
  else (pure ())

def decode_aarch32_instrs_STREXD_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rt2 : (BitVec 4)) (Rd : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let t := (BitVec.toNat Rt)
      let t2 := (BitVec.toNat Rt2)
      let n := (BitVec.toNat Rn)
      if (((((d == 15) || (t == 15)) || (t2 == 15)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((((d == n) || (d == t)) || (d == t2)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STREXD_Op_A_txt d n t t2))
  else (pure ())

def decode_aarch32_instrs_STREXH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:14560.29-14560.30"
      let d := (BitVec.toNat Rd)
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((d == n) || (d == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STREXH_Op_A_txt d n t))
  else (pure ())

def decode_aarch32_instrs_STREXH_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rd : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((d == n) || (d == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STREXH_Op_A_txt d n t))
  else (pure ())

def decode_aarch32_instrs_STRH_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:14640.29-14640.30"
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "STRHT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STRH_i_OpA_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_STRH_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm5 +++ 0#1) 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_STRH_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_STRH_i_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STRH_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_STRH_i_T3enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((P == 1#1) && (U == 1#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "STRHT")) : SailM Unit)
      else (pure ())
      if (((Rn == 0b1111#4) || ((P == 0#1) && (W == 0#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if (((t == 15) || (wback && (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STRH_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_STRH_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:14802.29-14802.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "STRHT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if (((t == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STRH_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_STRH_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_STRH_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_STRH_r_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if (((t == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STRH_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_STRHT_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm4H : (BitVec 4)) (imm4L : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:14930.29-14930.30"
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4H +++ imm4L) 32)
      if ((((t == 15) || (n == 15)) || (n == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      let m := m
      (execute_aarch32_instrs_STRHT_Op_A_txt add imm32 m n postindex register_form t))
  else (pure ())

def decode_aarch32_instrs_STRHT_A2enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:14966.29-14966.30"
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := true
      if (((((t == 15) || (n == 15)) || (n == t)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      (execute_aarch32_instrs_STRHT_Op_A_txt add imm32 m n postindex register_form t))
  else (pure ())

def decode_aarch32_instrs_STRHT_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      let m := m
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let postindex : Bool := false
      let add : Bool := true
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STRHT_Op_A_txt add imm32 m n postindex register_form t))
  else (pure ())

def decode_aarch32_instrs_STR_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:15054.29-15054.30"
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "STRT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STR_i_OpA_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_STR_i_T1enc_A_txt (imm5 : (BitVec 5)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm5 +++ 0b00#2) 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_STR_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_STR_i_T2enc_A_txt (Rt : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := 13
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      (execute_aarch32_instrs_STR_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_STR_i_T3enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STR_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_STR_i_T4enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((P == 1#1) && (U == 1#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "STRT")) : SailM Unit)
      else (pure ())
      if (((Rn == 0b1111#4) || ((P == 0#1) && (W == 0#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      if (((t == 15) || (wback && (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STR_i_OpT_A_txt add imm32 index n t wback))
  else (pure ())

def decode_aarch32_instrs_STR_r_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:15240.29-15240.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((P == 0#1) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_See "STRT")) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := ((P == 0#1) || (W == 1#1))
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if ((m == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((n == 15) || (n == t))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STR_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_STR_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rt : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_STR_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_STR_r_T2enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm2 : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let index : Bool := true
      let add : Bool := true
      let wback : Bool := false
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, (BitVec.toNat imm2)) : (SRType × Int))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      if (((t == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STR_r_Op_A_txt add index m n shift_n shift_t t wback))
  else (pure ())

def decode_aarch32_instrs_STRT_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:15375.29-15375.30"
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm12 32)
      if (((n == 15) || (n == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      let m := m
      (execute_aarch32_instrs_STRT_Op_A_txt add imm32 m n postindex register_form shift_n shift_t t))
  else (pure ())

def decode_aarch32_instrs_STRT_A2enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:15410.29-15410.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let postindex : Bool := true
      let add : Bool := (U == 1#1)
      let register_form : Bool := true
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if ((((n == 15) || (n == t)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_STRT_Op_A_txt add imm32 m n postindex register_form shift_n shift_t t))
  else (pure ())

def decode_aarch32_instrs_STRT_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      let m := m
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      let postindex : Bool := false
      let add : Bool := true
      let register_form : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STRT_Op_A_txt add imm32 m n postindex register_form shift_n shift_t t))
  else (pure ())

def decode_aarch32_instrs_SUB_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:15507.29-15507.30"
      if (((Rn == 0b1111#4) && (S == 0#1)) : Bool)
      then (sailThrow ((Error_See "ADR")) : SailM Unit)
      else (pure ())
      if ((Rn == 0b1101#4) : Bool)
      then (sailThrow ((Error_See "SUB (SP minus immediate)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_SUB_i_Op_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_SUB_i_T1enc_A_txt (imm3 : (BitVec 3)) (Rn : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm3 32)
      (execute_aarch32_instrs_SUB_i_Op_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_SUB_i_T2enc_A_txt (Rdn : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rdn)
      let n := (BitVec.toNat Rdn)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      (execute_aarch32_instrs_SUB_i_Op_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_SUB_i_T3enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then (sailThrow ((Error_See "CMP (immediate)")) : SailM Unit)
      else (pure ())
      if ((Rn == 0b1101#4) : Bool)
      then (sailThrow ((Error_See "SUB (SP minus immediate)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (T32ExpandImm ((i +++ imm3) +++ imm8)) ) : SailM (BitVec 32) )
      if ((((d == 15) && (! setflags)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SUB_i_Op_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_SUB_i_T4enc_A_txt (i : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "ADR")) : SailM Unit)
      else (pure ())
      if ((Rn == 0b1101#4) : Bool)
      then (sailThrow ((Error_See "SUB (SP minus immediate)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend ((i +++ imm3) +++ imm8) 32)
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SUB_i_Op_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_SUB_i_T5enc_A_txt (Rn : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Rn == 0b1110#4) && (IsZero imm8)) : Bool)
      then (sailThrow ((Error_See "ERET")) : SailM Unit)
      else (pure ())
      let d := 15
      let n := (BitVec.toNat Rn)
      let setflags : Bool := true
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      if ((n != 14) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((InITBlock ()) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SUB_i_Op_A_txt d imm32 n setflags))
  else (pure ())

def decode_aarch32_instrs_SUB_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:15700.29-15700.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if ((Rn == 0b1101#4) : Bool)
      then (sailThrow ((Error_See "SUB (SP minus register)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_SUB_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_SUB_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags ← (( do (pure (! (← (InITBlock ())))) ) : SailM Bool )
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_SUB_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_SUB_r_T2enc_A_txt (S : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then (sailThrow ((Error_See "CMP (register)")) : SailM Unit)
      else (pure ())
      if ((Rn == 0b1101#4) : Bool)
      then (sailThrow ((Error_See "SUB (SP minus register)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((((d == 15) && (! setflags)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SUB_r_Op_A_txt d m n setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_SUB_rr_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:15817.29-15817.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let setflags : Bool := (S == 1#1)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if (((((d == 15) || (n == 15)) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SUB_rr_Op_A_txt d m n s setflags shift_t))
  else (pure ())

def decode_aarch32_instrs_SUB_SP_i_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:15870.29-15870.30"
      let d := (BitVec.toNat Rd)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      (execute_aarch32_instrs_SUB_SP_i_Op_A_txt d imm32 setflags))
  else (pure ())

def decode_aarch32_instrs_SUB_SP_i_T1enc_A_txt (imm7 : (BitVec 7)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := 13
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm7 +++ 0b00#2) 32)
      (execute_aarch32_instrs_SUB_SP_i_Op_A_txt d imm32 setflags))
  else (pure ())

def decode_aarch32_instrs_SUB_SP_i_T2enc_A_txt (i : (BitVec 1)) (S : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then (sailThrow ((Error_See "CMP (immediate)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let setflags : Bool := (S == 1#1)
      let imm32 ← (( do (T32ExpandImm ((i +++ imm3) +++ imm8)) ) : SailM (BitVec 32) )
      if (((d == 15) && (! setflags)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SUB_SP_i_Op_A_txt d imm32 setflags))
  else (pure ())

def decode_aarch32_instrs_SUB_SP_i_T3enc_A_txt (i : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let setflags : Bool := false
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend ((i +++ imm3) +++ imm8) 32)
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SUB_SP_i_Op_A_txt d imm32 setflags))
  else (pure ())

def decode_aarch32_instrs_SUB_SP_r_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:15986.29-15986.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_SUB_SP_r_Op_A_txt d m setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_SUB_SP_r_T1enc_A_txt (S : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((Rd == 0b1111#4) && (S == 1#1)) : Bool)
      then (sailThrow ((Error_See "CMP (register)")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if ((((d == 15) && (! setflags)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SUB_SP_r_Op_A_txt d m setflags shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_SVC_A1enc_A_txt (cond : (BitVec 4)) (imm24 : (BitVec 24)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:16058.29-16058.30"
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm24 32)
      (execute_aarch32_instrs_SVC_Op_A_txt imm32))
  else (pure ())

def decode_aarch32_instrs_SVC_T1enc_A_txt (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      (execute_aarch32_instrs_SVC_Op_A_txt imm32))
  else (pure ())

def decode_aarch32_instrs_SXTAB16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:16102.29-16102.30"
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "SXTB16")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SXTAB16_Op_A_txt d m n rotation))
  else (pure ())

def decode_aarch32_instrs_SXTAB16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "SXTB16")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SXTAB16_Op_A_txt d m n rotation))
  else (pure ())

def decode_aarch32_instrs_SXTAB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:16177.29-16177.30"
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "SXTB")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SXTAB_Op_A_txt d m n rotation))
  else (pure ())

def decode_aarch32_instrs_SXTAB_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "SXTB")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SXTAB_Op_A_txt d m n rotation))
  else (pure ())

def decode_aarch32_instrs_SXTAH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:16252.29-16252.30"
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "SXTH")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SXTAH_Op_A_txt d m n rotation))
  else (pure ())

def decode_aarch32_instrs_SXTAH_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "SXTH")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SXTAH_Op_A_txt d m n rotation))
  else (pure ())

def decode_aarch32_instrs_SXTB16_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:16328.29-16328.30"
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SXTB16_Op_A_txt d m rotation))
  else (pure ())

def decode_aarch32_instrs_SXTB16_T1enc_A_txt (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SXTB16_Op_A_txt d m rotation))
  else (pure ())

def decode_aarch32_instrs_SXTB_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:16393.29-16393.30"
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SXTB_Op_A_txt d m rotation))
  else (pure ())

def decode_aarch32_instrs_SXTB_T1enc_A_txt (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let rotation := 0
      (execute_aarch32_instrs_SXTB_Op_A_txt d m rotation))
  else (pure ())

def decode_aarch32_instrs_SXTB_T2enc_A_txt (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SXTB_Op_A_txt d m rotation))
  else (pure ())

def decode_aarch32_instrs_SXTH_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:16477.29-16477.30"
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SXTH_Op_A_txt d m rotation))
  else (pure ())

def decode_aarch32_instrs_SXTH_T1enc_A_txt (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let rotation := 0
      (execute_aarch32_instrs_SXTH_Op_A_txt d m rotation))
  else (pure ())

def decode_aarch32_instrs_SXTH_T2enc_A_txt (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SXTH_Op_A_txt d m rotation))
  else (pure ())

def decode_aarch32_instrs_TBB_T1enc_A_txt (Rn : (BitVec 4)) (H : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let is_tbh : Bool := (H == 1#1)
      if ((m == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((InITBlock ()) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_TBB_Op_A_txt is_tbh m n))
  else (pure ())

def decode_aarch32_instrs_TEQ_i_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:16607.29-16607.30"
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let n := (BitVec.toNat Rn)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (A32ExpandImm_C imm12 (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      (execute_aarch32_instrs_TEQ_i_Op_A_txt carry imm32 n))
  else (pure ())

def decode_aarch32_instrs_TEQ_i_T1enc_A_txt (i : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let n := (BitVec.toNat Rn)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (T32ExpandImm_C ((i +++ imm3) +++ imm8) (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let carry := carry
      (execute_aarch32_instrs_TEQ_i_Op_A_txt carry imm32 n))
  else (pure ())

def decode_aarch32_instrs_TEQ_r_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:16674.29-16674.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_TEQ_r_Op_A_txt m n shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_TEQ_r_T1enc_A_txt (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((n == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_TEQ_r_Op_A_txt m n shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_TEQ_rr_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:16753.29-16753.30"
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if ((((n == 15) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_TEQ_rr_Op_A_txt m n s shift_t))
  else (pure ())

def decode_aarch32_instrs_TST_i_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:16794.29-16794.30"
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let n := (BitVec.toNat Rn)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (A32ExpandImm_C imm12 (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      (execute_aarch32_instrs_TST_i_Op_A_txt carry imm32 n))
  else (pure ())

def decode_aarch32_instrs_TST_i_T1enc_A_txt (i : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let carry ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let n := (BitVec.toNat Rn)
      let (carry, imm32) ← (( do
        let (tup__0, tup__1) ← do (T32ExpandImm_C ((i +++ imm3) +++ imm8) (← readReg PSTATE).C)
        let imm32 : (BitVec 32) := tup__0
        let carry : (BitVec 1) := tup__1
        (pure (carry, imm32)) ) : SailM ((BitVec 1) × (BitVec 32)) )
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let carry := carry
      (execute_aarch32_instrs_TST_i_Op_A_txt carry imm32 n))
  else (pure ())

def decode_aarch32_instrs_TST_r_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (imm5 : (BitVec 5)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:16861.29-16861.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      (execute_aarch32_instrs_TST_r_Op_A_txt m n shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_TST_r_T1enc_A_txt (Rm : (BitVec 3)) (Rn : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let (shift_n, shift_t) : (Int × SRType) :=
        let (tup__0, tup__1) := ((SRType_LSL, 0) : (SRType × Nat))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (shift_n, shift_t)
      let shift_n := shift_n
      (execute_aarch32_instrs_TST_r_Op_A_txt m n shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_TST_r_T2enc_A_txt (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (imm2 : (BitVec 2)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift stype (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((n == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_TST_r_Op_A_txt m n shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_TST_rr_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rs : (BitVec 4)) (stype : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:16962.29-16962.30"
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let s := (BitVec.toNat Rs)
      let shift_t ← (( do (DecodeRegShift stype) ) : SailM SRType )
      if ((((n == 15) || (m == 15)) || (s == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_TST_rr_Op_A_txt m n s shift_t))
  else (pure ())

def decode_aarch32_instrs_UADD16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:17006.29-17006.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UADD16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UADD16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UADD16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UADD8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:17077.29-17077.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UADD8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UADD8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UADD8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UASX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:17142.29-17142.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UASX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UASX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UASX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UBFX_A1enc_A_txt (cond : (BitVec 4)) (widthm1 : (BitVec 5)) (Rd : (BitVec 4)) (lsb : (BitVec 5)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:17203.29-17203.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let lsbit := (BitVec.toNat lsb)
      let widthminus1 := (BitVec.toNat widthm1)
      let msbit := (lsbit +i widthminus1)
      if (((d == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((msbit >b 31) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UBFX_Op_A_txt d lsbit msbit n))
  else (pure ())

def decode_aarch32_instrs_UBFX_T1enc_A_txt (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (widthm1 : (BitVec 5)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let lsbit := (BitVec.toNat (imm3 +++ imm2))
      let widthminus1 := (BitVec.toNat widthm1)
      let msbit := (lsbit +i widthminus1)
      if (((d == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((msbit >b 31) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UBFX_Op_A_txt d lsbit msbit n))
  else (pure ())

def decode_aarch32_instrs_UDF_A1enc_A_txt (imm12 : (BitVec 12)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm12 +++ imm4) 32)
      (execute_aarch32_instrs_UDF_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_UDF_T1enc_A_txt (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend imm8 32)
      (execute_aarch32_instrs_UDF_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_UDF_T2enc_A_txt (imm4 : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm4 +++ imm12) 32)
      (execute_aarch32_instrs_UDF_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_UDIV_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:17339.29-17339.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a != 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UDIV_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UDIV_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      if (((((d == 15) || (n == 15)) || (m == 15)) || (a != 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UDIV_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UHADD16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:17402.29-17402.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UHADD16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UHADD16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UHADD16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UHADD8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:17469.29-17469.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UHADD8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UHADD8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UHADD8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UHASX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:17532.29-17532.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UHASX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UHASX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UHASX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UHSAX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:17595.29-17595.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UHSAX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UHSAX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UHSAX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UHSUB16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:17658.29-17658.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UHSUB16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UHSUB16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UHSUB16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UHSUB8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:17725.29-17725.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UHSUB8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UHSUB8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UHSUB8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UMAAL_A1enc_A_txt (cond : (BitVec 4)) (RdHi : (BitVec 4)) (RdLo : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:17787.29-17787.30"
      let dLo := (BitVec.toNat RdLo)
      let dHi := (BitVec.toNat RdHi)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((dHi == dLo) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UMAAL_Op_A_txt dHi dLo m n))
  else (pure ())

def decode_aarch32_instrs_UMAAL_T1enc_A_txt (Rn : (BitVec 4)) (RdLo : (BitVec 4)) (RdHi : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let dLo := (BitVec.toNat RdLo)
      let dHi := (BitVec.toNat RdHi)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((dHi == dLo) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UMAAL_Op_A_txt dHi dLo m n))
  else (pure ())

def decode_aarch32_instrs_UMLAL_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (RdHi : (BitVec 4)) (RdLo : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:17860.29-17860.30"
      let dLo := (BitVec.toNat RdLo)
      let dHi := (BitVec.toNat RdHi)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((dHi == dLo) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UMLAL_Op_A_txt dHi dLo m n setflags))
  else (pure ())

def decode_aarch32_instrs_UMLAL_T1enc_A_txt (Rn : (BitVec 4)) (RdLo : (BitVec 4)) (RdHi : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let dLo := (BitVec.toNat RdLo)
      let dHi := (BitVec.toNat RdHi)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := false
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((dHi == dLo) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UMLAL_Op_A_txt dHi dLo m n setflags))
  else (pure ())

def decode_aarch32_instrs_UMULL_A1enc_A_txt (cond : (BitVec 4)) (S : (BitVec 1)) (RdHi : (BitVec 4)) (RdLo : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:17936.29-17936.30"
      let dLo := (BitVec.toNat RdLo)
      let dHi := (BitVec.toNat RdHi)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := (S == 1#1)
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((dHi == dLo) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UMULL_Op_A_txt dHi dLo m n setflags))
  else (pure ())

def decode_aarch32_instrs_UMULL_T1enc_A_txt (Rn : (BitVec 4)) (RdLo : (BitVec 4)) (RdHi : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let dLo := (BitVec.toNat RdLo)
      let dHi := (BitVec.toNat RdHi)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let setflags : Bool := false
      if (((((dLo == 15) || (dHi == 15)) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((dHi == dLo) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UMULL_Op_A_txt dHi dLo m n setflags))
  else (pure ())

def decode_aarch32_instrs_UQADD16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:18008.29-18008.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UQADD16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UQADD16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UQADD16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UQADD8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:18075.29-18075.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UQADD8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UQADD8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UQADD8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UQASX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:18138.29-18138.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UQASX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UQASX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UQASX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UQSAX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:18201.29-18201.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UQSAX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UQSAX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UQSAX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UQSUB16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:18264.29-18264.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UQSUB16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UQSUB16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UQSUB16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UQSUB8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:18331.29-18331.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UQSUB8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UQSUB8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UQSUB8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_USAD8_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:18396.29-18396.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_USAD8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_USAD8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_USAD8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_USADA8_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (Ra : (BitVec 4)) (Rm : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:18457.29-18457.30"
      if ((Ra == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "USAD8")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_USADA8_Op_A_txt a d m n))
  else (pure ())

def decode_aarch32_instrs_USADA8_T1enc_A_txt (Rn : (BitVec 4)) (Ra : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Ra == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "USAD8")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let a := (BitVec.toNat Ra)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_USADA8_Op_A_txt a d m n))
  else (pure ())

def decode_aarch32_instrs_USAT16_A1enc_A_txt (cond : (BitVec 4)) (sat_imm : (BitVec 4)) (Rd : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:18534.29-18534.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let saturate_to := (BitVec.toNat sat_imm)
      if (((d == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_USAT16_Op_A_txt d n saturate_to))
  else (pure ())

def decode_aarch32_instrs_USAT16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (sat_imm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let saturate_to := (BitVec.toNat sat_imm)
      if (((d == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_USAT16_Op_A_txt d n saturate_to))
  else (pure ())

def decode_aarch32_instrs_USAT_A1enc_A_txt (cond : (BitVec 4)) (sat_imm : (BitVec 5)) (Rd : (BitVec 4)) (imm5 : (BitVec 5)) (sh : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:18606.29-18606.30"
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let saturate_to := (BitVec.toNat sat_imm)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift (sh +++ 0#1) imm5)
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((d == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let shift_t := shift_t
      let shift_n := shift_n
      (execute_aarch32_instrs_USAT_Op_A_txt d n saturate_to shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_USAT_T1enc_A_txt (sh : (BitVec 1)) (Rn : (BitVec 4)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm2 : (BitVec 2)) (sat_imm : (BitVec 5)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let shift_n ← (( do (undefined_int ()) ) : SailM Int )
      let shift_t ← (( do (undefined_SRType ()) ) : SailM SRType )
      if (((sh == 1#1) && ((imm3 +++ imm2) == 0b00000#5)) : Bool)
      then (sailThrow ((Error_See "USAT16")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let saturate_to := (BitVec.toNat sat_imm)
      let (shift_n, shift_t) ← (( do
        let (tup__0, tup__1) ← do (DecodeImmShift (sh +++ 0#1) (imm3 +++ imm2))
        let shift_t : SRType := tup__0
        let shift_n : Int := tup__1
        (pure (shift_n, shift_t)) ) : SailM (Int × SRType) )
      let shift_n := shift_n
      if (((d == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_USAT_Op_A_txt d n saturate_to shift_n shift_t))
  else (pure ())

def decode_aarch32_instrs_USAX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:18689.29-18689.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_USAX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_USAX_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_USAX_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_USUB16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:18754.29-18754.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_USUB16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_USUB16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_USUB16_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_USUB8_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:18825.29-18825.30"
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_USUB8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_USUB8_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_USUB8_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_UXTAB16_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:18887.29-18887.30"
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "UXTB16")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UXTAB16_Op_A_txt d m n rotation))
  else (pure ())

def decode_aarch32_instrs_UXTAB16_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "UXTB16")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UXTAB16_Op_A_txt d m n rotation))
  else (pure ())

def decode_aarch32_instrs_UXTAB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:18962.29-18962.30"
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "UXTB")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UXTAB_Op_A_txt d m n rotation))
  else (pure ())

def decode_aarch32_instrs_UXTAB_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "UXTB")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UXTAB_Op_A_txt d m n rotation))
  else (pure ())

def decode_aarch32_instrs_UXTAH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:19037.29-19037.30"
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "UXTH")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UXTAH_Op_A_txt d m n rotation))
  else (pure ())

def decode_aarch32_instrs_UXTAH_T1enc_A_txt (Rn : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then (sailThrow ((Error_See "UXTH")) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UXTAH_Op_A_txt d m n rotation))
  else (pure ())

def decode_aarch32_instrs_UXTB16_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:19113.29-19113.30"
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UXTB16_Op_A_txt d m rotation))
  else (pure ())

def decode_aarch32_instrs_UXTB16_T1enc_A_txt (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UXTB16_Op_A_txt d m rotation))
  else (pure ())

def decode_aarch32_instrs_UXTB_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:19178.29-19178.30"
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UXTB_Op_A_txt d m rotation))
  else (pure ())

def decode_aarch32_instrs_UXTB_T1enc_A_txt (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let rotation := 0
      (execute_aarch32_instrs_UXTB_Op_A_txt d m rotation))
  else (pure ())

def decode_aarch32_instrs_UXTB_T2enc_A_txt (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UXTB_Op_A_txt d m rotation))
  else (pure ())

def decode_aarch32_instrs_UXTH_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:19262.29-19262.30"
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UXTH_Op_A_txt d m rotation))
  else (pure ())

def decode_aarch32_instrs_UXTH_T1enc_A_txt (Rm : (BitVec 3)) (Rd : (BitVec 3)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let rotation := 0
      (execute_aarch32_instrs_UXTH_Op_A_txt d m rotation))
  else (pure ())

def decode_aarch32_instrs_UXTH_T2enc_A_txt (Rd : (BitVec 4)) (rotate : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let m := (BitVec.toNat Rm)
      let rotation := (BitVec.toNat (rotate +++ 0b000#3))
      if (((d == 15) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_UXTH_Op_A_txt d m rotation))
  else (pure ())

def decode_aarch32_instrs_VABA_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let long_destination : Bool := false
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VABA_Op_A_txt d elements esize long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VABA_A2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let long_destination : Bool := true
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs := 1
      (execute_aarch32_instrs_VABA_Op_A_txt d elements esize long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VABA_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let long_destination : Bool := false
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VABA_Op_A_txt d elements esize long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VABA_T2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let long_destination : Bool := true
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs := 1
      (execute_aarch32_instrs_VABA_Op_A_txt d elements esize long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VABD_f_A1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VABD_f_Op_A_txt d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VABD_f_T1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (sz == 1#1)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VABD_f_Op_A_txt d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VABD_i_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let long_destination : Bool := false
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VABD_i_Op_A_txt d elements esize long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VABD_i_A2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let long_destination : Bool := true
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs := 1
      (execute_aarch32_instrs_VABD_i_Op_A_txt d elements esize long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VABD_i_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let long_destination : Bool := false
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VABD_i_Op_A_txt d elements esize long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VABD_i_T2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let long_destination : Bool := true
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs := 1
      (execute_aarch32_instrs_VABD_i_Op_A_txt d elements esize long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VABS_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((F == 1#1) && (((size == 0b01#2) && (! (HaveFP16Ext ()))) || (size == 0b00#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let advsimd : Bool := true
      let floating_point : Bool := (F == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VABS_Op_A_txt advsimd d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VABS_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:19863.29-19863.30"
      let floating_point ← (( do (undefined_bool ()) ) : SailM Bool )
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let regs ← (( do (undefined_int ()) ) : SailM Int )
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let regs := regs
      let elements := elements
      let floating_point := floating_point
      let advsimd : Bool := false
      let esize : Nat := 16
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, esize, m) : (Nat × Int × Nat) :=
        match (size : BitVec 2) with
        | 0b01 =>
          (let esize : Nat := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b10 =>
          (let esize : Nat := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b11 =>
          (let esize : Nat := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m))
        | _ => (d, esize, m)
      let m := m
      let esize := esize
      let d := d
      (execute_aarch32_instrs_VABS_Op_A_txt advsimd d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VABS_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((F == 1#1) && (((size == 0b01#2) && (! (HaveFP16Ext ()))) || (size == 0b00#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((F == 1#1) && (size == 0b01#2))) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let advsimd : Bool := true
      let floating_point : Bool := (F == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VABS_Op_A_txt advsimd d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VABS_T2enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let floating_point ← (( do (undefined_bool ()) ) : SailM Bool )
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let regs ← (( do (undefined_int ()) ) : SailM Int )
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (size == 0b01#2)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let regs := regs
      let elements := elements
      let floating_point := floating_point
      let advsimd : Bool := false
      let esize : Nat := 16
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, esize, m) : (Nat × Int × Nat) :=
        match (size : BitVec 2) with
        | 0b01 =>
          (let esize : Nat := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b10 =>
          (let esize : Nat := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b11 =>
          (let esize : Nat := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m))
        | _ => (d, esize, m)
      let m := m
      let esize := esize
      let d := d
      (execute_aarch32_instrs_VABS_Op_A_txt advsimd d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VACGE_A1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let or_equal : Bool := (op == 0#1)
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VACGE_Op_A_txt d elements esize m n or_equal regs))
  else (pure ())

def decode_aarch32_instrs_VACGE_T1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (sz == 1#1)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let or_equal : Bool := (op == 0#1)
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VACGE_Op_A_txt d elements esize m n or_equal regs))
  else (pure ())

def decode_aarch32_instrs_VADD_f_A1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let advsimd : Bool := true
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VADD_f_Op_A_txt advsimd d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VADD_f_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:20225.29-20225.30"
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let regs ← (( do (undefined_int ()) ) : SailM Int )
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let regs := regs
      let elements := elements
      let advsimd : Bool := false
      let esize : Nat := 16
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let n ← (( do (undefined_range 0 31) ) : SailM Nat )
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
        match (size : BitVec 2) with
        | 0b01 =>
          (let esize : Nat := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b10 =>
          (let esize : Nat := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b11 =>
          (let esize : Nat := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let n : Nat := (BitVec.toNat (N +++ Vn))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m, n))
        | _ => (d, esize, m, n)
      let n := n
      let m := m
      let esize := esize
      let d := d
      (execute_aarch32_instrs_VADD_f_Op_A_txt advsimd d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VADD_f_T1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (sz == 1#1)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let advsimd : Bool := true
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VADD_f_Op_A_txt advsimd d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VADD_f_T2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let regs ← (( do (undefined_int ()) ) : SailM Int )
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (size == 0b01#2)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let regs := regs
      let elements := elements
      let advsimd : Bool := false
      let esize : Nat := 16
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let n ← (( do (undefined_range 0 31) ) : SailM Nat )
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
        match (size : BitVec 2) with
        | 0b01 =>
          (let esize : Nat := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b10 =>
          (let esize : Nat := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b11 =>
          (let esize : Nat := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let n : Nat := (BitVec.toNat (N +++ Vn))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m, n))
        | _ => (d, esize, m, n)
      let n := n
      let m := m
      let esize := esize
      let d := d
      (execute_aarch32_instrs_VADD_f_Op_A_txt advsimd d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VADDHN_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VADDHN_Op_A_txt d elements esize m n))
  else (pure ())

def decode_aarch32_instrs_VADDHN_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VADDHN_Op_A_txt d elements esize m n))
  else (pure ())

def decode_aarch32_instrs_VADD_i_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VADD_i_Op_A_txt d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VADD_i_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VADD_i_Op_A_txt d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VADDL_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((op == 1#1) && ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let is_vaddw : Bool := (op == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VADDL_Op_A_txt d elements esize is_vaddw m n is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VADDL_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((op == 1#1) && ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let is_vaddw : Bool := (op == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VADDL_Op_A_txt d elements esize is_vaddw m n is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VAND_r_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VAND_r_Op_A_txt d m n regs))
  else (pure ())

def decode_aarch32_instrs_VAND_r_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VAND_r_Op_A_txt d m n regs))
  else (pure ())

def decode_aarch32_instrs_VBIC_i_A1enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((BitVec.join1 [(BitVec.access cmode 0)]) == 0#1) || ((Sail.BitVec.extractLsb cmode 3 2) == 0b11#2)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let imm64 ← (( do (AdvSIMDExpandImm 1#1 cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64) )
      let d := (BitVec.toNat (D +++ Vd))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VBIC_i_Op_A_txt d imm64 regs))
  else (pure ())

def decode_aarch32_instrs_VBIC_i_A2enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((BitVec.join1 [(BitVec.access cmode 0)]) == 0#1) || ((Sail.BitVec.extractLsb cmode 3 2) == 0b11#2)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let imm64 ← (( do (AdvSIMDExpandImm 1#1 cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64) )
      let d := (BitVec.toNat (D +++ Vd))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VBIC_i_Op_A_txt d imm64 regs))
  else (pure ())

def decode_aarch32_instrs_VBIC_i_T1enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((BitVec.join1 [(BitVec.access cmode 0)]) == 0#1) || ((Sail.BitVec.extractLsb cmode 3 2) == 0b11#2)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let imm64 ← (( do (AdvSIMDExpandImm 1#1 cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64) )
      let d := (BitVec.toNat (D +++ Vd))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VBIC_i_Op_A_txt d imm64 regs))
  else (pure ())

def decode_aarch32_instrs_VBIC_i_T2enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((BitVec.join1 [(BitVec.access cmode 0)]) == 0#1) || ((Sail.BitVec.extractLsb cmode 3 2) == 0b11#2)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let imm64 ← (( do (AdvSIMDExpandImm 1#1 cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64) )
      let d := (BitVec.toNat (D +++ Vd))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VBIC_i_Op_A_txt d imm64 regs))
  else (pure ())

def decode_aarch32_instrs_VBIC_r_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VBIC_r_Op_A_txt d m n regs))
  else (pure ())

def decode_aarch32_instrs_VBIC_r_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VBIC_r_Op_A_txt d m n regs))
  else (pure ())

def decode_aarch32_instrs_VBIF_A1enc_A_txt (D : (BitVec 1)) (op : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let operation : VBitOps := VBitOps_VBIF
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((op == 0b00#2) : Bool)
      then (sailThrow ((Error_See "VEOR")) : SailM Unit)
      else (pure ())
      let operation : VBitOps :=
        if ((op == 0b01#2) : Bool)
        then VBitOps_VBSL
        else operation
      let operation : VBitOps :=
        if ((op == 0b10#2) : Bool)
        then VBitOps_VBIT
        else operation
      let operation : VBitOps :=
        if ((op == 0b11#2) : Bool)
        then VBitOps_VBIF
        else operation
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VBIF_Op_A_txt d m n operation regs))
  else (pure ())

def decode_aarch32_instrs_VBIF_T1enc_A_txt (D : (BitVec 1)) (op : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let operation : VBitOps := VBitOps_VBIF
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((op == 0b00#2) : Bool)
      then (sailThrow ((Error_See "VEOR")) : SailM Unit)
      else (pure ())
      let operation : VBitOps :=
        if ((op == 0b01#2) : Bool)
        then VBitOps_VBSL
        else operation
      let operation : VBitOps :=
        if ((op == 0b10#2) : Bool)
        then VBitOps_VBIT
        else operation
      let operation : VBitOps :=
        if ((op == 0b11#2) : Bool)
        then VBitOps_VBIF
        else operation
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VBIF_Op_A_txt d m n operation regs))
  else (pure ())

def decode_aarch32_instrs_VCEQ_i_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((F == 1#1) && (((size == 0b01#2) && (! (HaveFP16Ext ()))) || (size == 0b00#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let floating_point : Bool := (F == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCEQ_i_Op_A_txt d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VCEQ_i_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((F == 1#1) && (((size == 0b01#2) && (! (HaveFP16Ext ()))) || (size == 0b00#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((F == 1#1) && (size == 0b01#2))) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let floating_point : Bool := (F == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCEQ_i_Op_A_txt d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VCEQ_r_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let int_operation : Bool := true
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCEQ_r_Op_A_txt d elements esize int_operation m n regs))
  else (pure ())

def decode_aarch32_instrs_VCEQ_r_A2enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let int_operation : Bool := false
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCEQ_r_Op_A_txt d elements esize int_operation m n regs))
  else (pure ())

def decode_aarch32_instrs_VCEQ_r_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let int_operation : Bool := true
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCEQ_r_Op_A_txt d elements esize int_operation m n regs))
  else (pure ())

def decode_aarch32_instrs_VCEQ_r_T2enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (sz == 1#1)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let int_operation : Bool := false
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCEQ_r_Op_A_txt d elements esize int_operation m n regs))
  else (pure ())

def decode_aarch32_instrs_VCGE_i_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((F == 1#1) && (((size == 0b01#2) && (! (HaveFP16Ext ()))) || (size == 0b00#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let floating_point : Bool := (F == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCGE_i_Op_A_txt d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VCGE_i_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((F == 1#1) && (((size == 0b01#2) && (! (HaveFP16Ext ()))) || (size == 0b00#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((F == 1#1) && (size == 0b01#2))) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let floating_point : Bool := (F == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCGE_i_Op_A_txt d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VCGE_r_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let vtype : VCGEType :=
        if ((U == 1#1) : Bool)
        then VCGEType_unsigned
        else VCGEType_signed
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCGE_r_Op_A_txt d elements esize m n regs vtype))
  else (pure ())

def decode_aarch32_instrs_VCGE_r_A2enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let vtype : VCGEType := VCGEType_fp
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCGE_r_Op_A_txt d elements esize m n regs vtype))
  else (pure ())

def decode_aarch32_instrs_VCGE_r_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let vtype : VCGEType :=
        if ((U == 1#1) : Bool)
        then VCGEType_unsigned
        else VCGEType_signed
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCGE_r_Op_A_txt d elements esize m n regs vtype))
  else (pure ())

def decode_aarch32_instrs_VCGE_r_T2enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (sz == 1#1)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let vtype : VCGEType := VCGEType_fp
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCGE_r_Op_A_txt d elements esize m n regs vtype))
  else (pure ())

def decode_aarch32_instrs_VCGT_i_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((F == 1#1) && (((size == 0b01#2) && (! (HaveFP16Ext ()))) || (size == 0b00#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let floating_point : Bool := (F == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCGT_i_Op_A_txt d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VCGT_i_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((F == 1#1) && (((size == 0b01#2) && (! (HaveFP16Ext ()))) || (size == 0b00#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((F == 1#1) && (size == 0b01#2))) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let floating_point : Bool := (F == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCGT_i_Op_A_txt d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VCGT_r_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let vtype : VCGTtype :=
        if ((U == 1#1) : Bool)
        then VCGTtype_unsigned
        else VCGTtype_signed
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCGT_r_Op_A_txt d elements esize m n regs vtype))
  else (pure ())

def decode_aarch32_instrs_VCGT_r_A2enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let vtype : VCGTtype := VCGTtype_fp
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCGT_r_Op_A_txt d elements esize m n regs vtype))
  else (pure ())

def decode_aarch32_instrs_VCGT_r_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let vtype : VCGTtype :=
        if ((U == 1#1) : Bool)
        then VCGTtype_unsigned
        else VCGTtype_signed
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCGT_r_Op_A_txt d elements esize m n regs vtype))
  else (pure ())

def decode_aarch32_instrs_VCGT_r_T2enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (sz == 1#1)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let vtype : VCGTtype := VCGTtype_fp
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCGT_r_Op_A_txt d elements esize m n regs vtype))
  else (pure ())

def decode_aarch32_instrs_VCLE_i_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((F == 1#1) && (((size == 0b01#2) && (! (HaveFP16Ext ()))) || (size == 0b00#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let floating_point : Bool := (F == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCLE_i_Op_A_txt d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VCLE_i_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((F == 1#1) && (((size == 0b01#2) && (! (HaveFP16Ext ()))) || (size == 0b00#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((F == 1#1) && (size == 0b01#2))) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let floating_point : Bool := (F == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCLE_i_Op_A_txt d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VCLS_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCLS_Op_A_txt d elements esize m regs))
  else (pure ())

def decode_aarch32_instrs_VCLS_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCLS_Op_A_txt d elements esize m regs))
  else (pure ())

def decode_aarch32_instrs_VCLT_i_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((F == 1#1) && (((size == 0b01#2) && (! (HaveFP16Ext ()))) || (size == 0b00#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let floating_point : Bool := (F == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCLT_i_Op_A_txt d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VCLT_i_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((F == 1#1) && (((size == 0b01#2) && (! (HaveFP16Ext ()))) || (size == 0b00#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((F == 1#1) && (size == 0b01#2))) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let floating_point : Bool := (F == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCLT_i_Op_A_txt d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VCLZ_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCLZ_Op_A_txt d elements esize m regs))
  else (pure ())

def decode_aarch32_instrs_VCLZ_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCLZ_Op_A_txt d elements esize m regs))
  else (pure ())

def decode_aarch32_instrs_VCMP_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (E : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:22307.29-22307.30"
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let quiet_nan_exc : Bool := (E == 1#1)
      let with_zero : Bool := false
      let esize : Nat := 16
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, esize, m) : (Nat × Int × Nat) :=
        match (size : BitVec 2) with
        | 0b01 =>
          (let esize : Nat := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b10 =>
          (let esize : Nat := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b11 =>
          (let esize : Nat := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m))
        | _ => (d, esize, m)
      let m := m
      let esize := esize
      let d := d
      (execute_aarch32_instrs_VCMP_Op_A_txt d esize m quiet_nan_exc with_zero))
  else (pure ())

def decode_aarch32_instrs_VCMP_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (E : (BitVec 1)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:22361.29-22361.30"
      let m ← (( do (undefined_int ()) ) : SailM Int )
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let m := m
      let quiet_nan_exc : Bool := (E == 1#1)
      let with_zero : Bool := true
      let esize : Nat := 16
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, esize) : (Nat × Int) :=
        match (size : BitVec 2) with
        | 0b01 =>
          (let esize : Nat := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          (d, esize))
        | 0b10 =>
          (let esize : Nat := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          (d, esize))
        | 0b11 =>
          (let esize : Nat := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          (d, esize))
        | _ => (d, esize)
      let esize := esize
      let d := d
      (execute_aarch32_instrs_VCMP_Op_A_txt d esize m quiet_nan_exc with_zero))
  else (pure ())

def decode_aarch32_instrs_VCMP_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (E : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (size == 0b01#2)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let quiet_nan_exc : Bool := (E == 1#1)
      let with_zero : Bool := false
      let esize : Nat := 16
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, esize, m) : (Nat × Int × Nat) :=
        match (size : BitVec 2) with
        | 0b01 =>
          (let esize : Nat := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b10 =>
          (let esize : Nat := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m))
        | 0b11 =>
          (let esize : Nat := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m))
        | _ => (d, esize, m)
      let m := m
      let esize := esize
      let d := d
      (execute_aarch32_instrs_VCMP_Op_A_txt d esize m quiet_nan_exc with_zero))
  else (pure ())

def decode_aarch32_instrs_VCMP_T2enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (E : (BitVec 1)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let m ← (( do (undefined_int ()) ) : SailM Int )
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (size == 0b01#2)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let m := m
      let quiet_nan_exc : Bool := (E == 1#1)
      let with_zero : Bool := true
      let esize : Nat := 16
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, esize) : (Nat × Int) :=
        match (size : BitVec 2) with
        | 0b01 =>
          (let esize : Nat := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          (d, esize))
        | 0b10 =>
          (let esize : Nat := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          (d, esize))
        | 0b11 =>
          (let esize : Nat := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          (d, esize))
        | _ => (d, esize)
      let esize := esize
      let d := d
      (execute_aarch32_instrs_VCMP_Op_A_txt d esize m quiet_nan_exc with_zero))
  else (pure ())

def decode_aarch32_instrs_VCNT_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size != 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := 8
      let elements := 8
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCNT_Op_A_txt d elements esize m regs))
  else (pure ())

def decode_aarch32_instrs_VCNT_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size != 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := 8
      let elements := 8
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCNT_Op_A_txt d elements esize m regs))
  else (pure ())

def decode_aarch32_instrs_VCVTB_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (op : (BitVec 1)) (Vd : (BitVec 4)) (sz : (BitVec 1)) (T : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:22617.29-22617.30"
      let uses_double : Bool := (sz == 1#1)
      let convert_from_half : Bool := (op == 0#1)
      let lowbit :=
        if ((T == 1#1) : Bool)
        then 16
        else 0
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, m) : (Nat × Nat) :=
        if (uses_double : Bool)
        then
          (let (d, m) : (Nat × Nat) :=
            if (convert_from_half : Bool)
            then
              (let d : Nat := (BitVec.toNat (D +++ Vd))
              let m : Nat := (BitVec.toNat (Vm +++ M))
              (d, m))
            else
              (let d : Nat := (BitVec.toNat (Vd +++ D))
              let m : Nat := (BitVec.toNat (M +++ Vm))
              (d, m))
          (d, m))
        else
          (let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, m))
      let m := m
      let d := d
      (execute_aarch32_instrs_VCVTB_Op_A_txt convert_from_half d lowbit m uses_double))
  else (pure ())

def decode_aarch32_instrs_VCVTB_T1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (Vd : (BitVec 4)) (sz : (BitVec 1)) (T : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let uses_double : Bool := (sz == 1#1)
      let convert_from_half : Bool := (op == 0#1)
      let lowbit :=
        if ((T == 1#1) : Bool)
        then 16
        else 0
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, m) : (Nat × Nat) :=
        if (uses_double : Bool)
        then
          (let (d, m) : (Nat × Nat) :=
            if (convert_from_half : Bool)
            then
              (let d : Nat := (BitVec.toNat (D +++ Vd))
              let m : Nat := (BitVec.toNat (Vm +++ M))
              (d, m))
            else
              (let d : Nat := (BitVec.toNat (Vd +++ D))
              let m : Nat := (BitVec.toNat (M +++ Vm))
              (d, m))
          (d, m))
        else
          (let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, m))
      let m := m
      let d := d
      (execute_aarch32_instrs_VCVTB_Op_A_txt convert_from_half d lowbit m uses_double))
  else (pure ())

def decode_aarch32_instrs_VCVT_ds_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:22712.29-22712.30"
      let double_to_single : Bool := (size == 0b11#2)
      let d :=
        if (double_to_single : Bool)
        then (BitVec.toNat (Vd +++ D))
        else (BitVec.toNat (D +++ Vd))
      let m :=
        if (double_to_single : Bool)
        then (BitVec.toNat (M +++ Vm))
        else (BitVec.toNat (Vm +++ M))
      sail_assert ((0 ≤b m) && ((m ≤b 31) && ((0 ≤b d) && (d ≤b 31)))) "src/instrs32.sail:22716.68-22716.69"
      (execute_aarch32_instrs_VCVT_ds_Op_A_txt d double_to_single m))
  else (pure ())

def decode_aarch32_instrs_VCVT_ds_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let double_to_single : Bool := (size == 0b11#2)
      let d :=
        if (double_to_single : Bool)
        then (BitVec.toNat (Vd +++ D))
        else (BitVec.toNat (D +++ Vd))
      let m :=
        if (double_to_single : Bool)
        then (BitVec.toNat (M +++ Vm))
        else (BitVec.toNat (Vm +++ M))
      sail_assert ((0 ≤b m) && ((m ≤b 31) && ((0 ≤b d) && (d ≤b 31)))) "src/instrs32.sail:22740.68-22740.69"
      (execute_aarch32_instrs_VCVT_ds_Op_A_txt d double_to_single m))
  else (pure ())

def decode_aarch32_instrs_VCVT_hs_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size != 0b01#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let half_to_single : Bool := (op == 1#1)
      if ((half_to_single && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((! half_to_single) && ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := 16
      let elements := 4
      let m := (BitVec.toNat (M +++ Vm))
      let d := (BitVec.toNat (D +++ Vd))
      (execute_aarch32_instrs_VCVT_hs_Op_A_txt d elements half_to_single m))
  else (pure ())

def decode_aarch32_instrs_VCVT_hs_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size != 0b01#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let half_to_single : Bool := (op == 1#1)
      if ((half_to_single && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((! half_to_single) && ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := 16
      let elements := 4
      let m := (BitVec.toNat (M +++ Vm))
      let d := (BitVec.toNat (D +++ Vd))
      (execute_aarch32_instrs_VCVT_hs_Op_A_txt d elements half_to_single m))
  else (pure ())

def decode_aarch32_instrs_VCVT_is_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 2)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let to_integer : Bool := ((BitVec.join1 [(BitVec.access op 1)]) == 1#1)
      let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access op 0)]) == 1#1)
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (size : BitVec 2) with
        | 0b01 =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
        | 0b10 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ => (elements, esize)
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCVT_is_Op_A_txt d elements esize m regs to_integer is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VCVT_is_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 2)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (size == 0b01#2)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let to_integer : Bool := ((BitVec.join1 [(BitVec.access op 1)]) == 1#1)
      let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access op 0)]) == 1#1)
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (size : BitVec 2) with
        | 0b01 =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
        | 0b10 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ => (elements, esize)
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCVT_is_Op_A_txt d elements esize m regs to_integer is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VCVT_iv_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (opc2 : (BitVec 3)) (Vd : (BitVec 4)) (size : (BitVec 2)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:22999.29-22999.30"
      if (((opc2 != 0b000#3) && (! (let b__0 := opc2
             if (((Sail.BitVec.extractLsb b__0 2 1) == (0b10#2 : (BitVec 2))) : Bool)
             then true
             else false : Bool))) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let esize : Nat := 16
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
      let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
      let to_integer : Bool := ((BitVec.join1 [(BitVec.access opc2 2)]) == 1#1)
      let (d, esize, is_unsigned, m, rounding) ← (( do
        if (to_integer : Bool)
        then
          (do
            let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opc2 0)]) == 0#1)
            let rounding ←
              if ((op == 1#1) : Bool)
              then (pure FPRounding_ZERO)
              else (FPRoundingMode (← (FPSCR_read ())))
            let d : Nat := (BitVec.toNat (Vd +++ D))
            let (esize, m) : (Int × Nat) :=
              match (size : BitVec 2) with
              | 0b01 =>
                (let esize : Nat := 16
                let m : Nat := (BitVec.toNat (Vm +++ M))
                (esize, m))
              | 0b10 =>
                (let esize : Nat := 32
                let m : Nat := (BitVec.toNat (Vm +++ M))
                (esize, m))
              | 0b11 =>
                (let esize : Nat := 64
                let m : Nat := (BitVec.toNat (M +++ Vm))
                (esize, m))
              | _ => (esize, m)
            (pure (d, esize, is_unsigned, m, rounding)))
        else
          (do
            let is_unsigned : Bool := (op == 0#1)
            let rounding ← (FPRoundingMode (← (FPSCR_read ())))
            let m : Nat := (BitVec.toNat (Vm +++ M))
            let (d, esize) : (Nat × Int) :=
              match (size : BitVec 2) with
              | 0b01 =>
                (let esize : Nat := 16
                let d : Nat := (BitVec.toNat (Vd +++ D))
                (d, esize))
              | 0b10 =>
                (let esize : Nat := 32
                let d : Nat := (BitVec.toNat (Vd +++ D))
                (d, esize))
              | 0b11 =>
                (let esize : Nat := 64
                let d : Nat := (BitVec.toNat (D +++ Vd))
                (d, esize))
              | _ => (d, esize)
            (pure (d, esize, is_unsigned, m, rounding))) ) : SailM (Nat × Int × Bool × Nat × FPRounding) )
      let m := m
      let esize := esize
      let d := d
      (execute_aarch32_instrs_VCVT_iv_Op_A_txt d esize m rounding to_integer is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VCVT_iv_T1enc_A_txt (D : (BitVec 1)) (opc2 : (BitVec 3)) (Vd : (BitVec 4)) (size : (BitVec 2)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((opc2 != 0b000#3) && (! (let b__0 := opc2
             if (((Sail.BitVec.extractLsb b__0 2 1) == (0b10#2 : (BitVec 2))) : Bool)
             then true
             else false : Bool))) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (size == 0b01#2)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 16
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
      let rounding ← (( do (undefined_FPRounding ()) ) : SailM FPRounding )
      let to_integer : Bool := ((BitVec.join1 [(BitVec.access opc2 2)]) == 1#1)
      let (d, esize, is_unsigned, m, rounding) ← (( do
        if (to_integer : Bool)
        then
          (do
            let is_unsigned : Bool := ((BitVec.join1 [(BitVec.access opc2 0)]) == 0#1)
            let rounding ←
              if ((op == 1#1) : Bool)
              then (pure FPRounding_ZERO)
              else (FPRoundingMode (← (FPSCR_read ())))
            let d : Nat := (BitVec.toNat (Vd +++ D))
            let (esize, m) : (Int × Nat) :=
              match (size : BitVec 2) with
              | 0b01 =>
                (let esize : Nat := 16
                let m : Nat := (BitVec.toNat (Vm +++ M))
                (esize, m))
              | 0b10 =>
                (let esize : Nat := 32
                let m : Nat := (BitVec.toNat (Vm +++ M))
                (esize, m))
              | 0b11 =>
                (let esize : Nat := 64
                let m : Nat := (BitVec.toNat (M +++ Vm))
                (esize, m))
              | _ => (esize, m)
            (pure (d, esize, is_unsigned, m, rounding)))
        else
          (do
            let is_unsigned : Bool := (op == 0#1)
            let rounding ← (FPRoundingMode (← (FPSCR_read ())))
            let m : Nat := (BitVec.toNat (Vm +++ M))
            let (d, esize) : (Nat × Int) :=
              match (size : BitVec 2) with
              | 0b01 =>
                (let esize : Nat := 16
                let d : Nat := (BitVec.toNat (Vd +++ D))
                (d, esize))
              | 0b10 =>
                (let esize : Nat := 32
                let d : Nat := (BitVec.toNat (Vd +++ D))
                (d, esize))
              | 0b11 =>
                (let esize : Nat := 64
                let d : Nat := (BitVec.toNat (D +++ Vd))
                (d, esize))
              | _ => (d, esize)
            (pure (d, esize, is_unsigned, m, rounding))) ) : SailM (Nat × Int × Bool × Nat × FPRounding) )
      let m := m
      let esize := esize
      let d := d
      (execute_aarch32_instrs_VCVT_iv_Op_A_txt d esize m rounding to_integer is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VCVT_xs_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (op : (BitVec 2)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := imm6
         if (((Sail.BitVec.extractLsb b__0 5 3) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access op 1)]) == 0#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access op 1)]) == 0#1) && (let b__1 := imm6
           if (((Sail.BitVec.extractLsb b__1 5 4) == (0b10#2 : (BitVec 2))) : Bool)
           then true
           else false : Bool)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((let b__2 := imm6
         if (((Sail.BitVec.extractLsb b__2 5 5) == (0#1 : (BitVec 1))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let to_fixed : Bool := ((BitVec.join1 [(BitVec.access op 0)]) == 1#1)
      let frac_bits := (64 -i (BitVec.toNat imm6))
      let is_unsigned : Bool := (U == 1#1)
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match ((BitVec.join1 [(BitVec.access op 1)]) : BitVec 1) with
        | 0 =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
        | _ =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCVT_xs_Op_A_txt d elements esize frac_bits m regs to_fixed is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VCVT_xs_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (op : (BitVec 2)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := imm6
         if (((Sail.BitVec.extractLsb b__0 5 3) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access op 1)]) == 0#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access op 1)]) == 0#1) && (let b__1 := imm6
           if (((Sail.BitVec.extractLsb b__1 5 4) == (0b10#2 : (BitVec 2))) : Bool)
           then true
           else false : Bool)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((let b__2 := imm6
         if (((Sail.BitVec.extractLsb b__2 5 5) == (0#1 : (BitVec 1))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let to_fixed : Bool := ((BitVec.join1 [(BitVec.access op 0)]) == 1#1)
      let frac_bits := (64 -i (BitVec.toNat imm6))
      let is_unsigned : Bool := (U == 1#1)
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match ((BitVec.join1 [(BitVec.access op 1)]) : BitVec 1) with
        | 0 =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
        | _ =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VCVT_xs_Op_A_txt d elements esize frac_bits m regs to_fixed is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VCVT_xv_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (op : (BitVec 1)) (U : (BitVec 1)) (Vd : (BitVec 4)) (sf : (BitVec 2)) (sx : (BitVec 1)) (i : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:23359.29-23359.30"
      if (((sf == 0b00#2) || ((sf == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sf == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let to_fixed : Bool := (op == 1#1)
      let is_unsigned : Bool := (U == 1#1)
      let size :=
        if ((sx == 0#1) : Bool)
        then 16
        else 32
      let frac_bits := (size -i (BitVec.toNat (imm4 +++ i)))
      let fp_size : Nat := 16
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, fp_size) : (Nat × Int) :=
        match (sf : BitVec 2) with
        | 0b01 =>
          (let fp_size : Nat := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          (d, fp_size))
        | 0b10 =>
          (let fp_size : Nat := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          (d, fp_size))
        | 0b11 =>
          (let fp_size : Nat := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          (d, fp_size))
        | _ => (d, fp_size)
      let fp_size := fp_size
      let d := d
      if ((frac_bits <b 0) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let d := d
      (execute_aarch32_instrs_VCVT_xv_Op_A_txt d fp_size frac_bits size to_fixed is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VCVT_xv_T1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (U : (BitVec 1)) (Vd : (BitVec 4)) (sf : (BitVec 2)) (sx : (BitVec 1)) (i : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((sf == 0b00#2) || ((sf == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (sf == 0b01#2)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let to_fixed : Bool := (op == 1#1)
      let is_unsigned : Bool := (U == 1#1)
      let size :=
        if ((sx == 0#1) : Bool)
        then 16
        else 32
      let frac_bits := (size -i (BitVec.toNat (imm4 +++ i)))
      let fp_size : Nat := 16
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, fp_size) : (Nat × Int) :=
        match (sf : BitVec 2) with
        | 0b01 =>
          (let fp_size : Nat := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          (d, fp_size))
        | 0b10 =>
          (let fp_size : Nat := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          (d, fp_size))
        | 0b11 =>
          (let fp_size : Nat := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          (d, fp_size))
        | _ => (d, fp_size)
      let fp_size := fp_size
      let d := d
      if ((frac_bits <b 0) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let d := d
      (execute_aarch32_instrs_VCVT_xv_Op_A_txt d fp_size frac_bits size to_fixed is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VDIV_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:23491.29-23491.30"
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 16
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let n ← (( do (undefined_range 0 31) ) : SailM Nat )
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
        match (size : BitVec 2) with
        | 0b01 =>
          (let esize : Nat := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b10 =>
          (let esize : Nat := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b11 =>
          (let esize : Nat := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let n : Nat := (BitVec.toNat (N +++ Vn))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m, n))
        | _ => (d, esize, m, n)
      let n := n
      let m := m
      let esize := esize
      let d := d
      (execute_aarch32_instrs_VDIV_Op_A_txt d esize m n))
  else (pure ())

def decode_aarch32_instrs_VDIV_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((←((pure (size == 0b01#2)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 16
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let n ← (( do (undefined_range 0 31) ) : SailM Nat )
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
        match (size : BitVec 2) with
        | 0b01 =>
          (let esize : Nat := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b10 =>
          (let esize : Nat := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b11 =>
          (let esize : Nat := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let n : Nat := (BitVec.toNat (N +++ Vn))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m, n))
        | _ => (d, esize, m, n)
      let n := n
      let m := m
      let esize := esize
      let d := d
      (execute_aarch32_instrs_VDIV_Op_A_txt d esize m n))
  else (pure ())

def decode_aarch32_instrs_VDUP_r_A1enc_A_txt (cond : (BitVec 4)) (B : (BitVec 1)) (Q : (BitVec 1)) (Vd : (BitVec 4)) (Rt : (BitVec 4)) (D : (BitVec 1)) (E : (BitVec 1)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:23626.29-23626.30"
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let t := (BitVec.toNat Rt)
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      let esize : Nat := 8
      let elements : Nat := 2
      let (elements, esize) ← (( do
        match ((B +++ E) : BitVec 2) with
        | 0b00 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (pure (elements, esize)))
        | 0b01 =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (pure (elements, esize)))
        | 0b10 =>
          (let esize : Nat := 8
          let elements : Nat := 8
          (pure (elements, esize)))
        | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
      let esize := esize
      let elements := elements
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VDUP_r_Op_A_txt d elements esize regs t))
  else (pure ())

def decode_aarch32_instrs_VDUP_r_T1enc_A_txt (B : (BitVec 1)) (Q : (BitVec 1)) (Vd : (BitVec 4)) (Rt : (BitVec 4)) (D : (BitVec 1)) (E : (BitVec 1)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let t := (BitVec.toNat Rt)
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      let esize : Nat := 8
      let elements : Nat := 2
      let (elements, esize) ← (( do
        match ((B +++ E) : BitVec 2) with
        | 0b00 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (pure (elements, esize)))
        | 0b01 =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (pure (elements, esize)))
        | 0b10 =>
          (let esize : Nat := 8
          let elements : Nat := 8
          (pure (elements, esize)))
        | _ => sailThrow ((Error_Undefined ())) ) : SailM (Int × Int) )
      let esize := esize
      let elements := elements
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VDUP_r_Op_A_txt d elements esize regs t))
  else (pure ())

def decode_aarch32_instrs_VDUP_s_A1enc_A_txt (D : (BitVec 1)) (imm4 : (BitVec 4)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := imm4
         if (((Sail.BitVec.extractLsb b__0 2 0) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 2
      let index ← (( do (undefined_range 0 7) ) : SailM Nat )
      let (elements, esize, index) : (Int × Int × Nat) :=
        let b__1 := imm4
        let (elements, esize, index) : (Int × Int × Nat) :=
          if (((Sail.BitVec.extractLsb b__1 0 0) == (1#1 : (BitVec 1))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm4 3 1))
            (elements, esize, index))
          else
            (let (elements, esize, index) : (Int × Int × Nat) :=
              if (((Sail.BitVec.extractLsb b__1 1 0) == (0b10#2 : (BitVec 2))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm4 3 2))
                (elements, esize, index))
              else
                (let (elements, esize, index) : (Int × Int × Nat) :=
                  if (((Sail.BitVec.extractLsb b__1 2 0) == (0b100#3 : (BitVec 3))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let index : Nat := (BitVec.toNat (BitVec.join1 [(BitVec.access imm4 3)]))
                    (elements, esize, index))
                  else (elements, esize, index)
                (elements, esize, index))
            (elements, esize, index))
        (elements, esize, index)
      let index := index
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VDUP_s_Op_A_txt d elements esize index m regs))
  else (pure ())

def decode_aarch32_instrs_VDUP_s_T1enc_A_txt (D : (BitVec 1)) (imm4 : (BitVec 4)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := imm4
         if (((Sail.BitVec.extractLsb b__0 2 0) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 2
      let index ← (( do (undefined_range 0 7) ) : SailM Nat )
      let (elements, esize, index) : (Int × Int × Nat) :=
        let b__1 := imm4
        let (elements, esize, index) : (Int × Int × Nat) :=
          if (((Sail.BitVec.extractLsb b__1 0 0) == (1#1 : (BitVec 1))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm4 3 1))
            (elements, esize, index))
          else
            (let (elements, esize, index) : (Int × Int × Nat) :=
              if (((Sail.BitVec.extractLsb b__1 1 0) == (0b10#2 : (BitVec 2))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm4 3 2))
                (elements, esize, index))
              else
                (let (elements, esize, index) : (Int × Int × Nat) :=
                  if (((Sail.BitVec.extractLsb b__1 2 0) == (0b100#3 : (BitVec 3))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let index : Nat := (BitVec.toNat (BitVec.join1 [(BitVec.access imm4 3)]))
                    (elements, esize, index))
                  else (elements, esize, index)
                (elements, esize, index))
            (elements, esize, index))
        (elements, esize, index)
      let index := index
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VDUP_s_Op_A_txt d elements esize index m regs))
  else (pure ())

def decode_aarch32_instrs_VEOR_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VEOR_Op_A_txt d m n regs))
  else (pure ())

def decode_aarch32_instrs_VEOR_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VEOR_Op_A_txt d m n regs))
  else (pure ())

def decode_aarch32_instrs_VEXT_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (imm4 : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 0#1) && ((BitVec.join1 [(BitVec.access imm4 3)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let quadword_operation : Bool := (Q == 1#1)
      let position := (8 *i (BitVec.toNat imm4))
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VEXT_Op_A_txt d m n position quadword_operation))
  else (pure ())

def decode_aarch32_instrs_VEXT_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (imm4 : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 0#1) && ((BitVec.join1 [(BitVec.access imm4 3)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let quadword_operation : Bool := (Q == 1#1)
      let position := (8 *i (BitVec.toNat imm4))
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VEXT_Op_A_txt d m n position quadword_operation))
  else (pure ())

def decode_aarch32_instrs_VFMA_A1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let advsimd : Bool := true
      let op1_neg : Bool := (op == 1#1)
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VFMA_Op_A_txt advsimd d elements esize m n op1_neg regs))
  else (pure ())

def decode_aarch32_instrs_VFMA_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:24102.29-24102.30"
      let floating_point ← (( do (undefined_bool ()) ) : SailM Bool )
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let regs ← (( do (undefined_int ()) ) : SailM Int )
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let regs := regs
      let elements := elements
      let floating_point := floating_point
      let advsimd : Bool := false
      let op1_neg : Bool := (op == 1#1)
      let esize : Nat := 16
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let n ← (( do (undefined_range 0 31) ) : SailM Nat )
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
        match (size : BitVec 2) with
        | 0b01 =>
          (let esize : Nat := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b10 =>
          (let esize : Nat := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b11 =>
          (let esize : Nat := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let n : Nat := (BitVec.toNat (N +++ Vn))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m, n))
        | _ => (d, esize, m, n)
      let n := n
      let m := m
      let esize := esize
      let d := d
      (execute_aarch32_instrs_VFMA_Op_A_txt advsimd d elements esize m n op1_neg regs))
  else (pure ())

def decode_aarch32_instrs_VFMA_T1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (sz == 1#1)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let advsimd : Bool := true
      let op1_neg : Bool := (op == 1#1)
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VFMA_Op_A_txt advsimd d elements esize m n op1_neg regs))
  else (pure ())

def decode_aarch32_instrs_VFMA_T2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let floating_point ← (( do (undefined_bool ()) ) : SailM Bool )
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let regs ← (( do (undefined_int ()) ) : SailM Int )
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (size == 0b01#2)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let regs := regs
      let elements := elements
      let floating_point := floating_point
      let advsimd : Bool := false
      let op1_neg : Bool := (op == 1#1)
      let esize : Nat := 16
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let n ← (( do (undefined_range 0 31) ) : SailM Nat )
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
        match (size : BitVec 2) with
        | 0b01 =>
          (let esize : Nat := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b10 =>
          (let esize : Nat := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b11 =>
          (let esize : Nat := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let n : Nat := (BitVec.toNat (N +++ Vn))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m, n))
        | _ => (d, esize, m, n)
      let n := n
      let m := m
      let esize := esize
      let d := d
      (execute_aarch32_instrs_VFMA_Op_A_txt advsimd d elements esize m n op1_neg regs))
  else (pure ())

def decode_aarch32_instrs_VFNMA_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:24319.29-24319.30"
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let op1_neg : Bool := (op == 1#1)
      let esize : Nat := 16
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let n ← (( do (undefined_range 0 31) ) : SailM Nat )
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
        match (size : BitVec 2) with
        | 0b01 =>
          (let esize : Nat := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b10 =>
          (let esize : Nat := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b11 =>
          (let esize : Nat := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let n : Nat := (BitVec.toNat (N +++ Vn))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m, n))
        | _ => (d, esize, m, n)
      let n := n
      let m := m
      let esize := esize
      let d := d
      (execute_aarch32_instrs_VFNMA_Op_A_txt d esize m n op1_neg))
  else (pure ())

def decode_aarch32_instrs_VFNMA_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (size == 0b01#2)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let op1_neg : Bool := (op == 1#1)
      let esize : Nat := 16
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let n ← (( do (undefined_range 0 31) ) : SailM Nat )
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
        match (size : BitVec 2) with
        | 0b01 =>
          (let esize : Nat := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b10 =>
          (let esize : Nat := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b11 =>
          (let esize : Nat := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let n : Nat := (BitVec.toNat (N +++ Vn))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m, n))
        | _ => (d, esize, m, n)
      let n := n
      let m := m
      let esize := esize
      let d := d
      (execute_aarch32_instrs_VFNMA_Op_A_txt d esize m n op1_neg))
  else (pure ())

def decode_aarch32_instrs_VHADD_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let add : Bool := (op == 0#1)
      let is_unsigned : Bool := (U == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VHADD_Op_A_txt add d elements esize m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VHADD_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let add : Bool := (op == 0#1)
      let is_unsigned : Bool := (U == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VHADD_Op_A_txt add d elements esize m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VLD1_1_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD1 (single element to all lanes)")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access index_align 0)]) != 0#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := 1
      let index := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 1))
      let alignment := 1
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD1_1_Op_A_txt alignment d ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD1_1_A2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD1 (single element to all lanes)")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access index_align 1)]) != 0#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := 2
      let index := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 2))
      let alignment :=
        if (((BitVec.join1 [(BitVec.access index_align 0)]) == 0#1) : Bool)
        then 1
        else 2
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD1_1_Op_A_txt alignment d ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD1_1_A3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD1 (single element to all lanes)")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access index_align 2)]) != 0#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((Sail.BitVec.extractLsb index_align 1 0) != 0b00#2) && ((Sail.BitVec.extractLsb index_align 1 0) != 0b11#2)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := 4
      let index := (BitVec.toNat (BitVec.join1 [(BitVec.access index_align 3)]))
      let alignment :=
        if (((Sail.BitVec.extractLsb index_align 1 0) == 0b00#2) : Bool)
        then 1
        else 4
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD1_1_Op_A_txt alignment d ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD1_1_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD1 (single element to all lanes)")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access index_align 0)]) != 0#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := 1
      let index := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 1))
      let alignment := 1
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD1_1_Op_A_txt alignment d ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD1_1_T2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD1 (single element to all lanes)")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access index_align 1)]) != 0#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := 2
      let index := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 2))
      let alignment :=
        if (((BitVec.join1 [(BitVec.access index_align 0)]) == 0#1) : Bool)
        then 1
        else 2
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD1_1_Op_A_txt alignment d ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD1_1_T3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD1 (single element to all lanes)")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access index_align 2)]) != 0#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((Sail.BitVec.extractLsb index_align 1 0) != 0b00#2) && ((Sail.BitVec.extractLsb index_align 1 0) != 0b11#2)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := 4
      let index := (BitVec.toNat (BitVec.join1 [(BitVec.access index_align 3)]))
      let alignment :=
        if (((Sail.BitVec.extractLsb index_align 1 0) == 0b00#2) : Bool)
        then 1
        else 4
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD1_1_Op_A_txt alignment d ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD1_a_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (T : (BitVec 1)) (a : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) || ((size == 0b00#2) && (a == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let regs :=
        if ((T == 0#1) : Bool)
        then 1
        else 2
      let alignment :=
        if ((a == 0#1) : Bool)
        then 1
        else ebytes
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d +i regs) >b 32)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD1_a_Op_A_txt alignment d ebytes m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VLD1_a_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (T : (BitVec 1)) (a : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) || ((size == 0b00#2) && (a == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let regs :=
        if ((T == 0#1) : Bool)
        then 1
        else 2
      let alignment :=
        if ((a == 0#1) : Bool)
        then 1
        else ebytes
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d +i regs) >b 32)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD1_a_Op_A_txt alignment d ebytes m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VLD1_m_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let regs := 1
      if (((BitVec.join1 [(BitVec.access align 1)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let alignment :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let elements := (Int.ediv 8 ebytes)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      sail_assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:24951.173-24951.174"
      (execute_aarch32_instrs_VLD1_m_Op_A_txt alignment d ebytes elements m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VLD1_m_A2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let regs := 2
      if ((align == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let alignment :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let elements := (Int.ediv 8 ebytes)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d +i regs) >b 32)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      sail_assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:24988.173-24988.174"
      (execute_aarch32_instrs_VLD1_m_Op_A_txt alignment d ebytes elements m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VLD1_m_A3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let regs := 3
      if (((BitVec.join1 [(BitVec.access align 1)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let alignment :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let elements := (Int.ediv 8 ebytes)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d +i regs) >b 32)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      sail_assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:25025.173-25025.174"
      (execute_aarch32_instrs_VLD1_m_Op_A_txt alignment d ebytes elements m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VLD1_m_A4enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let regs := 4
      let alignment :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let elements := (Int.ediv 8 ebytes)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d +i regs) >b 32)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      sail_assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:25059.173-25059.174"
      (execute_aarch32_instrs_VLD1_m_Op_A_txt alignment d ebytes elements m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VLD1_m_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let regs := 1
      if (((BitVec.join1 [(BitVec.access align 1)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let alignment :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let elements := (Int.ediv 8 ebytes)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      sail_assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:25096.173-25096.174"
      (execute_aarch32_instrs_VLD1_m_Op_A_txt alignment d ebytes elements m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VLD1_m_T2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let regs := 2
      if ((align == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let alignment :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let elements := (Int.ediv 8 ebytes)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d +i regs) >b 32)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      sail_assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:25133.173-25133.174"
      (execute_aarch32_instrs_VLD1_m_Op_A_txt alignment d ebytes elements m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VLD1_m_T3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let regs := 3
      if (((BitVec.join1 [(BitVec.access align 1)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let alignment :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let elements := (Int.ediv 8 ebytes)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d +i regs) >b 32)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      sail_assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:25170.173-25170.174"
      (execute_aarch32_instrs_VLD1_m_Op_A_txt alignment d ebytes elements m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VLD1_m_T4enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let regs := 4
      let alignment :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let elements := (Int.ediv 8 ebytes)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d +i regs) >b 32)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      sail_assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:25204.173-25204.174"
      (execute_aarch32_instrs_VLD1_m_Op_A_txt alignment d ebytes elements m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VLD2_1_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD2 (single 2-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      let ebytes := 1
      let index := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 1))
      let inc_name := 1
      let alignment :=
        if (((BitVec.join1 [(BitVec.access index_align 0)]) == 0#1) : Bool)
        then 1
        else 2
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d2 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD2_1_Op_A_txt alignment d d2 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD2_1_A2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD2 (single 2-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      let ebytes := 2
      let index := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 2))
      let inc_name :=
        if (((BitVec.join1 [(BitVec.access index_align 1)]) == 0#1) : Bool)
        then 1
        else 2
      let alignment :=
        if (((BitVec.join1 [(BitVec.access index_align 0)]) == 0#1) : Bool)
        then 1
        else 4
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d2 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD2_1_Op_A_txt alignment d d2 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD2_1_A3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD2 (single 2-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access index_align 1)]) != 0#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := 4
      let index := (BitVec.toNat (BitVec.join1 [(BitVec.access index_align 3)]))
      let inc_name :=
        if (((BitVec.join1 [(BitVec.access index_align 2)]) == 0#1) : Bool)
        then 1
        else 2
      let alignment :=
        if (((BitVec.join1 [(BitVec.access index_align 0)]) == 0#1) : Bool)
        then 1
        else 8
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d2 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD2_1_Op_A_txt alignment d d2 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD2_1_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD2 (single 2-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      let ebytes := 1
      let index := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 1))
      let inc_name := 1
      let alignment :=
        if (((BitVec.join1 [(BitVec.access index_align 0)]) == 0#1) : Bool)
        then 1
        else 2
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d2 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD2_1_Op_A_txt alignment d d2 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD2_1_T2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD2 (single 2-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      let ebytes := 2
      let index := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 2))
      let inc_name :=
        if (((BitVec.join1 [(BitVec.access index_align 1)]) == 0#1) : Bool)
        then 1
        else 2
      let alignment :=
        if (((BitVec.join1 [(BitVec.access index_align 0)]) == 0#1) : Bool)
        then 1
        else 4
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d2 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD2_1_Op_A_txt alignment d d2 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD2_1_T3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD2 (single 2-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access index_align 1)]) != 0#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := 4
      let index := (BitVec.toNat (BitVec.join1 [(BitVec.access index_align 3)]))
      let inc_name :=
        if (((BitVec.join1 [(BitVec.access index_align 2)]) == 0#1) : Bool)
        then 1
        else 2
      let alignment :=
        if (((BitVec.join1 [(BitVec.access index_align 0)]) == 0#1) : Bool)
        then 1
        else 8
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d2 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD2_1_Op_A_txt alignment d d2 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD2_a_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (T : (BitVec 1)) (a : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let alignment :=
        if ((a == 0#1) : Bool)
        then 1
        else (2 *i ebytes)
      let inc_name :=
        if ((T == 0#1) : Bool)
        then 1
        else 2
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d2 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD2_a_Op_A_txt alignment d d2 ebytes m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD2_a_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (T : (BitVec 1)) (a : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let alignment :=
        if ((a == 0#1) : Bool)
        then 1
        else (2 *i ebytes)
      let inc_name :=
        if ((T == 0#1) : Bool)
        then 1
        else 2
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d2 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD2_a_Op_A_txt alignment d d2 ebytes m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD2_m_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let pairs := 1
      if ((align == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let inc_name :=
        if ((itype == 0b1001#4) : Bool)
        then 2
        else 1
      let alignment :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let elements := (Int.ediv 8 ebytes)
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d2 +i pairs) >b 32)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      sail_assert (((pairs == 1) || (pairs == 2)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:25627.168-25627.169"
      (execute_aarch32_instrs_VLD2_m_Op_A_txt alignment d d2 ebytes elements m n pairs register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD2_m_A2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let pairs := 2
      let inc_name := 2
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let alignment :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let elements := (Int.ediv 8 ebytes)
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d2 +i pairs) >b 32)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      sail_assert (((pairs == 1) || (pairs == 2)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:25666.168-25666.169"
      (execute_aarch32_instrs_VLD2_m_Op_A_txt alignment d d2 ebytes elements m n pairs register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD2_m_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let pairs := 1
      if ((align == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let inc_name :=
        if ((itype == 0b1001#4) : Bool)
        then 2
        else 1
      let alignment :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let elements := (Int.ediv 8 ebytes)
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d2 +i pairs) >b 32)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      sail_assert (((pairs == 1) || (pairs == 2)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:25708.168-25708.169"
      (execute_aarch32_instrs_VLD2_m_Op_A_txt alignment d d2 ebytes elements m n pairs register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD2_m_T2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let pairs := 2
      let inc_name := 2
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let alignment :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let elements := (Int.ediv 8 ebytes)
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || ((d2 +i pairs) >b 32)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      sail_assert (((pairs == 1) || (pairs == 2)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:25747.168-25747.169"
      (execute_aarch32_instrs_VLD2_m_Op_A_txt alignment d d2 ebytes elements m n pairs register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD3_1_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD3 (single 3-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access index_align 0)]) != 0#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := 1
      let index := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 1))
      let inc_name := 1
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d3 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD3_1_Op_A_txt d d2 d3 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD3_1_A2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD3 (single 3-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access index_align 0)]) != 0#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := 2
      let index := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 2))
      let inc_name :=
        if (((BitVec.join1 [(BitVec.access index_align 1)]) == 0#1) : Bool)
        then 1
        else 2
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d3 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD3_1_Op_A_txt d d2 d3 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD3_1_A3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD3 (single 3-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      if (((Sail.BitVec.extractLsb index_align 1 0) != 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := 4
      let index := (BitVec.toNat (BitVec.join1 [(BitVec.access index_align 3)]))
      let inc_name :=
        if (((BitVec.join1 [(BitVec.access index_align 2)]) == 0#1) : Bool)
        then 1
        else 2
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d3 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD3_1_Op_A_txt d d2 d3 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD3_1_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD3 (single 3-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access index_align 0)]) != 0#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := 1
      let index := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 1))
      let inc_name := 1
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d3 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD3_1_Op_A_txt d d2 d3 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD3_1_T2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD3 (single 3-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access index_align 0)]) != 0#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := 2
      let index := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 2))
      let inc_name :=
        if (((BitVec.join1 [(BitVec.access index_align 1)]) == 0#1) : Bool)
        then 1
        else 2
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d3 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD3_1_Op_A_txt d d2 d3 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD3_1_T3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD3 (single 3-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      if (((Sail.BitVec.extractLsb index_align 1 0) != 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := 4
      let index := (BitVec.toNat (BitVec.join1 [(BitVec.access index_align 3)]))
      let inc_name :=
        if (((BitVec.join1 [(BitVec.access index_align 2)]) == 0#1) : Bool)
        then 1
        else 2
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d3 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD3_1_Op_A_txt d d2 d3 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD3_a_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (T : (BitVec 1)) (a : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) || (a == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let inc_name :=
        if ((T == 0#1) : Bool)
        then 1
        else 2
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d3 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD3_a_Op_A_txt d d2 d3 ebytes m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD3_a_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (T : (BitVec 1)) (a : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) || (a == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let inc_name :=
        if ((T == 0#1) : Bool)
        then 1
        else 2
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d3 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD3_a_Op_A_txt d d2 d3 ebytes m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD3_m_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let inc_name : Nat := 1
      let inc_name ← (( do
        match (itype : BitVec 4) with
        | 0b0100 => (pure 1)
        | 0b0101 => (pure 2)
        | _ => sailThrow ((Error_See "Related encodings")) ) : SailM Int )
      let inc_name := inc_name
      if (((size == 0b11#2) || ((BitVec.join1 [(BitVec.access align 1)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let alignment :=
        if (((BitVec.join1 [(BitVec.access align 0)]) == 0#1) : Bool)
        then 1
        else 8
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let elements := (Int.ediv 8 ebytes)
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d3 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD3_m_Op_A_txt alignment d d2 d3 ebytes elements m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD3_m_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let inc_name : Nat := 1
      let inc_name ← (( do
        match (itype : BitVec 4) with
        | 0b0100 => (pure 1)
        | 0b0101 => (pure 2)
        | _ => sailThrow ((Error_See "Related encodings")) ) : SailM Int )
      let inc_name := inc_name
      if (((size == 0b11#2) || ((BitVec.join1 [(BitVec.access align 1)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let alignment :=
        if (((BitVec.join1 [(BitVec.access align 0)]) == 0#1) : Bool)
        then 1
        else 8
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let elements := (Int.ediv 8 ebytes)
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d3 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD3_m_Op_A_txt alignment d d2 d3 ebytes elements m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD4_1_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD4 (single 4-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      let ebytes := 1
      let index := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 1))
      let inc_name := 1
      let alignment :=
        if (((BitVec.join1 [(BitVec.access index_align 0)]) == 0#1) : Bool)
        then 1
        else 4
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let d4 := (d3 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD4_1_Op_A_txt alignment d d2 d3 d4 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD4_1_A2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD4 (single 4-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      let ebytes := 2
      let index := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 2))
      let inc_name :=
        if (((BitVec.join1 [(BitVec.access index_align 1)]) == 0#1) : Bool)
        then 1
        else 2
      let alignment :=
        if (((BitVec.join1 [(BitVec.access index_align 0)]) == 0#1) : Bool)
        then 1
        else 8
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let d4 := (d3 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD4_1_Op_A_txt alignment d d2 d3 d4 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD4_1_A3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD4 (single 4-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      if (((Sail.BitVec.extractLsb index_align 1 0) == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := 4
      let index := (BitVec.toNat (BitVec.join1 [(BitVec.access index_align 3)]))
      let inc_name :=
        if (((BitVec.join1 [(BitVec.access index_align 2)]) == 0#1) : Bool)
        then 1
        else 2
      let alignment :=
        if (((Sail.BitVec.extractLsb index_align 1 0) == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat (Sail.BitVec.extractLsb index_align 1 0)))
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let d4 := (d3 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      sail_assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) || (index == 4)) || (index == 5)) || (index == 6)) || (index == 7)) && ((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:26383.183-26383.184"
      (execute_aarch32_instrs_VLD4_1_Op_A_txt alignment d d2 d3 d4 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD4_1_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD4 (single 4-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      let ebytes := 1
      let index := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 1))
      let inc_name := 1
      let alignment :=
        if (((BitVec.join1 [(BitVec.access index_align 0)]) == 0#1) : Bool)
        then 1
        else 4
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let d4 := (d3 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD4_1_Op_A_txt alignment d d2 d3 d4 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD4_1_T2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD4 (single 4-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      let ebytes := 2
      let index := (BitVec.toNat (Sail.BitVec.extractLsb index_align 3 2))
      let inc_name :=
        if (((BitVec.join1 [(BitVec.access index_align 1)]) == 0#1) : Bool)
        then 1
        else 2
      let alignment :=
        if (((BitVec.join1 [(BitVec.access index_align 0)]) == 0#1) : Bool)
        then 1
        else 8
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let d4 := (d3 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLD4_1_Op_A_txt alignment d d2 d3 d4 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD4_1_T3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "VLD4 (single 4-element structure to all lanes)")) : SailM Unit)
      else (pure ())
      if (((Sail.BitVec.extractLsb index_align 1 0) == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes := 4
      let index := (BitVec.toNat (BitVec.join1 [(BitVec.access index_align 3)]))
      let inc_name :=
        if (((BitVec.join1 [(BitVec.access index_align 2)]) == 0#1) : Bool)
        then 1
        else 2
      let alignment :=
        if (((Sail.BitVec.extractLsb index_align 1 0) == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat (Sail.BitVec.extractLsb index_align 1 0)))
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let d4 := (d3 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      sail_assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) || (index == 4)) || (index == 5)) || (index == 6)) || (index == 7)) && ((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:26502.183-26502.184"
      (execute_aarch32_instrs_VLD4_1_Op_A_txt alignment d d2 d3 d4 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD4_a_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (T : (BitVec 1)) (a : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) && (a == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes : Nat := 1
      let alignment ← (( do (undefined_int ()) ) : SailM Int )
      let (alignment, ebytes) : (Int × Int) :=
        if ((size == 0b11#2) : Bool)
        then
          (let ebytes : Nat := 4
          let alignment : Int := 16
          (alignment, ebytes))
        else
          (let ebytes : Int := (Int.shiftl 1 (BitVec.toNat size))
          let alignment : Int :=
            if ((size == 0b10#2) : Bool)
            then
              (if ((a == 0#1) : Bool)
              then 1
              else 8)
            else
              (if ((a == 0#1) : Bool)
              then 1
              else (4 *i ebytes))
          (alignment, ebytes))
      let ebytes := ebytes
      let alignment := alignment
      let inc_name :=
        if ((T == 0#1) : Bool)
        then 1
        else 2
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let d4 := (d3 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let alignment := alignment
      sail_assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32))))))))) "src/instrs32.sail:26586.149-26586.150"
      (execute_aarch32_instrs_VLD4_a_Op_A_txt alignment d d2 d3 d4 ebytes m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD4_a_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (T : (BitVec 1)) (a : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) && (a == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let ebytes : Nat := 1
      let alignment ← (( do (undefined_int ()) ) : SailM Int )
      let (alignment, ebytes) : (Int × Int) :=
        if ((size == 0b11#2) : Bool)
        then
          (let ebytes : Nat := 4
          let alignment : Int := 16
          (alignment, ebytes))
        else
          (let ebytes : Int := (Int.shiftl 1 (BitVec.toNat size))
          let alignment : Int :=
            if ((size == 0b10#2) : Bool)
            then
              (if ((a == 0#1) : Bool)
              then 1
              else 8)
            else
              (if ((a == 0#1) : Bool)
              then 1
              else (4 *i ebytes))
          (alignment, ebytes))
      let ebytes := ebytes
      let alignment := alignment
      let inc_name :=
        if ((T == 0#1) : Bool)
        then 1
        else 2
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let d4 := (d3 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let alignment := alignment
      sail_assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32))))))))) "src/instrs32.sail:26639.149-26639.150"
      (execute_aarch32_instrs_VLD4_a_Op_A_txt alignment d d2 d3 d4 ebytes m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD4_m_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let inc_name : Nat := 1
      let inc_name ← (( do
        match (itype : BitVec 4) with
        | 0b0000 => (pure 1)
        | 0b0001 => (pure 2)
        | _ => sailThrow ((Error_See "Related encodings")) ) : SailM Int )
      let inc_name := inc_name
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let alignment :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let elements := (Int.ediv 8 ebytes)
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let d4 := (d3 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      sail_assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32))))))))) "src/instrs32.sail:26725.149-26725.150"
      (execute_aarch32_instrs_VLD4_m_Op_A_txt alignment d d2 d3 d4 ebytes elements m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLD4_m_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let inc_name : Nat := 1
      let inc_name ← (( do
        match (itype : BitVec 4) with
        | 0b0000 => (pure 1)
        | 0b0001 => (pure 2)
        | _ => sailThrow ((Error_See "Related encodings")) ) : SailM Int )
      let inc_name := inc_name
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let alignment :=
        if ((align == 0b00#2) : Bool)
        then 1
        else (Int.shiftl 4 (BitVec.toNat align))
      let ebytes := (Int.shiftl 1 (BitVec.toNat size))
      let elements := (Int.ediv 8 ebytes)
      let d := (BitVec.toNat (D +++ Vd))
      let d2 := (d +i inc_name)
      let d3 := (d2 +i inc_name)
      let d4 := (d3 +i inc_name)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let wback : Bool := (m != 15)
      let register_index : Bool := ((m != 15) && (m != 13))
      if (((n == 15) || (d4 >b 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      sail_assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32))))))))) "src/instrs32.sail:26777.149-26777.150"
      (execute_aarch32_instrs_VLD4_m_Op_A_txt alignment d d2 d3 d4 ebytes elements m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VLDM_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (D : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:26827.29-26827.30"
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((P == 1#1) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "VLDR")) : SailM Unit)
      else (pure ())
      if (((P == U) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let single_regs : Bool := false
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let regs := (Int.ediv (BitVec.toNat imm8) 2)
      if ((←((pure (n == 15)) <&&> (do
           (pure wback) <||> (do
             (pure (bne (← (CurrentInstrSet ())) InstrSet_A32)))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((((regs == 0) || (regs >b 16)) || ((d +i regs) >b 32)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access imm8 0)]) == 1#1) && ((d +i regs) >b 16)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLDM_Op_A_txt add d imm32 n regs single_regs wback))
  else (pure ())

def decode_aarch32_instrs_VLDM_A2enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (D : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:26875.29-26875.30"
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((P == 1#1) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "VLDR")) : SailM Unit)
      else (pure ())
      if (((P == U) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let single_regs : Bool := true
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      let d := (BitVec.toNat (Vd +++ D))
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let regs := (BitVec.toNat imm8)
      if ((←((pure (n == 15)) <&&> (do
           (pure wback) <||> (do
             (pure (bne (← (CurrentInstrSet ())) InstrSet_A32)))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((regs == 0) || ((d +i regs) >b 32)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLDM_Op_A_txt add d imm32 n regs single_regs wback))
  else (pure ())

def decode_aarch32_instrs_VLDM_T1enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (D : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((P == 1#1) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "VLDR")) : SailM Unit)
      else (pure ())
      if (((P == U) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let single_regs : Bool := false
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let regs := (Int.ediv (BitVec.toNat imm8) 2)
      if ((←((pure (n == 15)) <&&> (do
           (pure wback) <||> (do
             (pure (bne (← (CurrentInstrSet ())) InstrSet_A32)))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((((regs == 0) || (regs >b 16)) || ((d +i regs) >b 32)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access imm8 0)]) == 1#1) && ((d +i regs) >b 16)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLDM_Op_A_txt add d imm32 n regs single_regs wback))
  else (pure ())

def decode_aarch32_instrs_VLDM_T2enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (D : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((P == 1#1) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "VLDR")) : SailM Unit)
      else (pure ())
      if (((P == U) && (W == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let single_regs : Bool := true
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      let d := (BitVec.toNat (Vd +++ D))
      let n := (BitVec.toNat Rn)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let regs := (BitVec.toNat imm8)
      if ((←((pure (n == 15)) <&&> (do
           (pure wback) <||> (do
             (pure (bne (← (CurrentInstrSet ())) InstrSet_A32)))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((regs == 0) || ((d +i regs) >b 32)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VLDM_Op_A_txt add d imm32 n regs single_regs wback))
  else (pure ())

def decode_aarch32_instrs_VLDR_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:27036.29-27036.30"
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let add : Bool := (U == 1#1)
      let imm32 : (BitVec 32) :=
        if ((esize == 16) : Bool)
        then (Sail.BitVec.zeroExtend (imm8 +++ 0#1) 32)
        else (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let d : Nat :=
        match (size : BitVec 2) with
        | 0b01 => (BitVec.toNat (Vd +++ D))
        | 0b10 => (BitVec.toNat (Vd +++ D))
        | 0b11 => (BitVec.toNat (D +++ Vd))
        | _ => d
      let d := d
      let n := (BitVec.toNat Rn)
      (execute_aarch32_instrs_VLDR_Op_A_txt add d esize imm32 n))
  else (pure ())

def decode_aarch32_instrs_VLDR_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (size == 0b01#2)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let add : Bool := (U == 1#1)
      let imm32 : (BitVec 32) :=
        if ((esize == 16) : Bool)
        then (Sail.BitVec.zeroExtend (imm8 +++ 0#1) 32)
        else (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let d : Nat :=
        match (size : BitVec 2) with
        | 0b01 => (BitVec.toNat (Vd +++ D))
        | 0b10 => (BitVec.toNat (Vd +++ D))
        | 0b11 => (BitVec.toNat (D +++ Vd))
        | _ => d
      let d := d
      let n := (BitVec.toNat Rn)
      (execute_aarch32_instrs_VLDR_Op_A_txt add d esize imm32 n))
  else (pure ())

def decode_aarch32_instrs_VMAX_f_A1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let maximum : Bool := (op == 0#1)
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMAX_f_Op_A_txt d elements esize m maximum n regs))
  else (pure ())

def decode_aarch32_instrs_VMAX_f_T1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (sz == 1#1)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let maximum : Bool := (op == 0#1)
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMAX_f_Op_A_txt d elements esize m maximum n regs))
  else (pure ())

def decode_aarch32_instrs_VMAX_i_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (op : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let maximum : Bool := (op == 0#1)
      let is_unsigned : Bool := (U == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMAX_i_Op_A_txt d elements esize m maximum n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMAX_i_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (op : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let maximum : Bool := (op == 0#1)
      let is_unsigned : Bool := (U == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMAX_i_Op_A_txt d elements esize m maximum n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMLA_f_A1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let advsimd : Bool := true
      let add : Bool := (op == 0#1)
      let esize : Nat := 16
      let elements : Nat := 2
      let (elements, esize) : (Int × Int) :=
        match (sz : BitVec 1) with
        | 0 =>
          (let esize : Nat := 32
          let elements : Nat := 2
          (elements, esize))
        | _ =>
          (let esize : Nat := 16
          let elements : Nat := 4
          (elements, esize))
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMLA_f_Op_A_txt add advsimd d elements esize m n regs))
  else (pure ())


