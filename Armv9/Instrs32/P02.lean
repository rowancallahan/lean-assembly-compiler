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

def decode_aarch32_instrs_VMLA_f_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:27444.29-27444.30"
      let floating_point ← (( do (undefined_bool ()) ) : SailM Bool )
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let regs ← (( do (undefined_int ()) ) : SailM Int )
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let regs := regs
      let elements := elements
      let floating_point := floating_point
      let advsimd : Bool := false
      let add : Bool := (op == 0#1)
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
      (execute_aarch32_instrs_VMLA_f_Op_A_txt add advsimd d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VMLA_f_T1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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

def decode_aarch32_instrs_VMLA_f_T2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let floating_point ← (( do (undefined_bool ()) ) : SailM Bool )
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let regs ← (( do (undefined_int ()) ) : SailM Int )
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (size == 0b01#2)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let regs := regs
      let elements := elements
      let floating_point := floating_point
      let advsimd : Bool := false
      let add : Bool := (op == 0#1)
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
      (execute_aarch32_instrs_VMLA_f_Op_A_txt add advsimd d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VMLA_i_A1enc_A_txt (op : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let add : Bool := (op == 0#1)
      let long_destination : Bool := false
      let is_unsigned : Bool := false
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMLA_i_Op_A_txt add d elements esize long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMLA_i_A2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let add : Bool := (op == 0#1)
      let long_destination : Bool := true
      let is_unsigned : Bool := (U == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs := 1
      (execute_aarch32_instrs_VMLA_i_Op_A_txt add d elements esize long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMLA_i_T1enc_A_txt (op : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let add : Bool := (op == 0#1)
      let long_destination : Bool := false
      let is_unsigned : Bool := false
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMLA_i_Op_A_txt add d elements esize long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMLA_i_T2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let add : Bool := (op == 0#1)
      let long_destination : Bool := true
      let is_unsigned : Bool := (U == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs := 1
      (execute_aarch32_instrs_VMLA_i_Op_A_txt add d elements esize long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMLA_s_A1enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (F : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || (((F == 1#1) && (size == 0b01#2)) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := false
      let add : Bool := (op == 0#1)
      let floating_point : Bool := (F == 1#1)
      let long_destination : Bool := false
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      let esize : Nat := 16
      let elements : Nat := 2
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Nat := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Nat := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && (((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) && (((esize == 16) || (esize == 32)) && (((elements == 2) || (elements == 4)) && ((0 ≤b d) && (d ≤b 31)))))))))) "src/instrs32.sail:27879.175-27879.176"
      (execute_aarch32_instrs_VMLA_s_Op_A_txt add d elements esize floating_point index long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMLA_s_A2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let add : Bool := (op == 0#1)
      let floating_point : Bool := false
      let long_destination : Bool := true
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let regs := 1
      let esize : Nat := 16
      let elements : Nat := 2
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Nat := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Nat := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && (((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) && (((esize == 16) || (esize == 32)) && (((elements == 2) || (elements == 4)) && ((0 ≤b d) && (d ≤b 31)))))))))) "src/instrs32.sail:27937.175-27937.176"
      (execute_aarch32_instrs_VMLA_s_Op_A_txt add d elements esize floating_point index long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMLA_s_T1enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (F : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || (((F == 1#1) && (size == 0b01#2)) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((F == 1#1) && (size == 0b01#2))) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := false
      let add : Bool := (op == 0#1)
      let floating_point : Bool := (F == 1#1)
      let long_destination : Bool := false
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      let esize : Nat := 16
      let elements : Nat := 2
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Nat := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Nat := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && (((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) && (((esize == 16) || (esize == 32)) && (((elements == 2) || (elements == 4)) && ((0 ≤b d) && (d ≤b 31)))))))))) "src/instrs32.sail:28000.175-28000.176"
      (execute_aarch32_instrs_VMLA_s_Op_A_txt add d elements esize floating_point index long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMLA_s_T2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let add : Bool := (op == 0#1)
      let floating_point : Bool := false
      let long_destination : Bool := true
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let regs := 1
      let esize : Nat := 16
      let elements : Nat := 2
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Nat := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Nat := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && (((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) && (((esize == 16) || (esize == 32)) && (((elements == 2) || (elements == 4)) && ((0 ≤b d) && (d ≤b 31)))))))))) "src/instrs32.sail:28058.175-28058.176"
      (execute_aarch32_instrs_VMLA_s_Op_A_txt add d elements esize floating_point index long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMOVX_A1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (HaveFP16Ext ())) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (Vd +++ D))
      let m := (BitVec.toNat (Vm +++ M))
      (execute_aarch32_instrs_VMOVX_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_VMOVX_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (HaveFP16Ext ())) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (Vd +++ D))
      let m := (BitVec.toNat (Vm +++ M))
      (execute_aarch32_instrs_VMOVX_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_VINS_A1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (HaveFP16Ext ())) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (Vd +++ D))
      let m := (BitVec.toNat (Vm +++ M))
      (execute_aarch32_instrs_VINS_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_VINS_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (HaveFP16Ext ())) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (Vd +++ D))
      let m := (BitVec.toNat (Vm +++ M))
      (execute_aarch32_instrs_VINS_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_VMOV_d_A1enc_A_txt (cond : (BitVec 4)) (op : (BitVec 1)) (Rt2 : (BitVec 4)) (Rt : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:28225.29-28225.30"
      let to_arm_registers : Bool := (op == 1#1)
      let t := (BitVec.toNat Rt)
      let t2 := (BitVec.toNat Rt2)
      let m := (BitVec.toNat (M +++ Vm))
      if (((t == 15) || (t2 == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((to_arm_registers && (t == t2)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VMOV_d_Op_A_txt m t t2 to_arm_registers))
  else (pure ())

def decode_aarch32_instrs_VMOV_d_T1enc_A_txt (op : (BitVec 1)) (Rt2 : (BitVec 4)) (Rt : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let to_arm_registers : Bool := (op == 1#1)
      let t := (BitVec.toNat Rt)
      let t2 := (BitVec.toNat Rt2)
      let m := (BitVec.toNat (M +++ Vm))
      if (((t == 15) || (t2 == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((to_arm_registers && (t == t2)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VMOV_d_Op_A_txt m t t2 to_arm_registers))
  else (pure ())

def decode_aarch32_instrs_VMOV_i_A1enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (op : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      if ((((op == 0#1) && ((BitVec.join1 [(BitVec.access cmode 0)]) == 1#1)) && ((Sail.BitVec.extractLsb cmode 3 2) != 0b11#2)) : Bool)
      then (sailThrow ((Error_See "VORR (immediate)")) : SailM Unit)
      else (pure ())
      if (((op == 1#1) && (cmode != 0b1110#4)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let single_register : Bool := false
      let advsimd : Bool := true
      let imm64 ← (( do (AdvSIMDExpandImm op cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64) )
      let d := (BitVec.toNat (D +++ Vd))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd d imm32 imm64 regs single_register))
  else (pure ())

def decode_aarch32_instrs_VMOV_i_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (imm4H : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (imm4L : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:28338.29-28338.30"
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
      let single_register : Bool := (size != 0b11#2)
      let advsimd : Bool := false
      let imm16 ← (( do (undefined_bitvector 16) ) : SailM (BitVec 16) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let imm64 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let regs : Nat := 1
      let (d, imm32, imm64, regs) ← (( do
        match (size : BitVec 2) with
        | 0b01 =>
          (do
            let d : Nat := (BitVec.toNat (Vd +++ D))
            let imm16 ← (( do (VFPExpandImm (imm4H +++ imm4L) 16) ) : SailM (BitVec 16) )
            let imm32 : (BitVec 32) := ((Zeros (n := 16)) +++ imm16)
            (pure (d, imm32, imm64, regs)))
        | 0b10 =>
          (do
            let d : Nat := (BitVec.toNat (Vd +++ D))
            let imm32 ← (VFPExpandImm (imm4H +++ imm4L) 32)
            (pure (d, imm32, imm64, regs)))
        | 0b11 =>
          (do
            let d : Nat := (BitVec.toNat (D +++ Vd))
            let imm64 ← (VFPExpandImm (imm4H +++ imm4L) 64)
            let regs : Nat := 1
            (pure (d, imm32, imm64, regs)))
        | _ => (pure (d, imm32, imm64, regs)) ) : SailM (Nat × (BitVec 32) × (BitVec 64) × Int) )
      let regs := regs
      let d := d
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd d imm32 imm64 regs single_register))
  else (pure ())

def decode_aarch32_instrs_VMOV_i_A3enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (op : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      if ((((op == 0#1) && ((BitVec.join1 [(BitVec.access cmode 0)]) == 1#1)) && ((Sail.BitVec.extractLsb cmode 3 2) != 0b11#2)) : Bool)
      then (sailThrow ((Error_See "VORR (immediate)")) : SailM Unit)
      else (pure ())
      if (((op == 1#1) && (cmode != 0b1110#4)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let single_register : Bool := false
      let advsimd : Bool := true
      let imm64 ← (( do (AdvSIMDExpandImm op cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64) )
      let d := (BitVec.toNat (D +++ Vd))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd d imm32 imm64 regs single_register))
  else (pure ())

def decode_aarch32_instrs_VMOV_i_A4enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (op : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      if ((((op == 0#1) && ((BitVec.join1 [(BitVec.access cmode 0)]) == 1#1)) && ((Sail.BitVec.extractLsb cmode 3 2) != 0b11#2)) : Bool)
      then (sailThrow ((Error_See "VORR (immediate)")) : SailM Unit)
      else (pure ())
      if (((op == 1#1) && (cmode != 0b1110#4)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let single_register : Bool := false
      let advsimd : Bool := true
      let imm64 ← (( do (AdvSIMDExpandImm op cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64) )
      let d := (BitVec.toNat (D +++ Vd))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd d imm32 imm64 regs single_register))
  else (pure ())

def decode_aarch32_instrs_VMOV_i_A5enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (op : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      if ((((op == 0#1) && ((BitVec.join1 [(BitVec.access cmode 0)]) == 1#1)) && ((Sail.BitVec.extractLsb cmode 3 2) != 0b11#2)) : Bool)
      then (sailThrow ((Error_See "VORR (immediate)")) : SailM Unit)
      else (pure ())
      if (((op == 1#1) && (cmode != 0b1110#4)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let single_register : Bool := false
      let advsimd : Bool := true
      let imm64 ← (( do (AdvSIMDExpandImm op cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64) )
      let d := (BitVec.toNat (D +++ Vd))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd d imm32 imm64 regs single_register))
  else (pure ())

def decode_aarch32_instrs_VMOV_i_T1enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (op : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      if ((((op == 0#1) && ((BitVec.join1 [(BitVec.access cmode 0)]) == 1#1)) && ((Sail.BitVec.extractLsb cmode 3 2) != 0b11#2)) : Bool)
      then (sailThrow ((Error_See "VORR (immediate)")) : SailM Unit)
      else (pure ())
      if (((op == 1#1) && (cmode != 0b1110#4)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let single_register : Bool := false
      let advsimd : Bool := true
      let imm64 ← (( do (AdvSIMDExpandImm op cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64) )
      let d := (BitVec.toNat (D +++ Vd))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd d imm32 imm64 regs single_register))
  else (pure ())

def decode_aarch32_instrs_VMOV_i_T2enc_A_txt (D : (BitVec 1)) (imm4H : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (imm4L : (BitVec 4)) : SailM Unit := do
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
      let single_register : Bool := (size != 0b11#2)
      let advsimd : Bool := false
      let imm16 ← (( do (undefined_bitvector 16) ) : SailM (BitVec 16) )
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      let imm64 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let regs : Nat := 1
      let (d, imm32, imm64, regs) ← (( do
        match (size : BitVec 2) with
        | 0b01 =>
          (do
            let d : Nat := (BitVec.toNat (Vd +++ D))
            let imm16 ← (( do (VFPExpandImm (imm4H +++ imm4L) 16) ) : SailM (BitVec 16) )
            let imm32 : (BitVec 32) := ((Zeros (n := 16)) +++ imm16)
            (pure (d, imm32, imm64, regs)))
        | 0b10 =>
          (do
            let d : Nat := (BitVec.toNat (Vd +++ D))
            let imm32 ← (VFPExpandImm (imm4H +++ imm4L) 32)
            (pure (d, imm32, imm64, regs)))
        | 0b11 =>
          (do
            let d : Nat := (BitVec.toNat (D +++ Vd))
            let imm64 ← (VFPExpandImm (imm4H +++ imm4L) 64)
            let regs : Nat := 1
            (pure (d, imm32, imm64, regs)))
        | _ => (pure (d, imm32, imm64, regs)) ) : SailM (Nat × (BitVec 32) × (BitVec 64) × Int) )
      let regs := regs
      let d := d
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd d imm32 imm64 regs single_register))
  else (pure ())

def decode_aarch32_instrs_VMOV_i_T3enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (op : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      if ((((op == 0#1) && ((BitVec.join1 [(BitVec.access cmode 0)]) == 1#1)) && ((Sail.BitVec.extractLsb cmode 3 2) != 0b11#2)) : Bool)
      then (sailThrow ((Error_See "VORR (immediate)")) : SailM Unit)
      else (pure ())
      if (((op == 1#1) && (cmode != 0b1110#4)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let single_register : Bool := false
      let advsimd : Bool := true
      let imm64 ← (( do (AdvSIMDExpandImm op cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64) )
      let d := (BitVec.toNat (D +++ Vd))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd d imm32 imm64 regs single_register))
  else (pure ())

def decode_aarch32_instrs_VMOV_i_T4enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (op : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      if ((((op == 0#1) && ((BitVec.join1 [(BitVec.access cmode 0)]) == 1#1)) && ((Sail.BitVec.extractLsb cmode 3 2) != 0b11#2)) : Bool)
      then (sailThrow ((Error_See "VORR (immediate)")) : SailM Unit)
      else (pure ())
      if (((op == 1#1) && (cmode != 0b1110#4)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let single_register : Bool := false
      let advsimd : Bool := true
      let imm64 ← (( do (AdvSIMDExpandImm op cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64) )
      let d := (BitVec.toNat (D +++ Vd))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd d imm32 imm64 regs single_register))
  else (pure ())

def decode_aarch32_instrs_VMOV_i_T5enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (op : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
      if ((((op == 0#1) && ((BitVec.join1 [(BitVec.access cmode 0)]) == 1#1)) && ((Sail.BitVec.extractLsb cmode 3 2) != 0b11#2)) : Bool)
      then (sailThrow ((Error_See "VORR (immediate)")) : SailM Unit)
      else (pure ())
      if (((op == 1#1) && (cmode != 0b1110#4)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let imm32 := imm32
      let single_register : Bool := false
      let advsimd : Bool := true
      let imm64 ← (( do (AdvSIMDExpandImm op cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64) )
      let d := (BitVec.toNat (D +++ Vd))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMOV_i_Op_A_txt advsimd d imm32 imm64 regs single_register))
  else (pure ())

def decode_aarch32_instrs_VMOVL_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm3H : (BitVec 3)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((imm3H == 0b000#3) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if ((((imm3H != 0b001#3) && (imm3H != 0b010#3)) && (imm3H != 0b100#3)) : Bool)
      then (sailThrow ((Error_See "VSHLL")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (8 *i (BitVec.toNat imm3H))
      let is_unsigned : Bool := (U == 1#1)
      let elements := (fdiv_int 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VMOVL_Op_A_txt d elements esize m is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMOVL_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm3H : (BitVec 3)) (Vd : (BitVec 4)) (L : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((imm3H == 0b000#3) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if ((((imm3H != 0b001#3) && (imm3H != 0b010#3)) && (imm3H != 0b100#3)) : Bool)
      then (sailThrow ((Error_See "VSHLL")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (8 *i (BitVec.toNat imm3H))
      let is_unsigned : Bool := (U == 1#1)
      let elements := (fdiv_int 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VMOVL_Op_A_txt d elements esize m is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMOVN_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VMOVN_Op_A_txt d elements esize m))
  else (pure ())

def decode_aarch32_instrs_VMOVN_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VMOVN_Op_A_txt d elements esize m))
  else (pure ())

def decode_aarch32_instrs_VMOV_h_A1enc_A_txt (cond : (BitVec 4)) (op : (BitVec 1)) (Vn : (BitVec 4)) (Rt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:28889.29-28889.30"
      if ((! (HaveFP16Ext ())) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((cond != 0b1110#4) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let to_arm_register : Bool := (op == 1#1)
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat (Vn +++ N))
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VMOV_h_Op_A_txt n t to_arm_register))
  else (pure ())

def decode_aarch32_instrs_VMOV_h_T1enc_A_txt (op : (BitVec 1)) (Vn : (BitVec 4)) (Rt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (HaveFP16Ext ())) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let to_arm_register : Bool := (op == 1#1)
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat (Vn +++ N))
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VMOV_h_Op_A_txt n t to_arm_register))
  else (pure ())

def decode_aarch32_instrs_VMOV_r_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:28974.29-28974.30"
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let single_register : Bool := (size == 0b10#2)
      let advsimd : Bool := false
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let regs : Nat := 1
      let (d, m, regs) : (Nat × Nat × Int) :=
        if (single_register : Bool)
        then
          (let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, m, regs))
        else
          (let d : Nat := (BitVec.toNat (D +++ Vd))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          let regs : Nat := 1
          (d, m, regs))
      let regs := regs
      let m := m
      let d := d
      (execute_aarch32_instrs_VMOV_r_Op_A_txt advsimd d m regs single_register))
  else (pure ())

def decode_aarch32_instrs_VMOV_r_T2enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let single_register : Bool := (size == 0b10#2)
      let advsimd : Bool := false
      let d ← (( do (undefined_range 0 31) ) : SailM Nat )
      let m ← (( do (undefined_range 0 31) ) : SailM Nat )
      let regs : Nat := 1
      let (d, m, regs) : (Nat × Nat × Int) :=
        if (single_register : Bool)
        then
          (let d : Nat := (BitVec.toNat (Vd +++ D))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, m, regs))
        else
          (let d : Nat := (BitVec.toNat (D +++ Vd))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          let regs : Nat := 1
          (d, m, regs))
      let regs := regs
      let m := m
      let d := d
      (execute_aarch32_instrs_VMOV_r_Op_A_txt advsimd d m regs single_register))
  else (pure ())

def decode_aarch32_instrs_VMOV_rs_A1enc_A_txt (cond : (BitVec 4)) (opc1 : (BitVec 2)) (Vd : (BitVec 4)) (Rt : (BitVec 4)) (D : (BitVec 1)) (opc2 : (BitVec 2)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:29062.29-29062.30"
      let advsimd ← (( do (undefined_bool ()) ) : SailM Bool )
      let esize : Nat := 8
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (advsimd, esize, index) ← (( do
        let b__0 := (opc1 +++ opc2)
        let (advsimd, esize, index) ← (( do
          if (((Sail.BitVec.extractLsb b__0 3 3) == (1#1 : (BitVec 1))) : Bool)
          then
            (let advsimd : Bool := true
            let esize : Nat := 8
            let index : Int := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc1 0)]) +++ opc2))
            (pure (advsimd, esize, index)))
          else
            (do
              let (advsimd, esize, index) ← (( do
                if ((((Sail.BitVec.extractLsb b__0 3 3) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 0 0) == (1#1 : (BitVec 1)))) : Bool)
                then
                  (let advsimd : Bool := true
                  let esize : Nat := 16
                  let index : Int := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc1 0)]) +++ (BitVec.join1 [(BitVec.access opc2 1)])))
                  (pure (advsimd, esize, index)))
                else
                  (do
                    let (advsimd, esize, index) ← (( do
                      if ((((Sail.BitVec.extractLsb b__0 3 3) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
                      then
                        (let advsimd : Bool := false
                        let esize : Nat := 32
                        let index : Int := (BitVec.toNat (BitVec.join1 [(BitVec.access opc1 0)]))
                        (pure (advsimd, esize, index)))
                      else sailThrow ((Error_Undefined ())) ) : SailM (Bool × Int × Int) )
                    (pure (advsimd, esize, index))) ) : SailM (Bool × Int × Int) )
              (pure (advsimd, esize, index))) ) : SailM (Bool × Int × Int) )
        (pure (advsimd, esize, index)) ) : SailM (Bool × Int × Int) )
      let advsimd := advsimd
      let index := index
      let esize := esize
      let d := (BitVec.toNat (D +++ Vd))
      let t := (BitVec.toNat Rt)
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      match esize with
      | 8 => (execute_aarch32_instrs_VMOV_rs_Op_A_txt advsimd d 8 index t)
      | 16 => (execute_aarch32_instrs_VMOV_rs_Op_A_txt advsimd d 16 index t)
      | 32 => (execute_aarch32_instrs_VMOV_rs_Op_A_txt advsimd d 32 index t)
      | _ => sail_assert false "src/instrs32.sail:29105.26-29105.27")
  else (pure ())

def decode_aarch32_instrs_VMOV_rs_T1enc_A_txt (opc1 : (BitVec 2)) (Vd : (BitVec 4)) (Rt : (BitVec 4)) (D : (BitVec 1)) (opc2 : (BitVec 2)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let advsimd ← (( do (undefined_bool ()) ) : SailM Bool )
      let esize : Nat := 8
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (advsimd, esize, index) ← (( do
        let b__0 := (opc1 +++ opc2)
        let (advsimd, esize, index) ← (( do
          if (((Sail.BitVec.extractLsb b__0 3 3) == (1#1 : (BitVec 1))) : Bool)
          then
            (let advsimd : Bool := true
            let esize : Nat := 8
            let index : Int := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc1 0)]) +++ opc2))
            (pure (advsimd, esize, index)))
          else
            (do
              let (advsimd, esize, index) ← (( do
                if ((((Sail.BitVec.extractLsb b__0 3 3) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 0 0) == (1#1 : (BitVec 1)))) : Bool)
                then
                  (let advsimd : Bool := true
                  let esize : Nat := 16
                  let index : Int := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc1 0)]) +++ (BitVec.join1 [(BitVec.access opc2 1)])))
                  (pure (advsimd, esize, index)))
                else
                  (do
                    let (advsimd, esize, index) ← (( do
                      if ((((Sail.BitVec.extractLsb b__0 3 3) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
                      then
                        (let advsimd : Bool := false
                        let esize : Nat := 32
                        let index : Int := (BitVec.toNat (BitVec.join1 [(BitVec.access opc1 0)]))
                        (pure (advsimd, esize, index)))
                      else sailThrow ((Error_Undefined ())) ) : SailM (Bool × Int × Int) )
                    (pure (advsimd, esize, index))) ) : SailM (Bool × Int × Int) )
              (pure (advsimd, esize, index))) ) : SailM (Bool × Int × Int) )
        (pure (advsimd, esize, index)) ) : SailM (Bool × Int × Int) )
      let advsimd := advsimd
      let index := index
      let esize := esize
      let d := (BitVec.toNat (D +++ Vd))
      let t := (BitVec.toNat Rt)
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      match esize with
      | 8 => (execute_aarch32_instrs_VMOV_rs_Op_A_txt advsimd d 8 index t)
      | 16 => (execute_aarch32_instrs_VMOV_rs_Op_A_txt advsimd d 16 index t)
      | 32 => (execute_aarch32_instrs_VMOV_rs_Op_A_txt advsimd d 32 index t)
      | _ => sail_assert false "src/instrs32.sail:29173.26-29173.27")
  else (pure ())

def decode_aarch32_instrs_VMOV_s_A1enc_A_txt (cond : (BitVec 4)) (op : (BitVec 1)) (Vn : (BitVec 4)) (Rt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:29211.29-29211.30"
      let to_arm_register : Bool := (op == 1#1)
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat (Vn +++ N))
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VMOV_s_Op_A_txt n t to_arm_register))
  else (pure ())

def decode_aarch32_instrs_VMOV_s_T1enc_A_txt (op : (BitVec 1)) (Vn : (BitVec 4)) (Rt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let to_arm_register : Bool := (op == 1#1)
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat (Vn +++ N))
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VMOV_s_Op_A_txt n t to_arm_register))
  else (pure ())

def decode_aarch32_instrs_VMOV_sr_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (opc1 : (BitVec 2)) (Vn : (BitVec 4)) (Rt : (BitVec 4)) (N : (BitVec 1)) (opc2 : (BitVec 2)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:29282.29-29282.30"
      let advsimd ← (( do (undefined_bool ()) ) : SailM Bool )
      let esize : Nat := 8
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (advsimd, esize, index) ← (( do
        let b__0 := ((U +++ opc1) +++ opc2)
        let (advsimd, esize, index) ← (( do
          if (((Sail.BitVec.extractLsb b__0 3 3) == (1#1 : (BitVec 1))) : Bool)
          then
            (let advsimd : Bool := true
            let esize : Nat := 8
            let index : Int := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc1 0)]) +++ opc2))
            (pure (advsimd, esize, index)))
          else
            (do
              let (advsimd, esize, index) ← (( do
                if ((((Sail.BitVec.extractLsb b__0 3 3) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 0 0) == (1#1 : (BitVec 1)))) : Bool)
                then
                  (let advsimd : Bool := true
                  let esize : Nat := 16
                  let index : Int := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc1 0)]) +++ (BitVec.join1 [(BitVec.access opc2 1)])))
                  (pure (advsimd, esize, index)))
                else
                  (do
                    let (advsimd, esize, index) ← (( do
                      if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
                      then
                        (let advsimd : Bool := false
                        let esize : Nat := 32
                        let index : Int := (BitVec.toNat (BitVec.join1 [(BitVec.access opc1 0)]))
                        (pure (advsimd, esize, index)))
                      else
                        (do
                          if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)
                          (pure (advsimd, esize, index))) ) : SailM (Bool × Int × Int) )
                    (pure (advsimd, esize, index))) ) : SailM (Bool × Int × Int) )
              (pure (advsimd, esize, index))) ) : SailM (Bool × Int × Int) )
        (pure (advsimd, esize, index)) ) : SailM (Bool × Int × Int) )
      let advsimd := advsimd
      let index := index
      let esize := esize
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat (N +++ Vn))
      let is_unsigned : Bool := (U == 1#1)
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      match esize with
      | 8 => (execute_aarch32_instrs_VMOV_sr_Op_A_txt advsimd 8 index n t is_unsigned)
      | 16 => (execute_aarch32_instrs_VMOV_sr_Op_A_txt advsimd 16 index n t is_unsigned)
      | 32 => (execute_aarch32_instrs_VMOV_sr_Op_A_txt advsimd 32 index n t is_unsigned)
      | _ => sail_assert false "src/instrs32.sail:29329.26-29329.27")
  else (pure ())

def decode_aarch32_instrs_VMOV_sr_T1enc_A_txt (U : (BitVec 1)) (opc1 : (BitVec 2)) (Vn : (BitVec 4)) (Rt : (BitVec 4)) (N : (BitVec 1)) (opc2 : (BitVec 2)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let advsimd ← (( do (undefined_bool ()) ) : SailM Bool )
      let esize : Nat := 8
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (advsimd, esize, index) ← (( do
        let b__0 := ((U +++ opc1) +++ opc2)
        let (advsimd, esize, index) ← (( do
          if (((Sail.BitVec.extractLsb b__0 3 3) == (1#1 : (BitVec 1))) : Bool)
          then
            (let advsimd : Bool := true
            let esize : Nat := 8
            let index : Int := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc1 0)]) +++ opc2))
            (pure (advsimd, esize, index)))
          else
            (do
              let (advsimd, esize, index) ← (( do
                if ((((Sail.BitVec.extractLsb b__0 3 3) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 0 0) == (1#1 : (BitVec 1)))) : Bool)
                then
                  (let advsimd : Bool := true
                  let esize : Nat := 16
                  let index : Int := (BitVec.toNat ((BitVec.join1 [(BitVec.access opc1 0)]) +++ (BitVec.join1 [(BitVec.access opc2 1)])))
                  (pure (advsimd, esize, index)))
                else
                  (do
                    let (advsimd, esize, index) ← (( do
                      if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
                      then
                        (let advsimd : Bool := false
                        let esize : Nat := 32
                        let index : Int := (BitVec.toNat (BitVec.join1 [(BitVec.access opc1 0)]))
                        (pure (advsimd, esize, index)))
                      else
                        (do
                          if ((((Sail.BitVec.extractLsb b__0 4 3) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb b__0 1 0) == (0b00#2 : (BitVec 2)))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (sailThrow ((Error_Undefined ())) : SailM Unit)
                          (pure (advsimd, esize, index))) ) : SailM (Bool × Int × Int) )
                    (pure (advsimd, esize, index))) ) : SailM (Bool × Int × Int) )
              (pure (advsimd, esize, index))) ) : SailM (Bool × Int × Int) )
        (pure (advsimd, esize, index)) ) : SailM (Bool × Int × Int) )
      let advsimd := advsimd
      let index := index
      let esize := esize
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat (N +++ Vn))
      let is_unsigned : Bool := (U == 1#1)
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      match esize with
      | 8 => (execute_aarch32_instrs_VMOV_sr_Op_A_txt advsimd 8 index n t is_unsigned)
      | 16 => (execute_aarch32_instrs_VMOV_sr_Op_A_txt advsimd 16 index n t is_unsigned)
      | 32 => (execute_aarch32_instrs_VMOV_sr_Op_A_txt advsimd 32 index n t is_unsigned)
      | _ => sail_assert false "src/instrs32.sail:29402.26-29402.27")
  else (pure ())

def decode_aarch32_instrs_VMOV_ss_A1enc_A_txt (cond : (BitVec 4)) (op : (BitVec 1)) (Rt2 : (BitVec 4)) (Rt : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:29443.29-29443.30"
      let to_arm_registers : Bool := (op == 1#1)
      let t := (BitVec.toNat Rt)
      let t2 := (BitVec.toNat Rt2)
      let m := (BitVec.toNat (Vm +++ M))
      if ((((t == 15) || (t2 == 15)) || (m == 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((to_arm_registers && (t == t2)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VMOV_ss_Op_A_txt m t t2 to_arm_registers))
  else (pure ())

def decode_aarch32_instrs_VMOV_ss_T1enc_A_txt (op : (BitVec 1)) (Rt2 : (BitVec 4)) (Rt : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let to_arm_registers : Bool := (op == 1#1)
      let t := (BitVec.toNat Rt)
      let t2 := (BitVec.toNat Rt2)
      let m := (BitVec.toNat (Vm +++ M))
      if ((((t == 15) || (t2 == 15)) || (m == 31)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((to_arm_registers && (t == t2)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VMOV_ss_Op_A_txt m t t2 to_arm_registers))
  else (pure ())

def decode_aarch32_instrs_VMUL_f_A1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VMUL_f_Op_A_txt advsimd d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VMUL_f_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:29579.29-29579.30"
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
      (execute_aarch32_instrs_VMUL_f_Op_A_txt advsimd d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VMUL_f_T1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((←((pure (sz == 1#1)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
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
      (execute_aarch32_instrs_VMUL_f_Op_A_txt advsimd d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VMUL_f_T2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let floating_point ← (( do (undefined_bool ()) ) : SailM Bool )
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let regs ← (( do (undefined_int ()) ) : SailM Int )
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
      let regs := regs
      let elements := elements
      let floating_point := floating_point
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
      (execute_aarch32_instrs_VMUL_f_Op_A_txt advsimd d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VMUL_i_A1enc_A_txt (op : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) || ((op == 1#1) && (size != 0b00#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := false
      let polynomial : Bool := (op == 1#1)
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
      (execute_aarch32_instrs_VMUL_i_Op_A_txt d elements esize long_destination m n polynomial regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMUL_i_A2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let polynomial : Bool := (op == 1#1)
      let long_destination : Bool := true
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 esize)
      let (elements, esize) ← (( do
        if (polynomial : Bool)
        then
          (do
            if (((U == 1#1) || (size == 0b01#2)) : Bool)
            then (sailThrow ((Error_Undefined ())) : SailM Unit)
            else (pure ())
            let (elements, esize) ← (( do
              if ((size == 0b10#2) : Bool)
              then
                (do
                  if ((! (← (HaveBit128PMULLExt ()))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (pure ())
                  let esize : Nat := 64
                  let elements : Int := 1
                  (pure (elements, esize)))
              else (pure (elements, esize)) ) : SailM (Int × Int) )
            (pure (elements, esize)))
        else (pure (elements, esize)) ) : SailM (Int × Int) )
      let esize := esize
      let elements := elements
      if (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs := 1
      (execute_aarch32_instrs_VMUL_i_Op_A_txt d elements esize long_destination m n polynomial regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMUL_i_T1enc_A_txt (op : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) || ((op == 1#1) && (size != 0b00#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := false
      let polynomial : Bool := (op == 1#1)
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
      (execute_aarch32_instrs_VMUL_i_Op_A_txt d elements esize long_destination m n polynomial regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMUL_i_T2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let polynomial : Bool := (op == 1#1)
      let long_destination : Bool := true
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let elements : Int := (Int.ediv 64 esize)
      let (elements, esize) ← (( do
        if (polynomial : Bool)
        then
          (do
            if (((U == 1#1) || (size == 0b01#2)) : Bool)
            then (sailThrow ((Error_Undefined ())) : SailM Unit)
            else (pure ())
            let (elements, esize) ← (( do
              if ((size == 0b10#2) : Bool)
              then
                (do
                  if ((← (InITBlock ())) : Bool)
                  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
                  else (pure ())
                  if ((! (← (HaveBit128PMULLExt ()))) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else (pure ())
                  let esize : Nat := 64
                  let elements : Int := 1
                  (pure (elements, esize)))
              else (pure (elements, esize)) ) : SailM (Int × Int) )
            (pure (elements, esize)))
        else (pure (elements, esize)) ) : SailM (Int × Int) )
      let esize := esize
      let elements := elements
      if (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs := 1
      (execute_aarch32_instrs_VMUL_i_Op_A_txt d elements esize long_destination m n polynomial regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMUL_s_A1enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (F : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || (((F == 1#1) && (size == 0b01#2)) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := false
      let floating_point : Bool := (F == 1#1)
      let long_destination : Bool := false
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      let esize : Nat := 16
      let elements : Nat := 2
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Nat := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Nat := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && (((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) && (((esize == 16) || (esize == 32)) && (((elements == 2) || (elements == 4)) && ((0 ≤b d) && (d ≤b 31)))))))))) "src/instrs32.sail:30043.175-30043.176"
      (execute_aarch32_instrs_VMUL_s_Op_A_txt d elements esize floating_point index long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMUL_s_A2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let long_destination : Bool := true
      let floating_point : Bool := false
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let regs := 1
      let esize : Nat := 16
      let elements : Nat := 2
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Nat := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Nat := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && (((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) && (((esize == 16) || (esize == 32)) && (((elements == 2) || (elements == 4)) && ((0 ≤b d) && (d ≤b 31)))))))))) "src/instrs32.sail:30099.175-30099.176"
      (execute_aarch32_instrs_VMUL_s_Op_A_txt d elements esize floating_point index long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMUL_s_T1enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (F : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if ((←((pure ((F == 1#1) && (size == 0b01#2))) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || (((F == 1#1) && (size == 0b01#2)) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := false
      let floating_point : Bool := (F == 1#1)
      let long_destination : Bool := false
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      let esize : Nat := 16
      let elements : Nat := 2
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Nat := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Nat := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && (((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) && (((esize == 16) || (esize == 32)) && (((elements == 2) || (elements == 4)) && ((0 ≤b d) && (d ≤b 31)))))))))) "src/instrs32.sail:30160.175-30160.176"
      (execute_aarch32_instrs_VMUL_s_Op_A_txt d elements esize floating_point index long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMUL_s_T2enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let long_destination : Bool := true
      let floating_point : Bool := false
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let regs := 1
      let esize : Nat := 16
      let elements : Nat := 2
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Nat := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Nat := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && (((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) && (((esize == 16) || (esize == 32)) && (((elements == 2) || (elements == 4)) && ((0 ≤b d) && (d ≤b 31)))))))))) "src/instrs32.sail:30216.175-30216.176"
      (execute_aarch32_instrs_VMUL_s_Op_A_txt d elements esize floating_point index long_destination m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VMVN_i_A1enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((((BitVec.join1 [(BitVec.access cmode 0)]) == 1#1) && ((Sail.BitVec.extractLsb cmode 3 2) != 0b11#2)) || ((Sail.BitVec.extractLsb cmode 3 1) == 0b111#3)) : Bool)
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
      (execute_aarch32_instrs_VMVN_i_Op_A_txt d imm64 regs))
  else (pure ())

def decode_aarch32_instrs_VMVN_i_A2enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((((BitVec.join1 [(BitVec.access cmode 0)]) == 1#1) && ((Sail.BitVec.extractLsb cmode 3 2) != 0b11#2)) || ((Sail.BitVec.extractLsb cmode 3 1) == 0b111#3)) : Bool)
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
      (execute_aarch32_instrs_VMVN_i_Op_A_txt d imm64 regs))
  else (pure ())

def decode_aarch32_instrs_VMVN_i_A3enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((((BitVec.join1 [(BitVec.access cmode 0)]) == 1#1) && ((Sail.BitVec.extractLsb cmode 3 2) != 0b11#2)) || ((Sail.BitVec.extractLsb cmode 3 1) == 0b111#3)) : Bool)
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
      (execute_aarch32_instrs_VMVN_i_Op_A_txt d imm64 regs))
  else (pure ())

def decode_aarch32_instrs_VMVN_i_T1enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((((BitVec.join1 [(BitVec.access cmode 0)]) == 1#1) && ((Sail.BitVec.extractLsb cmode 3 2) != 0b11#2)) || ((Sail.BitVec.extractLsb cmode 3 1) == 0b111#3)) : Bool)
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
      (execute_aarch32_instrs_VMVN_i_Op_A_txt d imm64 regs))
  else (pure ())

def decode_aarch32_instrs_VMVN_i_T2enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((((BitVec.join1 [(BitVec.access cmode 0)]) == 1#1) && ((Sail.BitVec.extractLsb cmode 3 2) != 0b11#2)) || ((Sail.BitVec.extractLsb cmode 3 1) == 0b111#3)) : Bool)
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
      (execute_aarch32_instrs_VMVN_i_Op_A_txt d imm64 regs))
  else (pure ())

def decode_aarch32_instrs_VMVN_i_T3enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((((BitVec.join1 [(BitVec.access cmode 0)]) == 1#1) && ((Sail.BitVec.extractLsb cmode 3 2) != 0b11#2)) || ((Sail.BitVec.extractLsb cmode 3 1) == 0b111#3)) : Bool)
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
      (execute_aarch32_instrs_VMVN_i_Op_A_txt d imm64 regs))
  else (pure ())

def decode_aarch32_instrs_VMVN_r_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size != 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMVN_r_Op_A_txt d m regs))
  else (pure ())

def decode_aarch32_instrs_VMVN_r_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size != 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VMVN_r_Op_A_txt d m regs))
  else (pure ())

def decode_aarch32_instrs_VNEG_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VNEG_Op_A_txt advsimd d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VNEG_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:30572.29-30572.30"
      let floating_point ← (( do (undefined_bool ()) ) : SailM Bool )
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let regs ← (( do (undefined_int ()) ) : SailM Int )
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VNEG_Op_A_txt advsimd d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VNEG_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VNEG_Op_A_txt advsimd d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VNEG_T2enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let floating_point ← (( do (undefined_bool ()) ) : SailM Bool )
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let regs ← (( do (undefined_int ()) ) : SailM Int )
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (size == 0b01#2)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VNEG_Op_A_txt advsimd d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VNMLA_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:30788.29-30788.30"
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
      let vtype : VFPNegMul :=
        if ((op == 1#1) : Bool)
        then VFPNegMul_VNMLA
        else VFPNegMul_VNMLS
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
      (execute_aarch32_instrs_VNMLA_Op_A_txt d esize m n vtype))
  else (pure ())

def decode_aarch32_instrs_VNMLA_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:30852.29-30852.30"
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let vtype : VFPNegMul := VFPNegMul_VNMUL
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
      (execute_aarch32_instrs_VNMLA_Op_A_txt d esize m n vtype))
  else (pure ())

def decode_aarch32_instrs_VNMLA_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      let vtype : VFPNegMul :=
        if ((op == 1#1) : Bool)
        then VFPNegMul_VNMLA
        else VFPNegMul_VNMLS
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
      (execute_aarch32_instrs_VNMLA_Op_A_txt d esize m n vtype))
  else (pure ())

def decode_aarch32_instrs_VNMLA_T2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (! (HaveFP16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (size == 0b01#2)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let vtype : VFPNegMul := VFPNegMul_VNMUL
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
      (execute_aarch32_instrs_VNMLA_Op_A_txt d esize m n vtype))
  else (pure ())

def decode_aarch32_instrs_VORN_r_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VORN_r_Op_A_txt d m n regs))
  else (pure ())

def decode_aarch32_instrs_VORN_r_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VORN_r_Op_A_txt d m n regs))
  else (pure ())

def decode_aarch32_instrs_VORR_i_A1enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((BitVec.join1 [(BitVec.access cmode 0)]) == 0#1) || ((Sail.BitVec.extractLsb cmode 3 2) == 0b11#2)) : Bool)
      then (sailThrow ((Error_See "VMOV (immediate)")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let imm64 ← (( do (AdvSIMDExpandImm 0#1 cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64) )
      let d := (BitVec.toNat (D +++ Vd))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VORR_i_Op_A_txt d imm64 regs))
  else (pure ())

def decode_aarch32_instrs_VORR_i_A2enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((BitVec.join1 [(BitVec.access cmode 0)]) == 0#1) || ((Sail.BitVec.extractLsb cmode 3 2) == 0b11#2)) : Bool)
      then (sailThrow ((Error_See "VMOV (immediate)")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let imm64 ← (( do (AdvSIMDExpandImm 0#1 cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64) )
      let d := (BitVec.toNat (D +++ Vd))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VORR_i_Op_A_txt d imm64 regs))
  else (pure ())

def decode_aarch32_instrs_VORR_i_T1enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((BitVec.join1 [(BitVec.access cmode 0)]) == 0#1) || ((Sail.BitVec.extractLsb cmode 3 2) == 0b11#2)) : Bool)
      then (sailThrow ((Error_See "VMOV (immediate)")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let imm64 ← (( do (AdvSIMDExpandImm 0#1 cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64) )
      let d := (BitVec.toNat (D +++ Vd))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VORR_i_Op_A_txt d imm64 regs))
  else (pure ())

def decode_aarch32_instrs_VORR_i_T2enc_A_txt (i : (BitVec 1)) (D : (BitVec 1)) (imm3 : (BitVec 3)) (Vd : (BitVec 4)) (cmode : (BitVec 4)) (Q : (BitVec 1)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((BitVec.join1 [(BitVec.access cmode 0)]) == 0#1) || ((Sail.BitVec.extractLsb cmode 3 2) == 0b11#2)) : Bool)
      then (sailThrow ((Error_See "VMOV (immediate)")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let imm64 ← (( do (AdvSIMDExpandImm 0#1 cmode ((i +++ imm3) +++ imm4)) ) : SailM (BitVec 64) )
      let d := (BitVec.toNat (D +++ Vd))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VORR_i_Op_A_txt d imm64 regs))
  else (pure ())

def decode_aarch32_instrs_VORR_r_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VORR_r_Op_A_txt d m n regs))
  else (pure ())

def decode_aarch32_instrs_VORR_r_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VORR_r_Op_A_txt d m n regs))
  else (pure ())

def decode_aarch32_instrs_VPADAL_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (op == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VPADAL_Op_A_txt d elements esize m regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VPADAL_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (op == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VPADAL_Op_A_txt d elements esize m regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VPADD_f_A1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Q == 1#1) : Bool)
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
      (execute_aarch32_instrs_VPADD_f_Op_A_txt d elements esize m n))
  else (pure ())

def decode_aarch32_instrs_VPADD_f_T1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((Q == 1#1) : Bool)
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
      (execute_aarch32_instrs_VPADD_f_Op_A_txt d elements esize m n))
  else (pure ())

def decode_aarch32_instrs_VPADD_i_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) || (Q == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VPADD_i_Op_A_txt d elements esize m n))
  else (pure ())

def decode_aarch32_instrs_VPADD_i_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) || (Q == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VPADD_i_Op_A_txt d elements esize m n))
  else (pure ())

def decode_aarch32_instrs_VPADDL_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (op == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VPADDL_Op_A_txt d elements esize m regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VPADDL_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (op == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VPADDL_Op_A_txt d elements esize m regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VPMAX_f_A1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
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
      (execute_aarch32_instrs_VPMAX_f_Op_A_txt d elements esize m maximum n))
  else (pure ())

def decode_aarch32_instrs_VPMAX_f_T1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
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
      (execute_aarch32_instrs_VPMAX_f_Op_A_txt d elements esize m maximum n))
  else (pure ())

def decode_aarch32_instrs_VPMAX_i_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (op : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
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
      (execute_aarch32_instrs_VPMAX_i_Op_A_txt d elements esize m maximum n is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VPMAX_i_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (op : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
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
      (execute_aarch32_instrs_VPMAX_i_Op_A_txt d elements esize m maximum n is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VQABS_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VQABS_Op_A_txt d elements esize m regs))
  else (pure ())

def decode_aarch32_instrs_VQABS_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VQABS_Op_A_txt d elements esize m regs))
  else (pure ())

def decode_aarch32_instrs_VQADD_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
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
      (execute_aarch32_instrs_VQADD_Op_A_txt d elements esize m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VQADD_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
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
      (execute_aarch32_instrs_VQADD_Op_A_txt d elements esize m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VQDMLAL_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let index ← (( do (undefined_int ()) ) : SailM Int )
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let index := index
      let add : Bool := (op == 0#1)
      let scalar_form : Bool := false
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      (execute_aarch32_instrs_VQDMLAL_Op_A_txt add d elements esize index m n scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQDMLAL_A2enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let add : Bool := (op == 0#1)
      let scalar_form : Bool := true
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let esize : Nat := 8
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Int := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Int := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31))))))) "src/instrs32.sail:32155.117-32155.118"
      (execute_aarch32_instrs_VQDMLAL_Op_A_txt add d elements esize index m n scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQDMLAL_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let index ← (( do (undefined_int ()) ) : SailM Int )
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let index := index
      let add : Bool := (op == 0#1)
      let scalar_form : Bool := false
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      (execute_aarch32_instrs_VQDMLAL_Op_A_txt add d elements esize index m n scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQDMLAL_T2enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let add : Bool := (op == 0#1)
      let scalar_form : Bool := true
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let esize : Nat := 8
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Int := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Int := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31))))))) "src/instrs32.sail:32245.117-32245.118"
      (execute_aarch32_instrs_VQDMLAL_Op_A_txt add d elements esize index m n scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQDMLSL_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let index ← (( do (undefined_int ()) ) : SailM Int )
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let index := index
      let add : Bool := (op == 0#1)
      let scalar_form : Bool := false
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      (execute_aarch32_instrs_VQDMLSL_Op_A_txt add d elements esize index m n scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQDMLSL_A2enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let add : Bool := (op == 0#1)
      let scalar_form : Bool := true
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let esize : Nat := 8
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Int := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Int := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31))))))) "src/instrs32.sail:32377.117-32377.118"
      (execute_aarch32_instrs_VQDMLSL_Op_A_txt add d elements esize index m n scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQDMLSL_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let index ← (( do (undefined_int ()) ) : SailM Int )
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let index := index
      let add : Bool := (op == 0#1)
      let scalar_form : Bool := false
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      (execute_aarch32_instrs_VQDMLSL_Op_A_txt add d elements esize index m n scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQDMLSL_T2enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let add : Bool := (op == 0#1)
      let scalar_form : Bool := true
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let esize : Nat := 8
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Int := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Int := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31))))))) "src/instrs32.sail:32467.117-32467.118"
      (execute_aarch32_instrs_VQDMLSL_Op_A_txt add d elements esize index m n scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQDMULH_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let index ← (( do (undefined_int ()) ) : SailM Int )
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let index := index
      let scalar_form : Bool := false
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VQDMULH_Op_A_txt d elements esize index m n regs scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQDMULH_A2enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if ((size == 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let scalar_form : Bool := true
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      let esize : Nat := 8
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Int := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Int := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31)))))))) "src/instrs32.sail:32590.135-32590.136"
      (execute_aarch32_instrs_VQDMULH_Op_A_txt d elements esize index m n regs scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQDMULH_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let index ← (( do (undefined_int ()) ) : SailM Int )
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let index := index
      let scalar_form : Bool := false
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VQDMULH_Op_A_txt d elements esize index m n regs scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQDMULH_T2enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if ((size == 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let scalar_form : Bool := true
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      let esize : Nat := 8
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Int := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Int := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31)))))))) "src/instrs32.sail:32683.135-32683.136"
      (execute_aarch32_instrs_VQDMULH_Op_A_txt d elements esize index m n regs scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQDMULL_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let index ← (( do (undefined_int ()) ) : SailM Int )
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let index := index
      let scalar_form : Bool := false
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      (execute_aarch32_instrs_VQDMULL_Op_A_txt d elements esize index m n scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQDMULL_A2enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let scalar_form : Bool := true
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let esize : Nat := 8
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Int := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Int := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31))))))) "src/instrs32.sail:32798.117-32798.118"
      (execute_aarch32_instrs_VQDMULL_Op_A_txt d elements esize index m n scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQDMULL_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let index ← (( do (undefined_int ()) ) : SailM Int )
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let index := index
      let scalar_form : Bool := false
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      (execute_aarch32_instrs_VQDMULL_Op_A_txt d elements esize index m n scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQDMULL_T2enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let scalar_form : Bool := true
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let esize : Nat := 8
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Int := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Int := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31))))))) "src/instrs32.sail:32884.117-32884.118"
      (execute_aarch32_instrs_VQDMULL_Op_A_txt d elements esize index m n scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQMOVN_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((op == 0b00#2) : Bool)
      then (sailThrow ((Error_See "VMOVN")) : SailM Unit)
      else (pure ())
      if (((size == 0b11#2) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let src_unsigned : Bool := (op == 0b11#2)
      let dest_unsigned : Bool := ((BitVec.join1 [(BitVec.access op 0)]) == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VQMOVN_Op_A_txt d dest_unsigned elements esize m src_unsigned))
  else (pure ())

def decode_aarch32_instrs_VQMOVN_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((op == 0b00#2) : Bool)
      then (sailThrow ((Error_See "VMOVN")) : SailM Unit)
      else (pure ())
      if (((size == 0b11#2) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let src_unsigned : Bool := (op == 0b11#2)
      let dest_unsigned : Bool := ((BitVec.join1 [(BitVec.access op 0)]) == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VQMOVN_Op_A_txt d dest_unsigned elements esize m src_unsigned))
  else (pure ())

def decode_aarch32_instrs_VQNEG_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VQNEG_Op_A_txt d elements esize m regs))
  else (pure ())

def decode_aarch32_instrs_VQNEG_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VQNEG_Op_A_txt d elements esize m regs))
  else (pure ())

def decode_aarch32_instrs_VQRDMULH_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let index ← (( do (undefined_int ()) ) : SailM Int )
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let index := index
      let scalar_form : Bool := false
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VQRDMULH_Op_A_txt d elements esize index m n regs scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQRDMULH_A2enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if ((size == 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let scalar_form : Bool := true
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      let esize : Nat := 8
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Int := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Int := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31)))))))) "src/instrs32.sail:33186.135-33186.136"
      (execute_aarch32_instrs_VQRDMULH_Op_A_txt d elements esize index m n regs scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQRDMULH_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let index ← (( do (undefined_int ()) ) : SailM Int )
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let index := index
      let scalar_form : Bool := false
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VQRDMULH_Op_A_txt d elements esize index m n regs scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQRDMULH_T2enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if ((size == 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let scalar_form : Bool := true
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      let esize : Nat := 8
      let elements ← (( do (undefined_int ()) ) : SailM Int )
      let m ← (( do (undefined_int ()) ) : SailM Int )
      let index ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b01#2) : Bool)
        then
          (let esize : Nat := 16
          let elements : Int := 4
          let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
          let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let (elements, esize, index, m) : (Int × Int × Int × Int) :=
        if ((size == 0b10#2) : Bool)
        then
          (let esize : Nat := 32
          let elements : Int := 2
          let m : Int := (BitVec.toNat Vm)
          let index : Int := (BitVec.toNat M)
          (elements, esize, index, m))
        else (elements, esize, index, m)
      let m := m
      let index := index
      let esize := esize
      let elements := elements
      sail_assert (((regs == 1) || (regs == 2)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && (d ≤b 31)))))))) "src/instrs32.sail:33279.135-33279.136"
      (execute_aarch32_instrs_VQRDMULH_Op_A_txt d elements esize index m n regs scalar_form))
  else (pure ())

def decode_aarch32_instrs_VQRDMLAH_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let index ← (( do (undefined_int ()) ) : SailM Int )
  if ((! (← (HaveQRDMLAHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let index := index
  let add : Bool := true
  let scalar_form : Bool := false
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv 64 esize)
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let regs :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VQRDMLAH_Op_A_txt d elements esize index m n regs scalar_form)

def decode_aarch32_instrs_VQRDMLAH_A2enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveQRDMLAHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let add : Bool := true
  let scalar_form : Bool := true
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let regs :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  let esize : Nat := 8
  let elements ← (( do (undefined_int ()) ) : SailM Int )
  let m ← (( do (undefined_int ()) ) : SailM Int )
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (elements, esize, index, m) : (Int × Int × Int × Int) :=
    if ((size == 0b01#2) : Bool)
    then
      (let esize : Nat := 16
      let elements : Int := 4
      let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
      let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
      (elements, esize, index, m))
    else (elements, esize, index, m)
  let (elements, esize, index, m) : (Int × Int × Int × Int) :=
    if ((size == 0b10#2) : Bool)
    then
      (let esize : Nat := 32
      let elements : Int := 2
      let m : Int := (BitVec.toNat Vm)
      let index : Int := (BitVec.toNat M)
      (elements, esize, index, m))
    else (elements, esize, index, m)
  let m := m
  let index := index
  let esize := esize
  let elements := elements
  sail_assert ((0 ≤b m) && (m ≤b 31)) "src/instrs32.sail:33410.43-33410.44"
  (execute_aarch32_instrs_VQRDMLAH_Op_A_txt d elements esize index m n regs scalar_form)

def decode_aarch32_instrs_VQRDMLAH_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let index ← (( do (undefined_int ()) ) : SailM Int )
  if ((! (← (HaveQRDMLAHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let index := index
  let add : Bool := true
  let scalar_form : Bool := false
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv 64 esize)
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let regs :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VQRDMLAH_Op_A_txt d elements esize index m n regs scalar_form)

def decode_aarch32_instrs_VQRDMLAH_T2enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveQRDMLAHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let add : Bool := true
  let scalar_form : Bool := true
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let regs :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  let esize : Nat := 8
  let elements ← (( do (undefined_int ()) ) : SailM Int )
  let m ← (( do (undefined_int ()) ) : SailM Int )
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (elements, esize, index, m) : (Int × Int × Int × Int) :=
    if ((size == 0b01#2) : Bool)
    then
      (let esize : Nat := 16
      let elements : Int := 4
      let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
      let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
      (elements, esize, index, m))
    else (elements, esize, index, m)
  let (elements, esize, index, m) : (Int × Int × Int × Int) :=
    if ((size == 0b10#2) : Bool)
    then
      (let esize : Nat := 32
      let elements : Int := 2
      let m : Int := (BitVec.toNat Vm)
      let index : Int := (BitVec.toNat M)
      (elements, esize, index, m))
    else (elements, esize, index, m)
  let m := m
  let index := index
  let esize := esize
  let elements := elements
  sail_assert ((0 ≤b m) && (m ≤b 31)) "src/instrs32.sail:33511.43-33511.44"
  (execute_aarch32_instrs_VQRDMLAH_Op_A_txt d elements esize index m n regs scalar_form)

def decode_aarch32_instrs_VQRDMLSH_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let index ← (( do (undefined_int ()) ) : SailM Int )
  if ((! (← (HaveQRDMLAHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let index := index
  let add : Bool := false
  let scalar_form : Bool := false
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv 64 esize)
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let regs :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VQRDMLSH_Op_A_txt d elements esize index m n regs scalar_form)

def decode_aarch32_instrs_VQRDMLSH_A2enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveQRDMLAHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let add : Bool := false
  let scalar_form : Bool := true
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let regs :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  let esize : Nat := 8
  let elements ← (( do (undefined_int ()) ) : SailM Int )
  let m ← (( do (undefined_int ()) ) : SailM Int )
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let (elements, esize, index, m) : (Int × Int × Int × Int) :=
    if ((size == 0b01#2) : Bool)
    then
      (let esize : Nat := 16
      let elements : Int := 4
      let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
      let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
      (elements, esize, index, m))
    else (elements, esize, index, m)
  let (elements, esize, index, m) : (Int × Int × Int × Int) :=
    if ((size == 0b10#2) : Bool)
    then
      (let esize : Nat := 32
      let elements : Int := 2
      let m : Int := (BitVec.toNat Vm)
      let index : Int := (BitVec.toNat M)
      (elements, esize, index, m))
    else (elements, esize, index, m)
  let m := m
  let index := index
  let esize := esize
  let elements := elements
  sail_assert ((0 ≤b m) && (m ≤b 31)) "src/instrs32.sail:33640.43-33640.44"
  (execute_aarch32_instrs_VQRDMLSH_Op_A_txt d elements esize index m n regs scalar_form)

def decode_aarch32_instrs_VQRDMLSH_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let index ← (( do (undefined_int ()) ) : SailM Int )
  if ((! (← (HaveQRDMLAHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((size == 0b00#2) || (size == 0b11#2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let index := index
  let add : Bool := false
  let scalar_form : Bool := false
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let elements := (Int.ediv 64 esize)
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let regs :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VQRDMLSH_Op_A_txt d elements esize index m n regs scalar_form)

def decode_aarch32_instrs_VQRDMLSH_T2enc_A_txt (Q : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveQRDMLAHExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((size == 0b11#2) : Bool)
  then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let add : Bool := false
  let scalar_form : Bool := true
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let regs :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  let esize : Nat := 8
  let m ← (( do (undefined_int ()) ) : SailM Int )
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let elements ← (( do (undefined_int ()) ) : SailM Int )
  let (elements, esize, index, m) : (Int × Int × Int × Int) :=
    if ((size == 0b01#2) : Bool)
    then
      (let esize : Nat := 16
      let elements : Int := 4
      let m : Int := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
      let index : Int := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
      (elements, esize, index, m))
    else (elements, esize, index, m)
  let (elements, esize, index, m) : (Int × Int × Int × Int) :=
    if ((size == 0b10#2) : Bool)
    then
      (let esize : Nat := 32
      let elements : Int := 2
      let m : Int := (BitVec.toNat Vm)
      let index : Int := (BitVec.toNat M)
      (elements, esize, index, m))
    else (elements, esize, index, m)
  let m := m
  let index := index
  let esize := esize
  let elements := elements
  sail_assert ((0 ≤b m) && (m ≤b 31)) "src/instrs32.sail:33741.43-33741.44"
  (execute_aarch32_instrs_VQRDMLSH_Op_A_txt d elements esize index m n regs scalar_form)

def decode_aarch32_instrs_VQRSHL_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let n := (BitVec.toNat (N +++ Vn))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VQRSHL_Op_A_txt d elements esize m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VQRSHL_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let n := (BitVec.toNat (N +++ Vn))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VQRSHL_Op_A_txt d elements esize m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VQRSHRN_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := imm6
         if (((Sail.BitVec.extractLsb b__0 5 3) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((U == 0#1) && (op == 0#1)) : Bool)
      then (sailThrow ((Error_See "VRSHRN")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 2
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := imm6
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 5 3) == (0b001#3 : (BitVec 3))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 5 4) == (0b01#2 : (BitVec 2))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 5 5) == (1#1 : (BitVec 1))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else (elements, esize, shift_amount)
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let src_unsigned : Bool := ((U == 1#1) && (op == 1#1))
      let dest_unsigned : Bool := (U == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VQRSHRN_Op_A_txt d dest_unsigned elements esize m shift_amount src_unsigned))
  else (pure ())

def decode_aarch32_instrs_VQRSHRN_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := imm6
         if (((Sail.BitVec.extractLsb b__0 5 3) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((U == 0#1) && (op == 0#1)) : Bool)
      then (sailThrow ((Error_See "VRSHRN")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 2
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := imm6
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 5 3) == (0b001#3 : (BitVec 3))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 5 4) == (0b01#2 : (BitVec 2))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 5 5) == (1#1 : (BitVec 1))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else (elements, esize, shift_amount)
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let src_unsigned : Bool := ((U == 1#1) && (op == 1#1))
      let dest_unsigned : Bool := (U == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VQRSHRN_Op_A_txt d dest_unsigned elements esize m shift_amount src_unsigned))
  else (pure ())

def decode_aarch32_instrs_VQSHL_i_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (op : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         if (((Sail.BitVec.extractLsb b__0 6 3) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((U == 0#1) && (op == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 1
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := (L +++ imm6)
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 6 3) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := ((BitVec.toNat imm6) -i 8)
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 6 4) == (0b001#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := ((BitVec.toNat imm6) -i 16)
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 6 5) == (0b01#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := ((BitVec.toNat imm6) -i 32)
                    (elements, esize, shift_amount))
                  else
                    (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                      if (((Sail.BitVec.extractLsb b__1 6 6) == (1#1 : (BitVec 1))) : Bool)
                      then
                        (let esize : Nat := 64
                        let elements : Nat := 1
                        let shift_amount : Int := (BitVec.toNat imm6)
                        (elements, esize, shift_amount))
                      else (elements, esize, shift_amount)
                    (elements, esize, shift_amount))
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let src_unsigned : Bool := ((U == 1#1) && (op == 1#1))
      let dest_unsigned : Bool := (U == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 => (execute_aarch32_instrs_VQSHL_i_Op_A_txt d dest_unsigned elements 8 m regs shift_amount src_unsigned)
      | 16 => (execute_aarch32_instrs_VQSHL_i_Op_A_txt d dest_unsigned elements 16 m regs shift_amount src_unsigned)
      | 32 => (execute_aarch32_instrs_VQSHL_i_Op_A_txt d dest_unsigned elements 32 m regs shift_amount src_unsigned)
      | 64 => (execute_aarch32_instrs_VQSHL_i_Op_A_txt d dest_unsigned elements 64 m regs shift_amount src_unsigned)
      | _ => sail_assert false "src/instrs32.sail:34086.26-34086.27")
  else (pure ())

def decode_aarch32_instrs_VQSHL_i_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (op : (BitVec 1)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         if (((Sail.BitVec.extractLsb b__0 6 3) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((U == 0#1) && (op == 0#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 1
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := (L +++ imm6)
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 6 3) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := ((BitVec.toNat imm6) -i 8)
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 6 4) == (0b001#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := ((BitVec.toNat imm6) -i 16)
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 6 5) == (0b01#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := ((BitVec.toNat imm6) -i 32)
                    (elements, esize, shift_amount))
                  else
                    (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                      if (((Sail.BitVec.extractLsb b__1 6 6) == (1#1 : (BitVec 1))) : Bool)
                      then
                        (let esize : Nat := 64
                        let elements : Nat := 1
                        let shift_amount : Int := (BitVec.toNat imm6)
                        (elements, esize, shift_amount))
                      else (elements, esize, shift_amount)
                    (elements, esize, shift_amount))
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let src_unsigned : Bool := ((U == 1#1) && (op == 1#1))
      let dest_unsigned : Bool := (U == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 => (execute_aarch32_instrs_VQSHL_i_Op_A_txt d dest_unsigned elements 8 m regs shift_amount src_unsigned)
      | 16 => (execute_aarch32_instrs_VQSHL_i_Op_A_txt d dest_unsigned elements 16 m regs shift_amount src_unsigned)
      | 32 => (execute_aarch32_instrs_VQSHL_i_Op_A_txt d dest_unsigned elements 32 m regs shift_amount src_unsigned)
      | 64 => (execute_aarch32_instrs_VQSHL_i_Op_A_txt d dest_unsigned elements 64 m regs shift_amount src_unsigned)
      | _ => sail_assert false "src/instrs32.sail:34171.26-34171.27")
  else (pure ())

def decode_aarch32_instrs_VQSHL_r_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let n := (BitVec.toNat (N +++ Vn))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VQSHL_r_Op_A_txt d elements esize m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VQSHL_r_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let n := (BitVec.toNat (N +++ Vn))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VQSHL_r_Op_A_txt d elements esize m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VQSHRN_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := imm6
         if (((Sail.BitVec.extractLsb b__0 5 3) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((U == 0#1) && (op == 0#1)) : Bool)
      then (sailThrow ((Error_See "VSHRN")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 2
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := imm6
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 5 3) == (0b001#3 : (BitVec 3))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 5 4) == (0b01#2 : (BitVec 2))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 5 5) == (1#1 : (BitVec 1))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else (elements, esize, shift_amount)
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let src_unsigned : Bool := ((U == 1#1) && (op == 1#1))
      let dest_unsigned : Bool := (U == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VQSHRN_Op_A_txt d dest_unsigned elements esize m shift_amount src_unsigned))
  else (pure ())

def decode_aarch32_instrs_VQSHRN_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := imm6
         if (((Sail.BitVec.extractLsb b__0 5 3) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((U == 0#1) && (op == 0#1)) : Bool)
      then (sailThrow ((Error_See "VSHRN")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 2
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := imm6
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 5 3) == (0b001#3 : (BitVec 3))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 5 4) == (0b01#2 : (BitVec 2))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 5 5) == (1#1 : (BitVec 1))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else (elements, esize, shift_amount)
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let src_unsigned : Bool := ((U == 1#1) && (op == 1#1))
      let dest_unsigned : Bool := (U == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VQSHRN_Op_A_txt d dest_unsigned elements esize m shift_amount src_unsigned))
  else (pure ())

def decode_aarch32_instrs_VQSUB_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
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
      (execute_aarch32_instrs_VQSUB_Op_A_txt d elements esize m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VQSUB_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
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
      (execute_aarch32_instrs_VQSUB_Op_A_txt d elements esize m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VRADDHN_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VRADDHN_Op_A_txt d elements esize m n))
  else (pure ())

def decode_aarch32_instrs_VRADDHN_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VRADDHN_Op_A_txt d elements esize m n))
  else (pure ())

def decode_aarch32_instrs_VRECPE_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((size == 0b01#2) && ((! (HaveFP16Ext ())) || (F == 0#1))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let floating_point : Bool := (F == 1#1)
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
      (execute_aarch32_instrs_VRECPE_Op_A_txt d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VRECPE_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((size == 0b01#2) && ((! (HaveFP16Ext ())) || (F == 0#1))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (size == 0b01#2)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let floating_point : Bool := (F == 1#1)
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
      (execute_aarch32_instrs_VRECPE_Op_A_txt d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VRECPS_A1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VRECPS_Op_A_txt d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VRECPS_T1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VRECPS_Op_A_txt d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VREV16_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 2)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((BitVec.toNat op) +i (BitVec.toNat size)) ≥b 3) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let container_size : Nat := 16
      let container_size : Int :=
        match (op : BitVec 2) with
        | 0b10 => 16
        | 0b01 => 32
        | 0b00 => 64
        | _ => container_size
      let container_size := container_size
      let containers := (Int.ediv 64 container_size)
      let elements_per_container := (Int.ediv container_size esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VREV16_Op_A_txt containers d elements_per_container esize m regs))
  else (pure ())

def decode_aarch32_instrs_VREV16_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 2)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((BitVec.toNat op) +i (BitVec.toNat size)) ≥b 3) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let container_size : Nat := 16
      let container_size : Int :=
        match (op : BitVec 2) with
        | 0b10 => 16
        | 0b01 => 32
        | 0b00 => 64
        | _ => container_size
      let container_size := container_size
      let containers := (Int.ediv 64 container_size)
      let elements_per_container := (Int.ediv container_size esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VREV16_Op_A_txt containers d elements_per_container esize m regs))
  else (pure ())

def decode_aarch32_instrs_VRHADD_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
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
      (execute_aarch32_instrs_VRHADD_Op_A_txt d elements esize m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VRHADD_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
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
      (execute_aarch32_instrs_VRHADD_Op_A_txt d elements esize m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VRSHL_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let n := (BitVec.toNat (N +++ Vn))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VRSHL_Op_A_txt d elements esize m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VRSHL_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let n := (BitVec.toNat (N +++ Vn))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VRSHL_Op_A_txt d elements esize m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VRSHR_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         if (((Sail.BitVec.extractLsb b__0 6 3) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 1
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := (L +++ imm6)
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 6 3) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 6 4) == (0b001#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 6 5) == (0b01#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else
                    (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                      if (((Sail.BitVec.extractLsb b__1 6 6) == (1#1 : (BitVec 1))) : Bool)
                      then
                        (let esize : Nat := 64
                        let elements : Nat := 1
                        let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                        (elements, esize, shift_amount))
                      else (elements, esize, shift_amount)
                    (elements, esize, shift_amount))
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let is_unsigned : Bool := (U == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 => (execute_aarch32_instrs_VRSHR_Op_A_txt d elements 8 m regs shift_amount is_unsigned)
      | 16 => (execute_aarch32_instrs_VRSHR_Op_A_txt d elements 16 m regs shift_amount is_unsigned)
      | 32 => (execute_aarch32_instrs_VRSHR_Op_A_txt d elements 32 m regs shift_amount is_unsigned)
      | 64 => (execute_aarch32_instrs_VRSHR_Op_A_txt d elements 64 m regs shift_amount is_unsigned)
      | _ => sail_assert false "src/instrs32.sail:35204.26-35204.27")
  else (pure ())

def decode_aarch32_instrs_VRSHR_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         if (((Sail.BitVec.extractLsb b__0 6 3) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 1
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := (L +++ imm6)
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 6 3) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 6 4) == (0b001#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 6 5) == (0b01#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else
                    (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                      if (((Sail.BitVec.extractLsb b__1 6 6) == (1#1 : (BitVec 1))) : Bool)
                      then
                        (let esize : Nat := 64
                        let elements : Nat := 1
                        let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                        (elements, esize, shift_amount))
                      else (elements, esize, shift_amount)
                    (elements, esize, shift_amount))
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let is_unsigned : Bool := (U == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 => (execute_aarch32_instrs_VRSHR_Op_A_txt d elements 8 m regs shift_amount is_unsigned)
      | 16 => (execute_aarch32_instrs_VRSHR_Op_A_txt d elements 16 m regs shift_amount is_unsigned)
      | 32 => (execute_aarch32_instrs_VRSHR_Op_A_txt d elements 32 m regs shift_amount is_unsigned)
      | 64 => (execute_aarch32_instrs_VRSHR_Op_A_txt d elements 64 m regs shift_amount is_unsigned)
      | _ => sail_assert false "src/instrs32.sail:35284.26-35284.27")
  else (pure ())

def decode_aarch32_instrs_VRSHRN_A1enc_A_txt (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := imm6
         if (((Sail.BitVec.extractLsb b__0 5 3) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 2
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := imm6
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 5 3) == (0b001#3 : (BitVec 3))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 5 4) == (0b01#2 : (BitVec 2))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 5 5) == (1#1 : (BitVec 1))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else (elements, esize, shift_amount)
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VRSHRN_Op_A_txt d elements esize m shift_amount))
  else (pure ())

def decode_aarch32_instrs_VRSHRN_T1enc_A_txt (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := imm6
         if (((Sail.BitVec.extractLsb b__0 5 3) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 2
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := imm6
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 5 3) == (0b001#3 : (BitVec 3))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 5 4) == (0b01#2 : (BitVec 2))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 5 5) == (1#1 : (BitVec 1))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else (elements, esize, shift_amount)
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VRSHRN_Op_A_txt d elements esize m shift_amount))
  else (pure ())

def decode_aarch32_instrs_VRSQRTE_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((size == 0b01#2) && ((! (HaveFP16Ext ())) || (F == 0#1))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let floating_point : Bool := (F == 1#1)
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
      (execute_aarch32_instrs_VRSQRTE_Op_A_txt d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VRSQRTE_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (F : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((size == 0b01#2) && ((! (HaveFP16Ext ())) || (F == 0#1))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((←((pure (size == 0b01#2)) <&&> (do
           (InITBlock ())))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let floating_point : Bool := (F == 1#1)
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
      (execute_aarch32_instrs_VRSQRTE_Op_A_txt d elements esize floating_point m regs))
  else (pure ())

def decode_aarch32_instrs_VRSQRTS_A1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VRSQRTS_Op_A_txt d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VRSQRTS_T1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VRSQRTS_Op_A_txt d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VRSRA_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         if (((Sail.BitVec.extractLsb b__0 6 3) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 1
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := (L +++ imm6)
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 6 3) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 6 4) == (0b001#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 6 5) == (0b01#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else
                    (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                      if (((Sail.BitVec.extractLsb b__1 6 6) == (1#1 : (BitVec 1))) : Bool)
                      then
                        (let esize : Nat := 64
                        let elements : Nat := 1
                        let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                        (elements, esize, shift_amount))
                      else (elements, esize, shift_amount)
                    (elements, esize, shift_amount))
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let is_unsigned : Bool := (U == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 => (execute_aarch32_instrs_VRSRA_Op_A_txt d elements 8 m regs shift_amount is_unsigned)
      | 16 => (execute_aarch32_instrs_VRSRA_Op_A_txt d elements 16 m regs shift_amount is_unsigned)
      | 32 => (execute_aarch32_instrs_VRSRA_Op_A_txt d elements 32 m regs shift_amount is_unsigned)
      | 64 => (execute_aarch32_instrs_VRSRA_Op_A_txt d elements 64 m regs shift_amount is_unsigned)
      | _ => sail_assert false "src/instrs32.sail:35727.26-35727.27")
  else (pure ())

def decode_aarch32_instrs_VRSRA_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         if (((Sail.BitVec.extractLsb b__0 6 3) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 1
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := (L +++ imm6)
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 6 3) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 6 4) == (0b001#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 6 5) == (0b01#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else
                    (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                      if (((Sail.BitVec.extractLsb b__1 6 6) == (1#1 : (BitVec 1))) : Bool)
                      then
                        (let esize : Nat := 64
                        let elements : Nat := 1
                        let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                        (elements, esize, shift_amount))
                      else (elements, esize, shift_amount)
                    (elements, esize, shift_amount))
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let is_unsigned : Bool := (U == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 => (execute_aarch32_instrs_VRSRA_Op_A_txt d elements 8 m regs shift_amount is_unsigned)
      | 16 => (execute_aarch32_instrs_VRSRA_Op_A_txt d elements 16 m regs shift_amount is_unsigned)
      | 32 => (execute_aarch32_instrs_VRSRA_Op_A_txt d elements 32 m regs shift_amount is_unsigned)
      | 64 => (execute_aarch32_instrs_VRSRA_Op_A_txt d elements 64 m regs shift_amount is_unsigned)
      | _ => sail_assert false "src/instrs32.sail:35807.26-35807.27")
  else (pure ())

def decode_aarch32_instrs_VRSUBHN_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VRSUBHN_Op_A_txt d elements esize m n))
  else (pure ())

def decode_aarch32_instrs_VRSUBHN_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VRSUBHN_Op_A_txt d elements esize m n))
  else (pure ())

def decode_aarch32_instrs_VSHL_i_A1enc_A_txt (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         if (((Sail.BitVec.extractLsb b__0 6 3) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 1
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := (L +++ imm6)
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 6 3) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := ((BitVec.toNat imm6) -i 8)
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 6 4) == (0b001#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := ((BitVec.toNat imm6) -i 16)
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 6 5) == (0b01#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := ((BitVec.toNat imm6) -i 32)
                    (elements, esize, shift_amount))
                  else
                    (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                      if (((Sail.BitVec.extractLsb b__1 6 6) == (1#1 : (BitVec 1))) : Bool)
                      then
                        (let esize : Nat := 64
                        let elements : Nat := 1
                        let shift_amount : Int := (BitVec.toNat imm6)
                        (elements, esize, shift_amount))
                      else (elements, esize, shift_amount)
                    (elements, esize, shift_amount))
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 => (execute_aarch32_instrs_VSHL_i_Op_A_txt d elements 8 m regs shift_amount)
      | 16 => (execute_aarch32_instrs_VSHL_i_Op_A_txt d elements 16 m regs shift_amount)
      | 32 => (execute_aarch32_instrs_VSHL_i_Op_A_txt d elements 32 m regs shift_amount)
      | 64 => (execute_aarch32_instrs_VSHL_i_Op_A_txt d elements 64 m regs shift_amount)
      | _ => sail_assert false "src/instrs32.sail:35979.26-35979.27")
  else (pure ())

def decode_aarch32_instrs_VSHL_i_T1enc_A_txt (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         if (((Sail.BitVec.extractLsb b__0 6 3) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 1
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := (L +++ imm6)
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 6 3) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := ((BitVec.toNat imm6) -i 8)
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 6 4) == (0b001#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := ((BitVec.toNat imm6) -i 16)
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 6 5) == (0b01#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := ((BitVec.toNat imm6) -i 32)
                    (elements, esize, shift_amount))
                  else
                    (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                      if (((Sail.BitVec.extractLsb b__1 6 6) == (1#1 : (BitVec 1))) : Bool)
                      then
                        (let esize : Nat := 64
                        let elements : Nat := 1
                        let shift_amount : Int := (BitVec.toNat imm6)
                        (elements, esize, shift_amount))
                      else (elements, esize, shift_amount)
                    (elements, esize, shift_amount))
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 => (execute_aarch32_instrs_VSHL_i_Op_A_txt d elements 8 m regs shift_amount)
      | 16 => (execute_aarch32_instrs_VSHL_i_Op_A_txt d elements 16 m regs shift_amount)
      | 32 => (execute_aarch32_instrs_VSHL_i_Op_A_txt d elements 32 m regs shift_amount)
      | 64 => (execute_aarch32_instrs_VSHL_i_Op_A_txt d elements 64 m regs shift_amount)
      | _ => sail_assert false "src/instrs32.sail:36057.26-36057.27")
  else (pure ())

def decode_aarch32_instrs_VSHLL_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := imm6
         if (((Sail.BitVec.extractLsb b__0 5 3) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 2
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := imm6
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 5 3) == (0b001#3 : (BitVec 3))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := ((BitVec.toNat imm6) -i 8)
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 5 4) == (0b01#2 : (BitVec 2))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := ((BitVec.toNat imm6) -i 16)
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 5 5) == (1#1 : (BitVec 1))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := ((BitVec.toNat imm6) -i 32)
                    (elements, esize, shift_amount))
                  else (elements, esize, shift_amount)
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      if ((shift_amount == 0) : Bool)
      then (sailThrow ((Error_See "VMOVL")) : SailM Unit)
      else (pure ())
      let shift_amount := shift_amount
      let is_unsigned : Bool := (U == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VSHLL_Op_A_txt d elements esize m shift_amount is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VSHLL_A2enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let shift_amount := esize
      let is_unsigned : Bool := false
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VSHLL_Op_A_txt d elements esize m shift_amount is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VSHLL_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := imm6
         if (((Sail.BitVec.extractLsb b__0 5 3) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 2
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := imm6
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 5 3) == (0b001#3 : (BitVec 3))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := ((BitVec.toNat imm6) -i 8)
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 5 4) == (0b01#2 : (BitVec 2))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := ((BitVec.toNat imm6) -i 16)
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 5 5) == (1#1 : (BitVec 1))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := ((BitVec.toNat imm6) -i 32)
                    (elements, esize, shift_amount))
                  else (elements, esize, shift_amount)
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      if ((shift_amount == 0) : Bool)
      then (sailThrow ((Error_See "VMOVL")) : SailM Unit)
      else (pure ())
      let shift_amount := shift_amount
      let is_unsigned : Bool := (U == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VSHLL_Op_A_txt d elements esize m shift_amount is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VSHLL_T2enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) || ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let shift_amount := esize
      let is_unsigned : Bool := false
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VSHLL_Op_A_txt d elements esize m shift_amount is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VSHL_r_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let n := (BitVec.toNat (N +++ Vn))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VSHL_r_Op_A_txt d elements esize m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VSHL_r_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let is_unsigned : Bool := (U == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let elements := (Int.ediv 64 esize)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let n := (BitVec.toNat (N +++ Vn))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VSHL_r_Op_A_txt d elements esize m n regs is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VSHR_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         if (((Sail.BitVec.extractLsb b__0 6 3) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 1
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := (L +++ imm6)
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 6 3) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 6 4) == (0b001#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 6 5) == (0b01#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else
                    (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                      if (((Sail.BitVec.extractLsb b__1 6 6) == (1#1 : (BitVec 1))) : Bool)
                      then
                        (let esize : Nat := 64
                        let elements : Nat := 1
                        let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                        (elements, esize, shift_amount))
                      else (elements, esize, shift_amount)
                    (elements, esize, shift_amount))
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let is_unsigned : Bool := (U == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 => (execute_aarch32_instrs_VSHR_Op_A_txt d elements 8 m regs shift_amount is_unsigned)
      | 16 => (execute_aarch32_instrs_VSHR_Op_A_txt d elements 16 m regs shift_amount is_unsigned)
      | 32 => (execute_aarch32_instrs_VSHR_Op_A_txt d elements 32 m regs shift_amount is_unsigned)
      | 64 => (execute_aarch32_instrs_VSHR_Op_A_txt d elements 64 m regs shift_amount is_unsigned)
      | _ => sail_assert false "src/instrs32.sail:36431.26-36431.27")
  else (pure ())

def decode_aarch32_instrs_VSHR_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         if (((Sail.BitVec.extractLsb b__0 6 3) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 1
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := (L +++ imm6)
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 6 3) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 6 4) == (0b001#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 6 5) == (0b01#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else
                    (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                      if (((Sail.BitVec.extractLsb b__1 6 6) == (1#1 : (BitVec 1))) : Bool)
                      then
                        (let esize : Nat := 64
                        let elements : Nat := 1
                        let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                        (elements, esize, shift_amount))
                      else (elements, esize, shift_amount)
                    (elements, esize, shift_amount))
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let is_unsigned : Bool := (U == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 => (execute_aarch32_instrs_VSHR_Op_A_txt d elements 8 m regs shift_amount is_unsigned)
      | 16 => (execute_aarch32_instrs_VSHR_Op_A_txt d elements 16 m regs shift_amount is_unsigned)
      | 32 => (execute_aarch32_instrs_VSHR_Op_A_txt d elements 32 m regs shift_amount is_unsigned)
      | 64 => (execute_aarch32_instrs_VSHR_Op_A_txt d elements 64 m regs shift_amount is_unsigned)
      | _ => sail_assert false "src/instrs32.sail:36511.26-36511.27")
  else (pure ())

def decode_aarch32_instrs_VSHRN_A1enc_A_txt (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := imm6
         if (((Sail.BitVec.extractLsb b__0 5 3) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 2
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := imm6
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 5 3) == (0b001#3 : (BitVec 3))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 5 4) == (0b01#2 : (BitVec 2))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 5 5) == (1#1 : (BitVec 1))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else (elements, esize, shift_amount)
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VSHRN_Op_A_txt d elements esize m shift_amount))
  else (pure ())

def decode_aarch32_instrs_VSHRN_T1enc_A_txt (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := imm6
         if (((Sail.BitVec.extractLsb b__0 5 3) == (0b000#3 : (BitVec 3))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 2
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := imm6
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 5 3) == (0b001#3 : (BitVec 3))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 5 4) == (0b01#2 : (BitVec 2))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 5 5) == (1#1 : (BitVec 1))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else (elements, esize, shift_amount)
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VSHRN_Op_A_txt d elements esize m shift_amount))
  else (pure ())

def decode_aarch32_instrs_VSLI_A1enc_A_txt (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         if (((Sail.BitVec.extractLsb b__0 6 3) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 1
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := (L +++ imm6)
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 6 3) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := ((BitVec.toNat imm6) -i 8)
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 6 4) == (0b001#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := ((BitVec.toNat imm6) -i 16)
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 6 5) == (0b01#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := ((BitVec.toNat imm6) -i 32)
                    (elements, esize, shift_amount))
                  else
                    (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                      if (((Sail.BitVec.extractLsb b__1 6 6) == (1#1 : (BitVec 1))) : Bool)
                      then
                        (let esize : Nat := 64
                        let elements : Nat := 1
                        let shift_amount : Int := (BitVec.toNat imm6)
                        (elements, esize, shift_amount))
                      else (elements, esize, shift_amount)
                    (elements, esize, shift_amount))
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 => (execute_aarch32_instrs_VSLI_Op_A_txt d elements 8 m regs shift_amount)
      | 16 => (execute_aarch32_instrs_VSLI_Op_A_txt d elements 16 m regs shift_amount)
      | 32 => (execute_aarch32_instrs_VSLI_Op_A_txt d elements 32 m regs shift_amount)
      | 64 => (execute_aarch32_instrs_VSLI_Op_A_txt d elements 64 m regs shift_amount)
      | _ => sail_assert false "src/instrs32.sail:36729.26-36729.27")
  else (pure ())

def decode_aarch32_instrs_VSLI_T1enc_A_txt (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         if (((Sail.BitVec.extractLsb b__0 6 3) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 1
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := (L +++ imm6)
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 6 3) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := ((BitVec.toNat imm6) -i 8)
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 6 4) == (0b001#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := ((BitVec.toNat imm6) -i 16)
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 6 5) == (0b01#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := ((BitVec.toNat imm6) -i 32)
                    (elements, esize, shift_amount))
                  else
                    (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                      if (((Sail.BitVec.extractLsb b__1 6 6) == (1#1 : (BitVec 1))) : Bool)
                      then
                        (let esize : Nat := 64
                        let elements : Nat := 1
                        let shift_amount : Int := (BitVec.toNat imm6)
                        (elements, esize, shift_amount))
                      else (elements, esize, shift_amount)
                    (elements, esize, shift_amount))
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 => (execute_aarch32_instrs_VSLI_Op_A_txt d elements 8 m regs shift_amount)
      | 16 => (execute_aarch32_instrs_VSLI_Op_A_txt d elements 16 m regs shift_amount)
      | 32 => (execute_aarch32_instrs_VSLI_Op_A_txt d elements 32 m regs shift_amount)
      | 64 => (execute_aarch32_instrs_VSLI_Op_A_txt d elements 64 m regs shift_amount)
      | _ => sail_assert false "src/instrs32.sail:36807.26-36807.27")
  else (pure ())

def decode_aarch32_instrs_VSQRT_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:36850.29-36850.30"
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
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
      (execute_aarch32_instrs_VSQRT_Op_A_txt d esize m))
  else (pure ())

def decode_aarch32_instrs_VSQRT_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      if ((←((pure ((_get_FPSCR_Type_length (← (FPSCR_read__1 ()))) != 0b000#3)) <||> (do
           (pure ((_get_FPSCR_Type_Stride (← (FPSCR_read__1 ()))) != 0b00#2))))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
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
      (execute_aarch32_instrs_VSQRT_Op_A_txt d esize m))
  else (pure ())

def decode_aarch32_instrs_VSRA_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         if (((Sail.BitVec.extractLsb b__0 6 3) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 1
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := (L +++ imm6)
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 6 3) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 6 4) == (0b001#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 6 5) == (0b01#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else
                    (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                      if (((Sail.BitVec.extractLsb b__1 6 6) == (1#1 : (BitVec 1))) : Bool)
                      then
                        (let esize : Nat := 64
                        let elements : Nat := 1
                        let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                        (elements, esize, shift_amount))
                      else (elements, esize, shift_amount)
                    (elements, esize, shift_amount))
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let is_unsigned : Bool := (U == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 => (execute_aarch32_instrs_VSRA_Op_A_txt d elements 8 m regs shift_amount is_unsigned)
      | 16 => (execute_aarch32_instrs_VSRA_Op_A_txt d elements 16 m regs shift_amount is_unsigned)
      | 32 => (execute_aarch32_instrs_VSRA_Op_A_txt d elements 32 m regs shift_amount is_unsigned)
      | 64 => (execute_aarch32_instrs_VSRA_Op_A_txt d elements 64 m regs shift_amount is_unsigned)
      | _ => sail_assert false "src/instrs32.sail:37028.26-37028.27")
  else (pure ())

def decode_aarch32_instrs_VSRA_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         if (((Sail.BitVec.extractLsb b__0 6 3) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 1
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := (L +++ imm6)
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 6 3) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 6 4) == (0b001#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 6 5) == (0b01#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else
                    (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                      if (((Sail.BitVec.extractLsb b__1 6 6) == (1#1 : (BitVec 1))) : Bool)
                      then
                        (let esize : Nat := 64
                        let elements : Nat := 1
                        let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                        (elements, esize, shift_amount))
                      else (elements, esize, shift_amount)
                    (elements, esize, shift_amount))
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let is_unsigned : Bool := (U == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 => (execute_aarch32_instrs_VSRA_Op_A_txt d elements 8 m regs shift_amount is_unsigned)
      | 16 => (execute_aarch32_instrs_VSRA_Op_A_txt d elements 16 m regs shift_amount is_unsigned)
      | 32 => (execute_aarch32_instrs_VSRA_Op_A_txt d elements 32 m regs shift_amount is_unsigned)
      | 64 => (execute_aarch32_instrs_VSRA_Op_A_txt d elements 64 m regs shift_amount is_unsigned)
      | _ => sail_assert false "src/instrs32.sail:37108.26-37108.27")
  else (pure ())

def decode_aarch32_instrs_VSRI_A1enc_A_txt (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         if (((Sail.BitVec.extractLsb b__0 6 3) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 1
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := (L +++ imm6)
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 6 3) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 6 4) == (0b001#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 6 5) == (0b01#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else
                    (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                      if (((Sail.BitVec.extractLsb b__1 6 6) == (1#1 : (BitVec 1))) : Bool)
                      then
                        (let esize : Nat := 64
                        let elements : Nat := 1
                        let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                        (elements, esize, shift_amount))
                      else (elements, esize, shift_amount)
                    (elements, esize, shift_amount))
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 => (execute_aarch32_instrs_VSRI_Op_A_txt d elements 8 m regs shift_amount)
      | 16 => (execute_aarch32_instrs_VSRI_Op_A_txt d elements 16 m regs shift_amount)
      | 32 => (execute_aarch32_instrs_VSRI_Op_A_txt d elements 32 m regs shift_amount)
      | 64 => (execute_aarch32_instrs_VSRI_Op_A_txt d elements 64 m regs shift_amount)
      | _ => sail_assert false "src/instrs32.sail:37204.26-37204.27")
  else (pure ())

def decode_aarch32_instrs_VSRI_T1enc_A_txt (D : (BitVec 1)) (imm6 : (BitVec 6)) (Vd : (BitVec 4)) (L : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((let b__0 := (L +++ imm6)
         if (((Sail.BitVec.extractLsb b__0 6 3) == (0x0#4 : (BitVec 4))) : Bool)
         then true
         else false : Bool) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let esize : Nat := 8
      let elements : Nat := 1
      let shift_amount ← (( do (undefined_int ()) ) : SailM Int )
      let (elements, esize, shift_amount) : (Int × Int × Int) :=
        let b__1 := (L +++ imm6)
        let (elements, esize, shift_amount) : (Int × Int × Int) :=
          if (((Sail.BitVec.extractLsb b__1 6 3) == (0x1#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 8
            let elements : Nat := 8
            let shift_amount : Int := (16 -i (BitVec.toNat imm6))
            (elements, esize, shift_amount))
          else
            (let (elements, esize, shift_amount) : (Int × Int × Int) :=
              if (((Sail.BitVec.extractLsb b__1 6 4) == (0b001#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 16
                let elements : Nat := 4
                let shift_amount : Int := (32 -i (BitVec.toNat imm6))
                (elements, esize, shift_amount))
              else
                (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                  if (((Sail.BitVec.extractLsb b__1 6 5) == (0b01#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 32
                    let elements : Nat := 2
                    let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                    (elements, esize, shift_amount))
                  else
                    (let (elements, esize, shift_amount) : (Int × Int × Int) :=
                      if (((Sail.BitVec.extractLsb b__1 6 6) == (1#1 : (BitVec 1))) : Bool)
                      then
                        (let esize : Nat := 64
                        let elements : Nat := 1
                        let shift_amount : Int := (64 -i (BitVec.toNat imm6))
                        (elements, esize, shift_amount))
                      else (elements, esize, shift_amount)
                    (elements, esize, shift_amount))
                (elements, esize, shift_amount))
            (elements, esize, shift_amount))
        (elements, esize, shift_amount)
      let shift_amount := shift_amount
      let esize := esize
      let elements := elements
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      match esize with
      | 8 => (execute_aarch32_instrs_VSRI_Op_A_txt d elements 8 m regs shift_amount)
      | 16 => (execute_aarch32_instrs_VSRI_Op_A_txt d elements 16 m regs shift_amount)
      | 32 => (execute_aarch32_instrs_VSRI_Op_A_txt d elements 32 m regs shift_amount)
      | 64 => (execute_aarch32_instrs_VSRI_Op_A_txt d elements 64 m regs shift_amount)
      | _ => sail_assert false "src/instrs32.sail:37282.26-37282.27")
  else (pure ())

def decode_aarch32_instrs_VST1_1_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST1_1_Op_A_txt alignment d ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST1_1_A2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST1_1_Op_A_txt alignment d ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST1_1_A3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST1_1_Op_A_txt alignment d ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST1_1_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST1_1_Op_A_txt alignment d ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST1_1_T2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST1_1_Op_A_txt alignment d ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST1_1_T3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST1_1_Op_A_txt alignment d ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST1_m_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
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
      sail_assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:37615.173-37615.174"
      (execute_aarch32_instrs_VST1_m_Op_A_txt alignment d ebytes elements m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VST1_m_A2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
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
      sail_assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:37652.173-37652.174"
      (execute_aarch32_instrs_VST1_m_Op_A_txt alignment d ebytes elements m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VST1_m_A3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
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
      sail_assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:37689.173-37689.174"
      (execute_aarch32_instrs_VST1_m_Op_A_txt alignment d ebytes elements m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VST1_m_A4enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
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
      sail_assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:37723.173-37723.174"
      (execute_aarch32_instrs_VST1_m_Op_A_txt alignment d ebytes elements m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VST1_m_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
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
      sail_assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:37760.173-37760.174"
      (execute_aarch32_instrs_VST1_m_Op_A_txt alignment d ebytes elements m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VST1_m_T2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
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
      sail_assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:37797.173-37797.174"
      (execute_aarch32_instrs_VST1_m_Op_A_txt alignment d ebytes elements m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VST1_m_T3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
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
      sail_assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:37834.173-37834.174"
      (execute_aarch32_instrs_VST1_m_Op_A_txt alignment d ebytes elements m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VST1_m_T4enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
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
      sail_assert (((((regs == 1) || (regs == 2)) || (regs == 3)) || (regs == 4)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:37868.173-37868.174"
      (execute_aarch32_instrs_VST1_m_Op_A_txt alignment d ebytes elements m n register_index regs wback))
  else (pure ())

def decode_aarch32_instrs_VST2_1_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST2_1_Op_A_txt alignment d d2 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST2_1_A2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST2_1_Op_A_txt alignment d d2 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST2_1_A3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST2_1_Op_A_txt alignment d d2 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST2_1_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST2_1_Op_A_txt alignment d d2 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST2_1_T2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST2_1_Op_A_txt alignment d d2 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST2_1_T3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST2_1_Op_A_txt alignment d d2 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST2_m_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
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
      sail_assert (((pairs == 1) || (pairs == 2)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:38187.168-38187.169"
      (execute_aarch32_instrs_VST2_m_Op_A_txt alignment d d2 ebytes elements m n pairs register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST2_m_A2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
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
      sail_assert (((pairs == 1) || (pairs == 2)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:38226.168-38226.169"
      (execute_aarch32_instrs_VST2_m_Op_A_txt alignment d d2 ebytes elements m n pairs register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST2_m_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
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
      sail_assert (((pairs == 1) || (pairs == 2)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:38268.168-38268.169"
      (execute_aarch32_instrs_VST2_m_Op_A_txt alignment d d2 ebytes elements m n pairs register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST2_m_T2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
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
      sail_assert (((pairs == 1) || (pairs == 2)) && ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:38307.168-38307.169"
      (execute_aarch32_instrs_VST2_m_Op_A_txt alignment d d2 ebytes elements m n pairs register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST3_1_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST3_1_Op_A_txt d d2 d3 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST3_1_A2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST3_1_Op_A_txt d d2 d3 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST3_1_A3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST3_1_Op_A_txt d d2 d3 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST3_1_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST3_1_Op_A_txt d d2 d3 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST3_1_T2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST3_1_Op_A_txt d d2 d3 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST3_1_T3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
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
      (execute_aarch32_instrs_VST3_1_Op_A_txt d d2 d3 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST3_m_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) || ((BitVec.join1 [(BitVec.access align 1)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let inc_name : Nat := 1
      let inc_name ← (( do
        match (itype : BitVec 4) with
        | 0b0100 => (pure 1)
        | 0b0101 => (pure 2)
        | _ => sailThrow ((Error_See "Related encodings")) ) : SailM Int )
      let inc_name := inc_name
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
      (execute_aarch32_instrs_VST3_m_Op_A_txt alignment d d2 d3 ebytes elements m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST3_m_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) || ((BitVec.join1 [(BitVec.access align 1)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let inc_name : Nat := 1
      let inc_name ← (( do
        match (itype : BitVec 4) with
        | 0b0100 => (pure 1)
        | 0b0101 => (pure 2)
        | _ => sailThrow ((Error_See "Related encodings")) ) : SailM Int )
      let inc_name := inc_name
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
      (execute_aarch32_instrs_VST3_m_Op_A_txt alignment d d2 d3 ebytes elements m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST4_1_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b00#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
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
      (execute_aarch32_instrs_VST4_1_Op_A_txt alignment d d2 d3 d4 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST4_1_A2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b01#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
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
      (execute_aarch32_instrs_VST4_1_Op_A_txt alignment d d2 d3 d4 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST4_1_A3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b10#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
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
      sail_assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) || (index == 4)) || (index == 5)) || (index == 6)) || (index == 7)) && ((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:38846.183-38846.184"
      (execute_aarch32_instrs_VST4_1_Op_A_txt alignment d d2 d3 d4 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST4_1_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b00#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
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
      (execute_aarch32_instrs_VST4_1_Op_A_txt alignment d d2 d3 d4 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST4_1_T2enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b01#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
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
      (execute_aarch32_instrs_VST4_1_Op_A_txt alignment d d2 d3 d4 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST4_1_T3enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (index_align : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b10#2) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
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
      sail_assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)) || (index == 4)) || (index == 5)) || (index == 6)) || (index == 7)) && ((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32)))))))))) "src/instrs32.sail:38974.183-38974.184"
      (execute_aarch32_instrs_VST4_1_Op_A_txt alignment d d2 d3 d4 ebytes index m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST4_m_A1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let inc_name : Nat := 1
      let inc_name ← (( do
        match (itype : BitVec 4) with
        | 0b0000 => (pure 1)
        | 0b0001 => (pure 2)
        | _ => sailThrow ((Error_See "Related encodings")) ) : SailM Int )
      let inc_name := inc_name
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
      sail_assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32))))))))) "src/instrs32.sail:39055.149-39055.150"
      (execute_aarch32_instrs_VST4_m_Op_A_txt alignment d d2 d3 d4 ebytes elements m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VST4_m_T1enc_A_txt (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (itype : (BitVec 4)) (size : (BitVec 2)) (align : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size == 0b11#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let inc_name : Nat := 1
      let inc_name ← (( do
        match (itype : BitVec 4) with
        | 0b0000 => (pure 1)
        | 0b0001 => (pure 2)
        | _ => sailThrow ((Error_See "Related encodings")) ) : SailM Int )
      let inc_name := inc_name
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
      sail_assert ((0 ≤b n) && ((n ≤b 15) && ((0 ≤b m) && ((m ≤b 15) && (((((ebytes == 1) || (ebytes == 2)) || (ebytes == 4)) || (ebytes == 8)) && ((0 ≤b d) && ((d ≤b 31) && (((((alignment == 1) || (alignment == 4)) || (alignment == 8)) || (alignment == 16)) || (alignment == 32))))))))) "src/instrs32.sail:39107.149-39107.150"
      (execute_aarch32_instrs_VST4_m_Op_A_txt alignment d d2 d3 d4 ebytes elements m n register_index wback))
  else (pure ())

def decode_aarch32_instrs_VSTM_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (D : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:39157.29-39157.30"
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((P == 1#1) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "VSTR")) : SailM Unit)
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
      (execute_aarch32_instrs_VSTM_Op_A_txt add d imm32 n regs single_regs wback))
  else (pure ())

def decode_aarch32_instrs_VSTM_A2enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (D : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:39205.29-39205.30"
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((P == 1#1) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "VSTR")) : SailM Unit)
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
      (execute_aarch32_instrs_VSTM_Op_A_txt add d imm32 n regs single_regs wback))
  else (pure ())

def decode_aarch32_instrs_VSTM_T1enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (D : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((P == 1#1) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "VSTR")) : SailM Unit)
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
      (execute_aarch32_instrs_VSTM_Op_A_txt add d imm32 n regs single_regs wback))
  else (pure ())

def decode_aarch32_instrs_VSTM_T2enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (D : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      if (((P == 1#1) && (W == 0#1)) : Bool)
      then (sailThrow ((Error_See "VSTR")) : SailM Unit)
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
      (execute_aarch32_instrs_VSTM_Op_A_txt add d imm32 n regs single_regs wback))
  else (pure ())

def decode_aarch32_instrs_VSTR_A1enc_A_txt (cond : (BitVec 4)) (U : (BitVec 1)) (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (imm8 : (BitVec 8)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:39367.29-39367.30"
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
      if ((←((pure (n == 15)) <&&> (do
           (pure (bne (← (CurrentInstrSet ())) InstrSet_A32))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let d := d
      (execute_aarch32_instrs_VSTR_Op_A_txt add d esize imm32 n))
  else (pure ())

def decode_aarch32_instrs_VSTR_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (Rn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (imm8 : (BitVec 8)) : SailM Unit := do
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
      if ((←((pure (n == 15)) <&&> (do
           (pure (bne (← (CurrentInstrSet ())) InstrSet_A32))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let d := d
      (execute_aarch32_instrs_VSTR_Op_A_txt add d esize imm32 n))
  else (pure ())

def decode_aarch32_instrs_VSUB_f_A1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VSUB_f_Op_A_txt advsimd d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VSUB_f_A2enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:39545.29-39545.30"
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
      (execute_aarch32_instrs_VSUB_f_Op_A_txt advsimd d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VSUB_f_T1enc_A_txt (D : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VSUB_f_Op_A_txt advsimd d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VSUB_f_T2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VSUB_f_Op_A_txt advsimd d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VSUBHN_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VSUBHN_Op_A_txt d elements esize m n))
  else (pure ())

def decode_aarch32_instrs_VSUBHN_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VSUBHN_Op_A_txt d elements esize m n))
  else (pure ())

def decode_aarch32_instrs_VSUB_i_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VSUB_i_Op_A_txt d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VSUB_i_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VSUB_i_Op_A_txt d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VSUBL_A1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      let is_vsubw : Bool := (op == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VSUBL_Op_A_txt d elements esize is_vsubw m n is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VSUBL_T1enc_A_txt (U : (BitVec 1)) (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (op : (BitVec 1)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      let is_vsubw : Bool := (op == 1#1)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VSUBL_Op_A_txt d elements esize is_vsubw m n is_unsigned))
  else (pure ())

def decode_aarch32_instrs_VSWP_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size != 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VSWP_Op_A_txt d m regs))
  else (pure ())

def decode_aarch32_instrs_VSWP_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((size != 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      let regs :=
        if ((Q == 0#1) : Bool)
        then 1
        else 2
      (execute_aarch32_instrs_VSWP_Op_A_txt d m regs))
  else (pure ())

def decode_aarch32_instrs_VTBL_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (len : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let is_vtbl : Bool := (op == 0#1)
      let length := ((BitVec.toNat len) +i 1)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      if (((n +i length) >b 32) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VTBL_Op_A_txt d is_vtbl length m n))
  else (pure ())

def decode_aarch32_instrs_VTBL_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (len : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let is_vtbl : Bool := (op == 0#1)
      let length := ((BitVec.toNat len) +i 1)
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      if (((n +i length) >b 32) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VTBL_Op_A_txt d is_vtbl length m n))
  else (pure ())

def decode_aarch32_instrs_VTRN_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VTRN_Op_A_txt d elements esize m regs))
  else (pure ())

def decode_aarch32_instrs_VTRN_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_VTRN_Op_A_txt d elements esize m regs))
  else (pure ())

def decode_aarch32_instrs_VTST_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size == 0b11#2) : Bool)
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
      (execute_aarch32_instrs_VTST_Op_A_txt d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VTST_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size == 0b11#2) : Bool)
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
      (execute_aarch32_instrs_VTST_Op_A_txt d elements esize m n regs))
  else (pure ())

def decode_aarch32_instrs_VUZP_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) || ((Q == 0#1) && (size == 0b10#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let quadword_operation : Bool := (Q == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VUZP_Op_A_txt d esize m quadword_operation))
  else (pure ())

def decode_aarch32_instrs_VUZP_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) || ((Q == 0#1) && (size == 0b10#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let quadword_operation : Bool := (Q == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VUZP_Op_A_txt d esize m quadword_operation))
  else (pure ())

def decode_aarch32_instrs_VZIP_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) || ((Q == 0#1) && (size == 0b10#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let quadword_operation : Bool := (Q == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VZIP_Op_A_txt d esize m quadword_operation))
  else (pure ())

def decode_aarch32_instrs_VZIP_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if (((size == 0b11#2) || ((Q == 0#1) && (size == 0b10#2))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let quadword_operation : Bool := (Q == 1#1)
      let esize := (Int.shiftl 8 (BitVec.toNat size))
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_VZIP_Op_A_txt d esize m quadword_operation))
  else (pure ())

def decode_aarch32_instrs_WFE_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:40507.29-40507.30"
      (execute_aarch32_instrs_WFE_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_WFE_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (execute_aarch32_instrs_WFE_Op_A_txt ())
  else (pure ())

def decode_aarch32_instrs_WFE_T2enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (execute_aarch32_instrs_WFE_Op_A_txt ())
  else (pure ())

def decode_aarch32_instrs_WFI_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:40578.29-40578.30"
      (execute_aarch32_instrs_WFI_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_WFI_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (execute_aarch32_instrs_WFI_Op_A_txt ())
  else (pure ())

def decode_aarch32_instrs_WFI_T2enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (execute_aarch32_instrs_WFI_Op_A_txt ())
  else (pure ())

def decode_aarch32_instrs_YIELD_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:40636.29-40636.30"
      (pure (execute_aarch32_instrs_YIELD_Op_A_txt ())))
  else (pure ())

def decode_aarch32_instrs_YIELD_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (pure (execute_aarch32_instrs_YIELD_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_YIELD_T2enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (pure (execute_aarch32_instrs_YIELD_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_CPS_A1enc_AS_txt (imod : (BitVec 2)) (M : (BitVec 1)) (A : (BitVec 1)) (I : (BitVec 1)) (F : (BitVec 1)) (mode : (BitVec 5)) : SailM Unit := do
  if (((mode != 0b00000#5) && (M == 0#1)) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if (((((BitVec.join1 [(BitVec.access imod 1)]) == 1#1) && (((A +++ I) +++ F) == 0b000#3)) || (((BitVec.join1 [(BitVec.access imod 1)]) == 0#1) && (((A +++ I) +++ F) != 0b000#3))) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  let enable : Bool := (imod == 0b10#2)
  let disable : Bool := (imod == 0b11#2)
  let changemode : Bool := (M == 1#1)
  let affectA : Bool := (A == 1#1)
  let affectI : Bool := (I == 1#1)
  let affectF : Bool := (F == 1#1)
  if ((((imod == 0b00#2) && (M == 0#1)) || (imod == 0b01#2)) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  (execute_aarch32_instrs_CPS_OpT_AS_txt affectA affectF affectI changemode disable enable mode)

def decode_aarch32_instrs_CPS_T1enc_AS_txt (im : (BitVec 1)) (A : (BitVec 1)) (I : (BitVec 1)) (F : (BitVec 1)) : SailM Unit := do
  let mode ← (( do (undefined_bitvector 5) ) : SailM (BitVec 5) )
  if ((((A +++ I) +++ F) == 0b000#3) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  let mode := mode
  let enable : Bool := (im == 0#1)
  let disable : Bool := (im == 1#1)
  let changemode : Bool := false
  let affectA : Bool := (A == 1#1)
  let affectI : Bool := (I == 1#1)
  let affectF : Bool := (F == 1#1)
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  (execute_aarch32_instrs_CPS_OpT_AS_txt affectA affectF affectI changemode disable enable mode)

def decode_aarch32_instrs_CPS_T2enc_AS_txt (imod : (BitVec 2)) (M : (BitVec 1)) (A : (BitVec 1)) (I : (BitVec 1)) (F : (BitVec 1)) (mode : (BitVec 5)) : SailM Unit := do
  if (((imod == 0b00#2) && (M == 0#1)) : Bool)
  then (sailThrow ((Error_See "Hint instructions")) : SailM Unit)
  else (pure ())
  if (((mode != 0b00000#5) && (M == 0#1)) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if (((((BitVec.join1 [(BitVec.access imod 1)]) == 1#1) && (((A +++ I) +++ F) == 0b000#3)) || (((BitVec.join1 [(BitVec.access imod 1)]) == 0#1) && (((A +++ I) +++ F) != 0b000#3))) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  let enable : Bool := (imod == 0b10#2)
  let disable : Bool := (imod == 0b11#2)
  let changemode : Bool := (M == 1#1)
  let affectA : Bool := (A == 1#1)
  let affectI : Bool := (I == 1#1)
  let affectF : Bool := (F == 1#1)
  if ((←((pure (imod == 0b01#2)) <||> (do
       (InITBlock ())))) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  (execute_aarch32_instrs_CPS_OpT_AS_txt affectA affectF affectI changemode disable enable mode)

def decode_aarch32_instrs_ERET_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:40855.29-40855.30"
      (execute_aarch32_instrs_ERET_Op_AS_txt ()))
  else (pure ())

def decode_aarch32_instrs_ERET_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((←((InITBlock ()) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ERET_Op_AS_txt ()))
  else (pure ())

def decode_aarch32_instrs_HVC_A1enc_A_txt (cond : (BitVec 4)) (imm12 : (BitVec 12)) (imm4 : (BitVec 4)) : SailM Unit := do
  sail_assert (cond != 0b1111#4) "src/instrs32.sail:40919.25-40919.26"
  if ((cond != 0b1110#4) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  let imm16 : (BitVec 16) := (imm12 +++ imm4)
  (execute_aarch32_instrs_HVC_Op_AS_txt imm16)

def decode_aarch32_instrs_HVC_T1enc_A_txt (imm4 : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let imm16 : (BitVec 16) := (imm4 +++ imm12)
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  (execute_aarch32_instrs_HVC_Op_AS_txt imm16)

def decode_aarch32_instrs_LDM_e_A1enc_AS_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 15)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:40995.29-40995.30"
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 15) := register_list
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := (U == 1#1)
      let wordhigher : Bool := (P == U)
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((wback && ((BitVec.join1 [(BitVec.access registers n)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDM_e_Op_AS_txt increment_name n registers wback wordhigher))
  else (pure ())

def decode_aarch32_instrs_LDM_u_A1enc_AS_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 15)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:41055.29-41055.30"
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 15) := register_list
      let increment_name : Bool := (U == 1#1)
      let wordhigher : Bool := (P == U)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDM_u_Op_AS_txt increment_name n registers wordhigher))
  else (pure ())

def decode_aarch32_instrs_MRS_A1enc_AS_txt (cond : (BitVec 4)) (R : (BitVec 1)) (Rd : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:41109.29-41109.30"
      let d := (BitVec.toNat Rd)
      let read_spsr : Bool := (R == 1#1)
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MRS_Op_AS_txt d read_spsr))
  else (pure ())

def decode_aarch32_instrs_MRS_T1enc_AS_txt (R : (BitVec 1)) (Rd : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let read_spsr : Bool := (R == 1#1)
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MRS_Op_AS_txt d read_spsr))
  else (pure ())

def decode_aarch32_instrs_MRS_br_A1enc_AS_txt (cond : (BitVec 4)) (R : (BitVec 1)) (M1 : (BitVec 4)) (Rd : (BitVec 4)) (M : (BitVec 1)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:41246.29-41246.30"
      let d := (BitVec.toNat Rd)
      let read_spsr : Bool := (R == 1#1)
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let SYSm : (BitVec 5) := (M +++ M1)
      (execute_aarch32_instrs_MRS_br_Op_AS_txt SYSm d read_spsr))
  else (pure ())

def decode_aarch32_instrs_MRS_br_T1enc_AS_txt (R : (BitVec 1)) (M1 : (BitVec 4)) (Rd : (BitVec 4)) (M : (BitVec 1)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let d := (BitVec.toNat Rd)
      let read_spsr : Bool := (R == 1#1)
      if ((d == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let SYSm : (BitVec 5) := (M +++ M1)
      (execute_aarch32_instrs_MRS_br_Op_AS_txt SYSm d read_spsr))
  else (pure ())

def decode_aarch32_instrs_MSR_br_A1enc_AS_txt (cond : (BitVec 4)) (R : (BitVec 1)) (M1 : (BitVec 4)) (M : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:41390.29-41390.30"
      let n := (BitVec.toNat Rn)
      let write_spsr : Bool := (R == 1#1)
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let SYSm : (BitVec 5) := (M +++ M1)
      (execute_aarch32_instrs_MSR_br_Op_AS_txt SYSm n write_spsr))
  else (pure ())

def decode_aarch32_instrs_MSR_br_T1enc_AS_txt (R : (BitVec 1)) (Rn : (BitVec 4)) (M1 : (BitVec 4)) (M : (BitVec 1)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := (BitVec.toNat Rn)
      let write_spsr : Bool := (R == 1#1)
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let SYSm : (BitVec 5) := (M +++ M1)
      (execute_aarch32_instrs_MSR_br_Op_AS_txt SYSm n write_spsr))
  else (pure ())

def decode_aarch32_instrs_MSR_i_A1enc_AS_txt (cond : (BitVec 4)) (R : (BitVec 1)) (mask : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:41463.29-41463.30"
      if (((mask == 0b0000#4) && (R == 0#1)) : Bool)
      then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
      else (pure ())
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      let write_spsr : Bool := (R == 1#1)
      if ((mask == 0b0000#4) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MSR_i_Op_AS_txt imm32 mask write_spsr))
  else (pure ())

def decode_aarch32_instrs_MSR_r_A1enc_AS_txt (cond : (BitVec 4)) (R : (BitVec 1)) (mask : (BitVec 4)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:41510.29-41510.30"
      let n := (BitVec.toNat Rn)
      let write_spsr : Bool := (R == 1#1)
      if ((mask == 0b0000#4) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MSR_r_Op_AS_txt mask n write_spsr))
  else (pure ())

def decode_aarch32_instrs_MSR_r_T1enc_AS_txt (R : (BitVec 1)) (Rn : (BitVec 4)) (mask : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := (BitVec.toNat Rn)
      let write_spsr : Bool := (R == 1#1)
      if ((mask == 0b0000#4) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_MSR_r_Op_AS_txt mask n write_spsr))
  else (pure ())

def decode_aarch32_instrs_RFE_A1enc_AS_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := (BitVec.toNat Rn)
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := (U == 1#1)
      let wordhigher : Bool := (P == U)
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_RFE_Op_AS_txt increment_name n wback wordhigher))
  else (pure ())

def decode_aarch32_instrs_RFE_T1enc_AS_txt (W : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := (BitVec.toNat Rn)
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := false
      let wordhigher : Bool := false
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((InITBlock ()) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_RFE_Op_AS_txt increment_name n wback wordhigher))
  else (pure ())

def decode_aarch32_instrs_RFE_T2enc_AS_txt (W : (BitVec 1)) (Rn : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let n := (BitVec.toNat Rn)
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := true
      let wordhigher : Bool := false
      if ((n == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((←((InITBlock ()) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_RFE_Op_AS_txt increment_name n wback wordhigher))
  else (pure ())

def decode_aarch32_instrs_SMC_A1enc_AS_txt (cond : (BitVec 4)) (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:41716.29-41716.30"
      (execute_aarch32_instrs_SMC_Op_AS_txt ()))
  else (pure ())

def decode_aarch32_instrs_SMC_T1enc_AS_txt (imm4 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((←((InITBlock ()) <&&> (do
           (pure (! (← (LastInITBlock ()))))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_SMC_Op_AS_txt ()))
  else (pure ())

def decode_aarch32_instrs_SRS_A1enc_AS_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (mode : (BitVec 5)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := (U == 1#1)
      let wordhigher : Bool := (P == U)
      (execute_aarch32_instrs_SRS_OpA_AS_txt increment_name mode wback wordhigher))
  else (pure ())

def decode_aarch32_instrs_SRS_T1enc_AS_txt (W : (BitVec 1)) (mode : (BitVec 5)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := false
      let wordhigher : Bool := false
      (execute_aarch32_instrs_SRS_OpT_AS_txt increment_name mode wback wordhigher))
  else (pure ())

def decode_aarch32_instrs_SRS_T2enc_AS_txt (W : (BitVec 1)) (mode : (BitVec 5)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let wback : Bool := (W == 1#1)
      let increment_name : Bool := true
      let wordhigher : Bool := false
      (execute_aarch32_instrs_SRS_OpT_AS_txt increment_name mode wback wordhigher))
  else (pure ())

def decode_aarch32_instrs_STM_u_A1enc_AS_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (Rn : (BitVec 4)) (register_list : (BitVec 16)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:41928.29-41928.30"
      let n := (BitVec.toNat Rn)
      let registers : (BitVec 16) := register_list
      let increment_name : Bool := (U == 1#1)
      let wordhigher : Bool := (P == U)
      if (((n == 15) || ((BitCount registers) <b 1)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STM_u_Op_AS_txt increment_name n registers wordhigher))
  else (pure ())

def decode_aarch32_instrs_VMRS_A1enc_AS_txt (cond : (BitVec 4)) (reg : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:41998.29-41998.30"
      let t := (BitVec.toNat Rt)
      if ((! (let b__0 := reg
           if (((Sail.BitVec.extractLsb b__0 3 1) == (0b000#3 : (BitVec 3))) : Bool)
           then true
           else
             (if ((b__0 == (0x5#4 : (BitVec 4))) : Bool)
             then true
             else
               (if (((Sail.BitVec.extractLsb b__0 3 1) == (0b011#3 : (BitVec 3))) : Bool)
               then true
               else
                 (if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                 then true
                 else false))) : Bool)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((t == 15) && (reg != 0b0001#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VMRS_Op_AS_txt reg t))
  else (pure ())

def decode_aarch32_instrs_VMRS_T1enc_AS_txt (reg : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      if ((! (let b__0 := reg
           if (((Sail.BitVec.extractLsb b__0 3 1) == (0b000#3 : (BitVec 3))) : Bool)
           then true
           else
             (if ((b__0 == (0x5#4 : (BitVec 4))) : Bool)
             then true
             else
               (if (((Sail.BitVec.extractLsb b__0 3 1) == (0b011#3 : (BitVec 3))) : Bool)
               then true
               else
                 (if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                 then true
                 else false))) : Bool)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((t == 15) && (reg != 0b0001#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VMRS_Op_AS_txt reg t))
  else (pure ())

def decode_aarch32_instrs_VMSR_A1enc_AS_txt (cond : (BitVec 4)) (reg : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:42089.29-42089.30"
      let t := (BitVec.toNat Rt)
      if (((! (let b__0 := reg
             if (((Sail.BitVec.extractLsb b__0 3 1) == (0b000#3 : (BitVec 3))) : Bool)
             then true
             else false : Bool)) && (reg != 0b1000#4)) : Bool)
      then
        (do
          let c ← (( do (ConstrainUnpredictable Unpredictable_VMSR) ) : SailM Constraint )
          sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs32.sail:42096.62-42096.63"
          match c with
          | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
          | .Constraint_NOP => (EndOfInstruction ())
          | _ => (pure ()))
      else (pure ())
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VMSR_Op_AS_txt reg t))
  else (pure ())

def decode_aarch32_instrs_VMSR_T1enc_AS_txt (reg : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      if (((! (let b__0 := reg
             if (((Sail.BitVec.extractLsb b__0 3 1) == (0b000#3 : (BitVec 3))) : Bool)
             then true
             else false : Bool)) && (reg != 0b1000#4)) : Bool)
      then
        (do
          let c ← (( do (ConstrainUnpredictable Unpredictable_VMSR) ) : SailM Constraint )
          sail_assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "src/instrs32.sail:42137.62-42137.63"
          match c with
          | .Constraint_UNDEF => (sailThrow ((Error_Undefined ())) : SailM Unit)
          | .Constraint_NOP => (EndOfInstruction ())
          | _ => (pure ()))
      else (pure ())
      if ((t == 15) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_VMSR_Op_AS_txt reg t))
  else (pure ())

def decode_aarch32_instrs_AESD_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveAESExt ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_AESD_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_AESD_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (← (HaveAESExt ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_AESD_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_AESE_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveAESExt ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_AESE_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_AESE_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (← (HaveAESExt ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_AESE_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_AESIMC_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveAESExt ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_AESIMC_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_AESIMC_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (← (HaveAESExt ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_AESIMC_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_AESMC_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveAESExt ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_AESMC_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_AESMC_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (← (HaveAESExt ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b00#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_AESMC_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_CRC32_A1enc_A_txt (cond : (BitVec 4)) (sz : (BitVec 2)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (C : (BitVec 1)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:42477.29-42477.30"
      if ((! (← (HaveCRCExt ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let size := (Int.shiftl 8 (BitVec.toNat sz))
      let crc32c : Bool := (C == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((size == 64) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((cond != 0b1110#4) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_CRC32_Op_A_txt crc32c d m n size))
  else (pure ())

def decode_aarch32_instrs_CRC32_T1enc_A_txt (C : (BitVec 1)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (sz : (BitVec 2)) (Rm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (← (HaveCRCExt ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat Rd)
      let n := (BitVec.toNat Rn)
      let m := (BitVec.toNat Rm)
      let size := (Int.shiftl 8 (BitVec.toNat sz))
      let crc32c : Bool := (C == 1#1)
      if ((((d == 15) || (n == 15)) || (m == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((size == 64) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_CRC32_Op_A_txt crc32c d m n size))
  else (pure ())

def decode_aarch32_instrs_DCPS1_T1enc_A_txt (_ : Unit) : SailM Unit := do
  (execute_aarch32_instrs_DCPS1_Op_A_txt ())

def decode_aarch32_instrs_DCPS2_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((! (HaveEL EL2)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch32_instrs_DCPS2_Op_A_txt ())

def decode_aarch32_instrs_DCPS3_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((! (HaveEL EL3)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch32_instrs_DCPS3_Op_A_txt ())

def decode_aarch32_instrs_HLT_A1enc_A_txt (cond : (BitVec 4)) (imm12 : (BitVec 12)) (imm4 : (BitVec 4)) : SailM Unit := do
  sail_assert (cond != 0b1111#4) "src/instrs32.sail:42755.25-42755.26"
  if ((←((pure ((_get_EDSCR_Type_HDE (← (EDSCR_read ()))) == 0#1)) <||> (do
       (pure (! (← (HaltingAllowed ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((cond != 0b1110#4) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  (execute_aarch32_instrs_HLT_Op_A_txt ())

def decode_aarch32_instrs_HLT_T1enc_A_txt (imm6 : (BitVec 6)) : SailM Unit := do
  if ((←((pure ((_get_EDSCR_Type_HDE (← (EDSCR_read ()))) == 0#1)) <||> (do
       (pure (! (← (HaltingAllowed ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  (execute_aarch32_instrs_HLT_Op_A_txt ())

def decode_aarch32_instrs_LDA_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:42802.29-42802.30"
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDA_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_LDA_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDA_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_LDAB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:42864.29-42864.30"
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDAB_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_LDAB_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDAB_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_LDAEX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:42927.29-42927.30"
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDAEX_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_LDAEX_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDAEX_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_LDAEXB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:42990.29-42990.30"
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDAEXB_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_LDAEXB_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDAEXB_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_LDAEXD_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:43057.29-43057.30"
      let t := (BitVec.toNat Rt)
      let t2 := (t +i 1)
      let n := (BitVec.toNat Rn)
      if (((((BitVec.join1 [(BitVec.access Rt 0)]) == 1#1) || (t2 == 15)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDAEXD_Op_A_txt n t t2))
  else (pure ())

def decode_aarch32_instrs_LDAEXD_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rt2 : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let t2 := (BitVec.toNat Rt2)
      let n := (BitVec.toNat Rn)
      if (((((t == 15) || (t2 == 15)) || (t == t2)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDAEXD_Op_A_txt n t t2))
  else (pure ())

def decode_aarch32_instrs_LDAEXH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:43123.29-43123.30"
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDAEXH_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_LDAEXH_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDAEXH_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_LDAH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:43185.29-43185.30"
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDAH_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_LDAH_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_LDAH_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_SEVL_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:43243.29-43243.30"
      (execute_aarch32_instrs_SEVL_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_SEVL_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (execute_aarch32_instrs_SEVL_Op_A_txt ())
  else (pure ())

def decode_aarch32_instrs_SEVL_T2enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (execute_aarch32_instrs_SEVL_Op_A_txt ())
  else (pure ())

def decode_aarch32_instrs_SHA1C_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveSHA1Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((Q != 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1C_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHA1C_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (← (HaveSHA1Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((Q != 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1C_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHA1H_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveSHA1Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b10#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1H_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_SHA1H_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (← (HaveSHA1Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b10#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1H_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_SHA1M_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveSHA1Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((Q != 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1M_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHA1M_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (← (HaveSHA1Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((Q != 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1M_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHA1P_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveSHA1Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((Q != 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1P_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHA1P_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (← (HaveSHA1Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((Q != 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1P_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHA1SU0_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveSHA1Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((Q != 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1SU0_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHA1SU0_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (← (HaveSHA1Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((Q != 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1SU0_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHA1SU1_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveSHA1Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b10#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1SU1_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_SHA1SU1_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (← (HaveSHA1Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b10#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA1SU1_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_SHA256H_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveSHA256Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((Q != 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA256H_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHA256H_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (← (HaveSHA256Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((Q != 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA256H_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHA256H2_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveSHA256Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((Q != 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA256H2_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHA256H2_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (← (HaveSHA256Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((Q != 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA256H2_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHA256SU0_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveSHA256Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b10#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA256SU0_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_SHA256SU0_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (← (HaveSHA256Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((size != 0b10#2) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA256SU0_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_SHA256SU1_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveSHA256Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((Q != 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA256SU1_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_SHA256SU1_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if ((! (← (HaveSHA256Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if ((Q != 1#1) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (D +++ Vd))
      let n := (BitVec.toNat (N +++ Vn))
      let m := (BitVec.toNat (M +++ Vm))
      (execute_aarch32_instrs_SHA256SU1_Op_A_txt d m n))
  else (pure ())

def decode_aarch32_instrs_STL_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:44146.29-44146.30"
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STL_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_STL_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STL_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_STLB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:44208.29-44208.30"
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STLB_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_STLB_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STLB_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_STLEX_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:44275.29-44275.30"
      let d := (BitVec.toNat Rd)
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((d == n) || (d == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STLEX_Op_A_txt d n t))
  else (pure ())

def decode_aarch32_instrs_STLEX_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rd : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_STLEX_Op_A_txt d n t))
  else (pure ())

def decode_aarch32_instrs_STLEXB_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:44352.29-44352.30"
      let d := (BitVec.toNat Rd)
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((d == n) || (d == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STLEXB_Op_A_txt d n t))
  else (pure ())

def decode_aarch32_instrs_STLEXB_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rd : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_STLEXB_Op_A_txt d n t))
  else (pure ())

def decode_aarch32_instrs_STLEXD_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:44433.29-44433.30"
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
      (execute_aarch32_instrs_STLEXD_Op_A_txt d n t t2))
  else (pure ())

def decode_aarch32_instrs_STLEXD_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rt2 : (BitVec 4)) (Rd : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_STLEXD_Op_A_txt d n t t2))
  else (pure ())

def decode_aarch32_instrs_STLEXH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rd : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:44509.29-44509.30"
      let d := (BitVec.toNat Rd)
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if ((((d == 15) || (t == 15)) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      if (((d == n) || (d == t)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STLEXH_Op_A_txt d n t))
  else (pure ())

def decode_aarch32_instrs_STLEXH_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) (Rd : (BitVec 4)) : SailM Unit := do
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
      (execute_aarch32_instrs_STLEXH_Op_A_txt d n t))
  else (pure ())

def decode_aarch32_instrs_STLH_A1enc_A_txt (cond : (BitVec 4)) (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:44581.29-44581.30"
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STLH_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_STLH_T1enc_A_txt (Rn : (BitVec 4)) (Rt : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      let t := (BitVec.toNat Rt)
      let n := (BitVec.toNat Rn)
      if (((t == 15) || (n == 15)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_STLH_Op_A_txt n t))
  else (pure ())

def decode_aarch32_instrs_VCVTA_asimd_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (RM : (BitVec 2)) (op : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let rounding ← (( do (FPDecodeRM RM) ) : SailM FPRounding )
  let is_unsigned : Bool := (op == 1#1)
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
  (execute_aarch32_instrs_VCVTA_asimd_Op_A_txt d elements esize m regs rounding is_unsigned)

def decode_aarch32_instrs_VCVTA_asimd_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (RM : (BitVec 2)) (op : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let rounding ← (( do (FPDecodeRM RM) ) : SailM FPRounding )
  let is_unsigned : Bool := (op == 1#1)
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
  (execute_aarch32_instrs_VCVTA_asimd_Op_A_txt d elements esize m regs rounding is_unsigned)

def decode_aarch32_instrs_VCVTA_vfp_A1enc_A_txt (D : (BitVec 1)) (RM : (BitVec 2)) (Vd : (BitVec 4)) (size : (BitVec 2)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let rounding ← (( do (FPDecodeRM RM) ) : SailM FPRounding )
  let is_unsigned : Bool := (op == 0#1)
  let d := (BitVec.toNat (Vd +++ D))
  let esize : Nat := 16
  let m ← (( do (undefined_range 0 31) ) : SailM Nat )
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
  let m := m
  let esize := esize
  (execute_aarch32_instrs_VCVTA_vfp_Op_A_txt d esize m rounding is_unsigned)

def decode_aarch32_instrs_VCVTA_vfp_T1enc_A_txt (D : (BitVec 1)) (RM : (BitVec 2)) (Vd : (BitVec 4)) (size : (BitVec 2)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let rounding ← (( do (FPDecodeRM RM) ) : SailM FPRounding )
  let is_unsigned : Bool := (op == 0#1)
  let d := (BitVec.toNat (Vd +++ D))
  let esize : Nat := 16
  let m ← (( do (undefined_range 0 31) ) : SailM Nat )
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
  let m := m
  let esize := esize
  (execute_aarch32_instrs_VCVTA_vfp_Op_A_txt d esize m rounding is_unsigned)

def decode_aarch32_instrs_VMAXNM_A1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let maximum : Bool := (op == 0#1)
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
  (execute_aarch32_instrs_VMAXNM_Op_A_txt advsimd d elements esize m maximum n regs)

def decode_aarch32_instrs_VMAXNM_A2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let elements ← (( do (undefined_int ()) ) : SailM Int )
  let regs ← (( do (undefined_int ()) ) : SailM Int )
  if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let regs := regs
  let elements := elements
  let advsimd : Bool := false
  let maximum : Bool := (op == 0#1)
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
  (execute_aarch32_instrs_VMAXNM_Op_A_txt advsimd d elements esize m maximum n regs)

def decode_aarch32_instrs_VMAXNM_T1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((sz == 1#1) && (! (HaveFP16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let maximum : Bool := (op == 0#1)
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
  (execute_aarch32_instrs_VMAXNM_Op_A_txt advsimd d elements esize m maximum n regs)

def decode_aarch32_instrs_VMAXNM_T2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let elements ← (( do (undefined_int ()) ) : SailM Int )
  let regs ← (( do (undefined_int ()) ) : SailM Int )
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let regs := regs
  let elements := elements
  let advsimd : Bool := false
  let maximum : Bool := (op == 0#1)
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
  (execute_aarch32_instrs_VMAXNM_Op_A_txt advsimd d elements esize m maximum n regs)

def decode_aarch32_instrs_VRINTA_asimd_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 3)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((BitVec.join1 [(BitVec.access op 2)]) != (BitVec.join1 [(BitVec.access op 0)])) : Bool)
  then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let rounding ← (( do (FPDecodeRM ((BitVec.join1 [(BitVec.access op 2)]) +++ (Complement.complement (BitVec.join1 [(BitVec.access op 1)])))) ) : SailM FPRounding )
  let exact : Bool := false
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
  (execute_aarch32_instrs_VRINTA_asimd_Op_A_txt d elements esize exact m regs rounding)

def decode_aarch32_instrs_VRINTA_asimd_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (op : (BitVec 3)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((BitVec.join1 [(BitVec.access op 2)]) != (BitVec.join1 [(BitVec.access op 0)])) : Bool)
  then (sailThrow ((Error_See "Related encodings")) : SailM Unit)
  else (pure ())
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let rounding ← (( do (FPDecodeRM ((BitVec.join1 [(BitVec.access op 2)]) +++ (Complement.complement (BitVec.join1 [(BitVec.access op 1)])))) ) : SailM FPRounding )
  let exact : Bool := false
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
  (execute_aarch32_instrs_VRINTA_asimd_Op_A_txt d elements esize exact m regs rounding)

def decode_aarch32_instrs_VRINTA_vfp_A1enc_A_txt (D : (BitVec 1)) (RM : (BitVec 2)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let rounding ← (( do (FPDecodeRM RM) ) : SailM FPRounding )
  let exact : Bool := false
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
  (execute_aarch32_instrs_VRINTA_vfp_Op_A_txt d esize exact m rounding)

def decode_aarch32_instrs_VRINTA_vfp_T1enc_A_txt (D : (BitVec 1)) (RM : (BitVec 2)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let rounding ← (( do (FPDecodeRM RM) ) : SailM FPRounding )
  let exact : Bool := false
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
  (execute_aarch32_instrs_VRINTA_vfp_Op_A_txt d esize exact m rounding)

def decode_aarch32_instrs_VRINTX_asimd_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let rounding : FPRounding := FPRounding_TIEEVEN
  let exact : Bool := true
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
  (execute_aarch32_instrs_VRINTX_asimd_Op_A_txt d elements esize exact m regs rounding)

def decode_aarch32_instrs_VRINTX_asimd_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let rounding : FPRounding := FPRounding_TIEEVEN
  let exact : Bool := true
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
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  (execute_aarch32_instrs_VRINTX_asimd_Op_A_txt d elements esize exact m regs rounding)

def decode_aarch32_instrs_VRINTX_vfp_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:45469.29-45469.30"
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let exact : Bool := true
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
      (execute_aarch32_instrs_VRINTX_vfp_Op_A_txt d esize exact m))
  else (pure ())

def decode_aarch32_instrs_VRINTX_vfp_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      let exact : Bool := true
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
      (execute_aarch32_instrs_VRINTX_vfp_Op_A_txt d esize exact m))
  else (pure ())

def decode_aarch32_instrs_VRINTZ_asimd_A1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let rounding : FPRounding := FPRounding_ZERO
  let exact : Bool := false
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
  (execute_aarch32_instrs_VRINTZ_asimd_Op_A_txt d elements esize exact m regs rounding)

def decode_aarch32_instrs_VRINTZ_asimd_T1enc_A_txt (D : (BitVec 1)) (size : (BitVec 2)) (Vd : (BitVec 4)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((size == 0b01#2) && (! (HaveFP16Ext ()))) || ((size == 0b00#2) || (size == 0b11#2))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let rounding : FPRounding := FPRounding_ZERO
  let exact : Bool := false
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
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  (execute_aarch32_instrs_VRINTZ_asimd_Op_A_txt d elements esize exact m regs rounding)

def decode_aarch32_instrs_VRINTZ_vfp_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:45698.29-45698.30"
      if (((size == 0b00#2) || ((size == 0b01#2) && (! (HaveFP16Ext ())))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      if (((size == 0b01#2) && (cond != 0b1110#4)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      let rounding ← (( do
        if ((op == 1#1) : Bool)
        then (pure FPRounding_ZERO)
        else (FPRoundingMode (← (FPSCR_read ()))) ) : SailM FPRounding )
      let exact : Bool := false
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
      (execute_aarch32_instrs_VRINTZ_vfp_Op_A_txt d esize exact m rounding))
  else (pure ())

def decode_aarch32_instrs_VRINTZ_vfp_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (size : (BitVec 2)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
      let rounding ← (( do
        if ((op == 1#1) : Bool)
        then (pure FPRounding_ZERO)
        else (FPRoundingMode (← (FPSCR_read ()))) ) : SailM FPRounding )
      let exact : Bool := false
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
      (execute_aarch32_instrs_VRINTZ_vfp_Op_A_txt d esize exact m rounding))
  else (pure ())

def decode_aarch32_instrs_VSEL_A1enc_A_txt (D : (BitVec 1)) (cc : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
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
  let cond : (BitVec 4) := ((cc +++ ((BitVec.join1 [(BitVec.access cc 1)]) ^^^ (BitVec.join1 [(BitVec.access cc 0)]))) +++ 0#1)
  (execute_aarch32_instrs_VSEL_Op_A_txt cond d esize m n)

def decode_aarch32_instrs_VSEL_T1enc_A_txt (D : (BitVec 1)) (cc : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
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
  let cond : (BitVec 4) := ((cc +++ ((BitVec.join1 [(BitVec.access cc 1)]) ^^^ (BitVec.join1 [(BitVec.access cc 0)]))) +++ 0#1)
  (execute_aarch32_instrs_VSEL_Op_A_txt cond d esize m n)

def decode_aarch32_instrs_SETPAN_A1enc_A_txt (imm1 : (BitVec 1)) : SailM Unit := do
  if ((! (← (HavePANExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let value_name : (BitVec 1) := imm1
  (execute_aarch32_instrs_SETPAN_Op_A_txt value_name)

def decode_aarch32_instrs_SETPAN_T1enc_A_txt (imm1 : (BitVec 1)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((! (← (HavePANExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let value_name : (BitVec 1) := imm1
  (execute_aarch32_instrs_SETPAN_Op_A_txt value_name)

def decode_aarch32_instrs_ESB_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:45997.29-45997.30"
      if ((! (← (HaveRASExt ()))) : Bool)
      then (EndOfInstruction ())
      else (pure ())
      if ((cond != 0b1110#4) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ESB_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_ESB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveRASExt ()))) : Bool)
      then (EndOfInstruction ())
      else (pure ())
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (execute_aarch32_instrs_ESB_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_TSB_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:46053.29-46053.30"
      if ((! (← (HaveSelfHostedTrace ()))) : Bool)
      then (EndOfInstruction ())
      else (pure ())
      if ((cond != 0b1110#4) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (pure (execute_aarch32_instrs_TSB_Op_A_txt ())))
  else (pure ())

def decode_aarch32_instrs_TSB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveSelfHostedTrace ()))) : Bool)
      then (EndOfInstruction ())
      else (pure ())
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (pure (execute_aarch32_instrs_TSB_Op_A_txt ())))
  else (pure ())

def decode_aarch32_instrs_CSDB_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:46109.29-46109.30"
      if ((cond != 0b1110#4) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (pure (execute_aarch32_instrs_CSDB_Op_A_txt ())))
  else (pure ())

def decode_aarch32_instrs_CSDB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (pure (execute_aarch32_instrs_CSDB_Op_A_txt ())))
  else (pure ())

def decode_aarch32_instrs_SSBB_A1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (pure (execute_aarch32_instrs_SSBB_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_SSBB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (pure (execute_aarch32_instrs_SSBB_Op_A_txt ())))
  else (pure ())

def decode_aarch32_instrs_PSSBB_A1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then (pure (execute_aarch32_instrs_PSSBB_Op_A_txt ()))
  else (pure ())

def decode_aarch32_instrs_PSSBB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((← (InITBlock ())) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ())
      (pure (execute_aarch32_instrs_PSSBB_Op_A_txt ())))
  else (pure ())

def decode_aarch32_instrs_VDOT_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (U : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveDOTPExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := (U == 0#1)
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let esize := 32
  let regs :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VDOT_Op_A_txt d esize m n regs is_signed)

def decode_aarch32_instrs_VDOT_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (U : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveDOTPExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := (U == 0#1)
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let esize := 32
  let regs :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VDOT_Op_A_txt d esize m n regs is_signed)

def decode_aarch32_instrs_VDOT_s_A1enc_A_txt (op1 : (BitVec 1)) (D : (BitVec 1)) (op2 : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (U : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveDOTPExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := (U == 0#1)
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (Sail.BitVec.extractLsb Vm 3 0))
  let index := (BitVec.toNat M)
  let esize := 32
  let regs :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VDOT_s_Op_A_txt d esize index m n regs is_signed)

def decode_aarch32_instrs_VDOT_s_T1enc_A_txt (op1 : (BitVec 1)) (D : (BitVec 1)) (op2 : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (U : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveDOTPExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let is_signed : Bool := (U == 0#1)
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (Sail.BitVec.extractLsb Vm 3 0))
  let index := (BitVec.toNat M)
  let esize := 32
  let regs :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VDOT_s_Op_A_txt d esize index m n regs is_signed)

def decode_aarch32_instrs_VJCVT_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  sail_assert (cond != 0b1111#4) "src/instrs32.sail:46459.25-46459.26"
  if ((! (← (HaveFJCVTZSExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((cond != 0b1110#4) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (Vd +++ D))
  let m := (BitVec.toNat (M +++ Vm))
  (execute_aarch32_instrs_VJCVT_Op_A_txt d m)

def decode_aarch32_instrs_VJCVT_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveFJCVTZSExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (Vd +++ D))
  let m := (BitVec.toNat (M +++ Vm))
  (execute_aarch32_instrs_VJCVT_Op_A_txt d m)

def decode_aarch32_instrs_VCMLA_A1enc_A_txt (rot : (BitVec 2)) (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveFCADDExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let esize := (Int.shiftl 16 (BitVec.toNat S))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let elements := (fdiv_int 64 esize)
  let regs :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  sail_assert ((esize == 16) || (esize == 32)) "src/instrs32.sail:46581.41-46581.42"
  (execute_aarch32_instrs_VCMLA_Op_A_txt d elements esize m n regs rot)

def decode_aarch32_instrs_VCMLA_T1enc_A_txt (rot : (BitVec 2)) (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveFCADDExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let esize := (Int.shiftl 16 (BitVec.toNat S))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let elements := (fdiv_int 64 esize)
  let regs :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  sail_assert ((esize == 16) || (esize == 32)) "src/instrs32.sail:46620.41-46620.42"
  (execute_aarch32_instrs_VCMLA_Op_A_txt d elements esize m n regs rot)

def decode_aarch32_instrs_VCMLA_idx_A1enc_A_txt (S : (BitVec 1)) (D : (BitVec 1)) (rot : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveFCADDExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m :=
    if ((S == 1#1) : Bool)
    then (BitVec.toNat (M +++ Vm))
    else (BitVec.toNat Vm)
  let esize := (Int.shiftl 16 (BitVec.toNat S))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let elements := (fdiv_int 64 esize)
  let regs :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  let index :=
    if ((S == 1#1) : Bool)
    then 0
    else (BitVec.toNat M)
  sail_assert ((0 ≤b m) && ((m ≤b 31) && ((esize == 16) || (esize == 32)))) "src/instrs32.sail:46716.64-46716.65"
  (execute_aarch32_instrs_VCMLA_idx_Op_A_txt d elements esize index m n regs rot)

def decode_aarch32_instrs_VCMLA_idx_T1enc_A_txt (S : (BitVec 1)) (D : (BitVec 1)) (rot : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveFCADDExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m :=
    if ((S == 1#1) : Bool)
    then (BitVec.toNat (M +++ Vm))
    else (BitVec.toNat Vm)
  let esize := (Int.shiftl 16 (BitVec.toNat S))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let elements := (fdiv_int 64 esize)
  let regs :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  let index :=
    if ((S == 1#1) : Bool)
    then 0
    else (BitVec.toNat M)
  sail_assert ((0 ≤b m) && ((m ≤b 31) && ((esize == 16) || (esize == 32)))) "src/instrs32.sail:46756.64-46756.65"
  (execute_aarch32_instrs_VCMLA_idx_Op_A_txt d elements esize index m n regs rot)

def decode_aarch32_instrs_VCADD_A1enc_A_txt (rot : (BitVec 1)) (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveFCADDExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let esize := (Int.shiftl 16 (BitVec.toNat S))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let elements := (fdiv_int 64 esize)
  let regs :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  sail_assert ((esize == 16) || (esize == 32)) "src/instrs32.sail:46829.41-46829.42"
  (execute_aarch32_instrs_VCADD_Op_A_txt d elements esize m n regs rot)

def decode_aarch32_instrs_VCADD_T1enc_A_txt (rot : (BitVec 1)) (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveFCADDExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let esize := (Int.shiftl 16 (BitVec.toNat S))
  if (((! (HaveFP16Ext ())) && (esize == 16)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let elements := (fdiv_int 64 esize)
  let regs :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  sail_assert ((esize == 16) || (esize == 32)) "src/instrs32.sail:46868.41-46868.42"
  (execute_aarch32_instrs_VCADD_Op_A_txt d elements esize m n regs rot)

def decode_aarch32_instrs_VFMAL_A1enc_A_txt (S : (BitVec 1)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveFP16MulNoRoundingToFP32Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (N +++ Vn))
    else (BitVec.toNat (Vn +++ N))
  let m :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (M +++ Vm))
    else (BitVec.toNat (Vm +++ M))
  let esize := 32
  let regs :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (S == 1#1)
  sail_assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && (m ≤b 31)))) "src/instrs32.sail:46936.64-46936.65"
  (execute_aarch32_instrs_VFMAL_Op_A_txt Q d datasize esize m n regs sub_op)

def decode_aarch32_instrs_VFMAL_T1enc_A_txt (S : (BitVec 1)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveFP16MulNoRoundingToFP32Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (N +++ Vn))
    else (BitVec.toNat (Vn +++ N))
  let m :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (M +++ Vm))
    else (BitVec.toNat (Vm +++ M))
  let esize := 32
  let regs :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (S == 1#1)
  sail_assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && (m ≤b 31)))) "src/instrs32.sail:46972.64-46972.65"
  (execute_aarch32_instrs_VFMAL_Op_A_txt Q d datasize esize m n regs sub_op)

def decode_aarch32_instrs_VFMAL_i_A1enc_A_txt (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveFP16MulNoRoundingToFP32Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (N +++ Vn))
    else (BitVec.toNat (Vn +++ N))
  let m :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
    else (BitVec.toNat ((Sail.BitVec.extractLsb Vm 2 0) +++ M))
  let index :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
    else (BitVec.toNat (BitVec.join1 [(BitVec.access Vm 3)]))
  let esize := 32
  let regs :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (S == 1#1)
  sail_assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && ((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)))))) "src/instrs32.sail:47039.89-47039.90"
  (execute_aarch32_instrs_VFMAL_i_Op_A_txt Q d datasize esize index m n regs sub_op)

def decode_aarch32_instrs_VFMAL_i_T1enc_A_txt (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveFP16MulNoRoundingToFP32Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (N +++ Vn))
    else (BitVec.toNat (Vn +++ N))
  let m :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
    else (BitVec.toNat ((Sail.BitVec.extractLsb Vm 2 0) +++ M))
  let index :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
    else (BitVec.toNat (BitVec.join1 [(BitVec.access Vm 3)]))
  let esize := 32
  let regs :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  let datasize :=
    if ((Q == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (S == 1#1)
  sail_assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && ((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)))))) "src/instrs32.sail:47076.89-47076.90"
  (execute_aarch32_instrs_VFMAL_i_Op_A_txt Q d datasize esize index m n regs sub_op)

def decode_aarch32_instrs_VDOT_bf16_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveAArch32BF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let regs :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VDOT_bf16_Op_A_txt d m n regs)

def decode_aarch32_instrs_VDOT_bf16_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveAArch32BF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let regs :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VDOT_bf16_Op_A_txt d m n regs)

def decode_aarch32_instrs_VDOT_bf16_i_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveAArch32BF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat Vm)
  let i := (BitVec.toNat M)
  let regs :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VDOT_bf16_i_Op_A_txt d i m n regs)

def decode_aarch32_instrs_VDOT_bf16_i_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveAArch32BF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat Vm)
  let i := (BitVec.toNat M)
  let regs :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VDOT_bf16_i_Op_A_txt d i m n regs)

def decode_aarch32_instrs_VMMLA_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveAArch32BF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let regs := 2
  (execute_aarch32_instrs_VMMLA_Op_A_txt d m n)

def decode_aarch32_instrs_VMMLA_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveAArch32BF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let regs := 2
  (execute_aarch32_instrs_VMMLA_Op_A_txt d m n)

def decode_aarch32_instrs_VCVT_A1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveAArch32BF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let m := (BitVec.toNat (M +++ Vm))
  (execute_aarch32_instrs_VCVT_Op_A_txt d m)

def decode_aarch32_instrs_VCVT_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveAArch32BF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let m := (BitVec.toNat (M +++ Vm))
  (execute_aarch32_instrs_VCVT_Op_A_txt d m)

def decode_aarch32_instrs_VCVTB_bf16_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:47410.29-47410.30"
      if ((! (← (HaveAArch32BF16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (Vd +++ D))
      let m := (BitVec.toNat (Vm +++ M))
      (execute_aarch32_instrs_VCVTB_bf16_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_VCVTB_bf16_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveAArch32BF16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (Vd +++ D))
      let m := (BitVec.toNat (Vm +++ M))
      (execute_aarch32_instrs_VCVTB_bf16_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_VCVTT_A1enc_A_txt (cond : (BitVec 4)) (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:47467.29-47467.30"
      if ((! (← (HaveAArch32BF16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (Vd +++ D))
      let m := (BitVec.toNat (Vm +++ M))
      (execute_aarch32_instrs_VCVTT_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_VCVTT_T1enc_A_txt (D : (BitVec 1)) (Vd : (BitVec 4)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveAArch32BF16Ext ()))) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else (pure ())
      let d := (BitVec.toNat (Vd +++ D))
      let m := (BitVec.toNat (Vm +++ M))
      (execute_aarch32_instrs_VCVTT_Op_A_txt d m))
  else (pure ())

def decode_aarch32_instrs_VFMA_bf_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveAArch32BF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let elements := (Int.ediv 128 32)
  let sel := (BitVec.toNat Q)
  (execute_aarch32_instrs_VFMA_bf_Op_A_txt d elements m n sel)

def decode_aarch32_instrs_VFMA_bf_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveAArch32BF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let elements := (Int.ediv 128 32)
  let sel := (BitVec.toNat Q)
  (execute_aarch32_instrs_VFMA_bf_Op_A_txt d elements m n sel)

def decode_aarch32_instrs_VFMA_bfs_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveAArch32BF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
  let i := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
  let elements := (Int.ediv 128 32)
  let sel := (BitVec.toNat Q)
  (execute_aarch32_instrs_VFMA_bfs_Op_A_txt d elements i m n sel)

def decode_aarch32_instrs_VFMA_bfs_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveAArch32BF16Ext ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
  let i := (BitVec.toNat (M +++ (BitVec.join1 [(BitVec.access Vm 3)])))
  let elements := (Int.ediv 128 32)
  let sel := (BitVec.toNat Q)
  (execute_aarch32_instrs_VFMA_bfs_Op_A_txt d elements i m n sel)

def decode_aarch32_instrs_MMLA_A1enc_A_txt (B : (BitVec 1)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (U : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveAArch32Int8MatMulExt ()))) : Bool)
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
  if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  (execute_aarch32_instrs_MMLA_Op_A_txt d m n op1_unsigned op2_unsigned)

def decode_aarch32_instrs_MMLA_T1enc_A_txt (B : (BitVec 1)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (M : (BitVec 1)) (U : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveAArch32Int8MatMulExt ()))) : Bool)
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
  if (((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  (execute_aarch32_instrs_MMLA_Op_A_txt d m n op1_unsigned op2_unsigned)

def decode_aarch32_instrs_VUSDOT_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveAArch32Int8MatMulExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let regs :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VUSDOT_Op_A_txt d m n regs)

def decode_aarch32_instrs_VUSDOT_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveAArch32Int8MatMulExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && ((((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1)) || ((BitVec.join1 [(BitVec.access Vm 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat (M +++ Vm))
  let regs :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_VUSDOT_Op_A_txt d m n regs)

def decode_aarch32_instrs_DOT_A1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (U : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((! (← (HaveAArch32Int8MatMulExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let op1_unsigned : Bool := (U == 0#1)
  let op2_unsigned : Bool := (U == 1#1)
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat Vm)
  let i := (BitVec.toNat M)
  let regs :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_DOT_Op_A_txt d i m n op1_unsigned op2_unsigned regs)

def decode_aarch32_instrs_DOT_T1enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (U : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if ((← (InITBlock ())) : Bool)
  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
  else (pure ())
  if ((! (← (HaveAArch32Int8MatMulExt ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if (((Q == 1#1) && (((BitVec.join1 [(BitVec.access Vd 0)]) == 1#1) || ((BitVec.join1 [(BitVec.access Vn 0)]) == 1#1))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let op1_unsigned : Bool := (U == 0#1)
  let op2_unsigned : Bool := (U == 1#1)
  let d := (BitVec.toNat (D +++ Vd))
  let n := (BitVec.toNat (N +++ Vn))
  let m := (BitVec.toNat Vm)
  let i := (BitVec.toNat M)
  let regs :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  (execute_aarch32_instrs_DOT_Op_A_txt d i m n op1_unsigned op2_unsigned regs)

def decode_aarch32_instrs_CLRBHB_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      sail_assert (cond != 0b1111#4) "src/instrs32.sail:47977.29-47977.30"
      if ((! (← (HaveFeatCLRBHB ()))) : Bool)
      then (EndOfInstruction ())
      else (pure ())
      (pure (execute_aarch32_instrs_CLRBHB_Op_A_txt ())))
  else (pure ())

def decode_aarch32_instrs_CLRBHB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  if ((← (ConditionPassed ())) : Bool)
  then
    (do
      if ((! (← (HaveFeatCLRBHB ()))) : Bool)
      then (EndOfInstruction ())
      else (pure ())
      (pure (execute_aarch32_instrs_CLRBHB_Op_A_txt ())))
  else (pure ())

