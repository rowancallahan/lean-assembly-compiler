import Armv9.Armv9
import Armv9.Flow
import Armv9.Arith
import Armv9.Vector
import Armv9.MonoRewrites
import Armv9.Prelude
import Armv9.Builtins
import Armv9.V8Base
import Armv9.Instrs64Sve.P03
import Armv9.Instrs64Sve.P04

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

def decode_ST1D_Z_P_BZ_D_64_scaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 64
  let offs_size := 64
  let offs_unsigned : Bool := true
  let scale := 3
  match VL with
  | 128 => (execute_ST1D_Z_P_BZ_D_64_scaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1D_Z_P_BZ_D_64_scaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1D_Z_P_BZ_D_64_scaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1D_Z_P_BZ_D_64_scaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1D_Z_P_BZ_D_64_scaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1B_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_ST1B_Z_P_AI_D 128 esize g msize n offset t)
  | 256 => (execute_ST1B_Z_P_AI_D 256 esize g msize n offset t)
  | 512 => (execute_ST1B_Z_P_AI_D 512 esize g msize n offset t)
  | 1024 => (execute_ST1B_Z_P_AI_D 1024 esize g msize n offset t)
  | 2048 => (execute_ST1B_Z_P_AI_D 2048 esize g msize n offset t)
  | _ => (pure ())

def decode_ST1H_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_ST1H_Z_P_AI_D 128 esize g msize n offset t)
  | 256 => (execute_ST1H_Z_P_AI_D 256 esize g msize n offset t)
  | 512 => (execute_ST1H_Z_P_AI_D 512 esize g msize n offset t)
  | 1024 => (execute_ST1H_Z_P_AI_D 1024 esize g msize n offset t)
  | 2048 => (execute_ST1H_Z_P_AI_D 2048 esize g msize n offset t)
  | _ => (pure ())

def decode_ST1W_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_ST1W_Z_P_AI_D 128 esize g msize n offset t)
  | 256 => (execute_ST1W_Z_P_AI_D 256 esize g msize n offset t)
  | 512 => (execute_ST1W_Z_P_AI_D 512 esize g msize n offset t)
  | 1024 => (execute_ST1W_Z_P_AI_D 1024 esize g msize n offset t)
  | 2048 => (execute_ST1W_Z_P_AI_D 2048 esize g msize n offset t)
  | _ => (pure ())

def decode_ST1D_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 64
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_ST1D_Z_P_AI_D 128 esize g msize n offset t)
  | 256 => (execute_ST1D_Z_P_AI_D 256 esize g msize n offset t)
  | 512 => (execute_ST1D_Z_P_AI_D 512 esize g msize n offset t)
  | 1024 => (execute_ST1D_Z_P_AI_D 1024 esize g msize n offset t)
  | 2048 => (execute_ST1D_Z_P_AI_D 2048 esize g msize n offset t)
  | _ => (pure ())

def decode_ST1B_Z_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_ST1B_Z_P_AI_S 128 esize g msize n offset t)
  | 256 => (execute_ST1B_Z_P_AI_S 256 esize g msize n offset t)
  | 512 => (execute_ST1B_Z_P_AI_S 512 esize g msize n offset t)
  | 1024 => (execute_ST1B_Z_P_AI_S 1024 esize g msize n offset t)
  | 2048 => (execute_ST1B_Z_P_AI_S 2048 esize g msize n offset t)
  | _ => (pure ())

def decode_ST1H_Z_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_ST1H_Z_P_AI_S 128 esize g msize n offset t)
  | 256 => (execute_ST1H_Z_P_AI_S 256 esize g msize n offset t)
  | 512 => (execute_ST1H_Z_P_AI_S 512 esize g msize n offset t)
  | 1024 => (execute_ST1H_Z_P_AI_S 1024 esize g msize n offset t)
  | 2048 => (execute_ST1H_Z_P_AI_S 2048 esize g msize n offset t)
  | _ => (pure ())

def decode_ST1W_Z_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 32
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_ST1W_Z_P_AI_S 128 esize g msize n offset t)
  | 256 => (execute_ST1W_Z_P_AI_S 256 esize g msize n offset t)
  | 512 => (execute_ST1W_Z_P_AI_S 512 esize g msize n offset t)
  | 1024 => (execute_ST1W_Z_P_AI_S 1024 esize g msize n offset t)
  | 2048 => (execute_ST1W_Z_P_AI_S 2048 esize g msize n offset t)
  | _ => (pure ())

def decode_ST1B_Z_P_BI__ (msz : (BitVec 2)) (size : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let msize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1B_Z_P_BI__ 128 esize g msize n offset t)
  | 256 => (execute_ST1B_Z_P_BI__ 256 esize g msize n offset t)
  | 512 => (execute_ST1B_Z_P_BI__ 512 esize g msize n offset t)
  | 1024 => (execute_ST1B_Z_P_BI__ 1024 esize g msize n offset t)
  | 2048 => (execute_ST1B_Z_P_BI__ 2048 esize g msize n offset t)
  | _ => (pure ())

def decode_ST1H_Z_P_BI__ (msz : (BitVec 2)) (size : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let msize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1H_Z_P_BI__ 128 esize g msize n offset t)
  | 256 => (execute_ST1H_Z_P_BI__ 256 esize g msize n offset t)
  | 512 => (execute_ST1H_Z_P_BI__ 512 esize g msize n offset t)
  | 1024 => (execute_ST1H_Z_P_BI__ 1024 esize g msize n offset t)
  | 2048 => (execute_ST1H_Z_P_BI__ 2048 esize g msize n offset t)
  | _ => (pure ())

def decode_ST1W_Z_P_BI__ (msz : (BitVec 2)) (sz : (BitVec 1)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let msize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1W_Z_P_BI__ 128 esize g msize n offset t)
  | 256 => (execute_ST1W_Z_P_BI__ 256 esize g msize n offset t)
  | 512 => (execute_ST1W_Z_P_BI__ 512 esize g msize n offset t)
  | 1024 => (execute_ST1W_Z_P_BI__ 1024 esize g msize n offset t)
  | 2048 => (execute_ST1W_Z_P_BI__ 2048 esize g msize n offset t)
  | _ => (pure ())

def decode_ST1D_Z_P_BI__ (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1D_Z_P_BI__ 128 esize g msize n offset t)
  | 256 => (execute_ST1D_Z_P_BI__ 256 esize g msize n offset t)
  | 512 => (execute_ST1D_Z_P_BI__ 512 esize g msize n offset t)
  | 1024 => (execute_ST1D_Z_P_BI__ 1024 esize g msize n offset t)
  | 2048 => (execute_ST1D_Z_P_BI__ 2048 esize g msize n offset t)
  | _ => (pure ())

def decode_ST1W_Z_P_BI_U128 (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let msize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1W_Z_P_BI_U128 128 esize g msize n offset t)
  | 256 => (execute_ST1W_Z_P_BI_U128 256 esize g msize n offset t)
  | 512 => (execute_ST1W_Z_P_BI_U128 512 esize g msize n offset t)
  | 1024 => (execute_ST1W_Z_P_BI_U128 1024 esize g msize n offset t)
  | 2048 => (execute_ST1W_Z_P_BI_U128 2048 esize g msize n offset t)
  | _ => (pure ())

def decode_ST1D_Z_P_BI_U128 (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let msize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1D_Z_P_BI_U128 128 esize g msize n offset t)
  | 256 => (execute_ST1D_Z_P_BI_U128 256 esize g msize n offset t)
  | 512 => (execute_ST1D_Z_P_BI_U128 512 esize g msize n offset t)
  | 1024 => (execute_ST1D_Z_P_BI_U128 1024 esize g msize n offset t)
  | 2048 => (execute_ST1D_Z_P_BI_U128 2048 esize g msize n offset t)
  | _ => (pure ())

def decode_STNT1B_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1B_Z_P_BI_Contiguous 128 esize g n offset t)
  | 256 => (execute_STNT1B_Z_P_BI_Contiguous 256 esize g n offset t)
  | 512 => (execute_STNT1B_Z_P_BI_Contiguous 512 esize g n offset t)
  | 1024 => (execute_STNT1B_Z_P_BI_Contiguous 1024 esize g n offset t)
  | 2048 => (execute_STNT1B_Z_P_BI_Contiguous 2048 esize g n offset t)
  | _ => (pure ())

def decode_STNT1H_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1H_Z_P_BI_Contiguous 128 esize g n offset t)
  | 256 => (execute_STNT1H_Z_P_BI_Contiguous 256 esize g n offset t)
  | 512 => (execute_STNT1H_Z_P_BI_Contiguous 512 esize g n offset t)
  | 1024 => (execute_STNT1H_Z_P_BI_Contiguous 1024 esize g n offset t)
  | 2048 => (execute_STNT1H_Z_P_BI_Contiguous 2048 esize g n offset t)
  | _ => (pure ())

def decode_STNT1W_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1W_Z_P_BI_Contiguous 128 esize g n offset t)
  | 256 => (execute_STNT1W_Z_P_BI_Contiguous 256 esize g n offset t)
  | 512 => (execute_STNT1W_Z_P_BI_Contiguous 512 esize g n offset t)
  | 1024 => (execute_STNT1W_Z_P_BI_Contiguous 1024 esize g n offset t)
  | 2048 => (execute_STNT1W_Z_P_BI_Contiguous 2048 esize g n offset t)
  | _ => (pure ())

def decode_STNT1D_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1D_Z_P_BI_Contiguous 128 esize g n offset t)
  | 256 => (execute_STNT1D_Z_P_BI_Contiguous 256 esize g n offset t)
  | 512 => (execute_STNT1D_Z_P_BI_Contiguous 512 esize g n offset t)
  | 1024 => (execute_STNT1D_Z_P_BI_Contiguous 1024 esize g n offset t)
  | 2048 => (execute_STNT1D_Z_P_BI_Contiguous 2048 esize g n offset t)
  | _ => (pure ())

def decode_ST2B_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 8
  let offset := (BitVec.toInt imm4)
  let nreg := 2
  match VL with
  | 128 => (execute_ST2B_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_ST2B_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_ST2B_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_ST2B_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_ST2B_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST2H_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let offset := (BitVec.toInt imm4)
  let nreg := 2
  match VL with
  | 128 => (execute_ST2H_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_ST2H_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_ST2H_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_ST2H_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_ST2H_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST2W_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let offset := (BitVec.toInt imm4)
  let nreg := 2
  match VL with
  | 128 => (execute_ST2W_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_ST2W_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_ST2W_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_ST2W_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_ST2W_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST2D_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let offset := (BitVec.toInt imm4)
  let nreg := 2
  match VL with
  | 128 => (execute_ST2D_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_ST2D_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_ST2D_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_ST2D_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_ST2D_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST3B_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 8
  let offset := (BitVec.toInt imm4)
  let nreg := 3
  match VL with
  | 128 => (execute_ST3B_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_ST3B_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_ST3B_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_ST3B_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_ST3B_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST3H_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let offset := (BitVec.toInt imm4)
  let nreg := 3
  match VL with
  | 128 => (execute_ST3H_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_ST3H_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_ST3H_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_ST3H_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_ST3H_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST3W_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let offset := (BitVec.toInt imm4)
  let nreg := 3
  match VL with
  | 128 => (execute_ST3W_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_ST3W_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_ST3W_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_ST3W_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_ST3W_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST3D_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let offset := (BitVec.toInt imm4)
  let nreg := 3
  match VL with
  | 128 => (execute_ST3D_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_ST3D_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_ST3D_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_ST3D_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_ST3D_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST4B_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 8
  let offset := (BitVec.toInt imm4)
  let nreg := 4
  match VL with
  | 128 => (execute_ST4B_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_ST4B_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_ST4B_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_ST4B_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_ST4B_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST4H_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let offset := (BitVec.toInt imm4)
  let nreg := 4
  match VL with
  | 128 => (execute_ST4H_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_ST4H_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_ST4H_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_ST4H_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_ST4H_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST4W_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let offset := (BitVec.toInt imm4)
  let nreg := 4
  match VL with
  | 128 => (execute_ST4W_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_ST4W_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_ST4W_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_ST4W_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_ST4W_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST4D_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let offset := (BitVec.toInt imm4)
  let nreg := 4
  match VL with
  | 128 => (execute_ST4D_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_ST4D_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_ST4D_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_ST4D_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_ST4D_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST2Q_Z_P_BI_Contiguous (num : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let offset := (BitVec.toInt imm4)
  let nreg := 2
  match VL with
  | 128 => (execute_ST2Q_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_ST2Q_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_ST2Q_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_ST2Q_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_ST2Q_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST3Q_Z_P_BI_Contiguous (num : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let offset := (BitVec.toInt imm4)
  let nreg := 3
  match VL with
  | 128 => (execute_ST3Q_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_ST3Q_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_ST3Q_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_ST3Q_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_ST3Q_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST4Q_Z_P_BI_Contiguous (num : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let offset := (BitVec.toInt imm4)
  let nreg := 4
  match VL with
  | 128 => (execute_ST4Q_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_ST4Q_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_ST4Q_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_ST4Q_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_ST4Q_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LDNT1B_Z_P_AR_S_x32_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDNT1B_Z_P_AR_S_x32_unscaled 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDNT1B_Z_P_AR_S_x32_unscaled 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDNT1B_Z_P_AR_S_x32_unscaled 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDNT1B_Z_P_AR_S_x32_unscaled 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDNT1B_Z_P_AR_S_x32_unscaled 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDNT1H_Z_P_AR_S_x32_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDNT1H_Z_P_AR_S_x32_unscaled 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDNT1H_Z_P_AR_S_x32_unscaled 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDNT1H_Z_P_AR_S_x32_unscaled 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDNT1H_Z_P_AR_S_x32_unscaled 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDNT1H_Z_P_AR_S_x32_unscaled 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDNT1W_Z_P_AR_S_x32_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 32
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDNT1W_Z_P_AR_S_x32_unscaled 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDNT1W_Z_P_AR_S_x32_unscaled 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDNT1W_Z_P_AR_S_x32_unscaled 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDNT1W_Z_P_AR_S_x32_unscaled 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDNT1W_Z_P_AR_S_x32_unscaled 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDNT1SB_Z_P_AR_S_x32_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LDNT1SB_Z_P_AR_S_x32_unscaled 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDNT1SB_Z_P_AR_S_x32_unscaled 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDNT1SB_Z_P_AR_S_x32_unscaled 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDNT1SB_Z_P_AR_S_x32_unscaled 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDNT1SB_Z_P_AR_S_x32_unscaled 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDNT1SH_Z_P_AR_S_x32_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LDNT1SH_Z_P_AR_S_x32_unscaled 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDNT1SH_Z_P_AR_S_x32_unscaled 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDNT1SH_Z_P_AR_S_x32_unscaled 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDNT1SH_Z_P_AR_S_x32_unscaled 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDNT1SH_Z_P_AR_S_x32_unscaled 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDNT1B_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDNT1B_Z_P_AR_D_64_unscaled 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDNT1B_Z_P_AR_D_64_unscaled 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDNT1B_Z_P_AR_D_64_unscaled 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDNT1B_Z_P_AR_D_64_unscaled 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDNT1B_Z_P_AR_D_64_unscaled 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDNT1H_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDNT1H_Z_P_AR_D_64_unscaled 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDNT1H_Z_P_AR_D_64_unscaled 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDNT1H_Z_P_AR_D_64_unscaled 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDNT1H_Z_P_AR_D_64_unscaled 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDNT1H_Z_P_AR_D_64_unscaled 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDNT1W_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDNT1W_Z_P_AR_D_64_unscaled 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDNT1W_Z_P_AR_D_64_unscaled 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDNT1W_Z_P_AR_D_64_unscaled 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDNT1W_Z_P_AR_D_64_unscaled 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDNT1W_Z_P_AR_D_64_unscaled 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDNT1D_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 64
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDNT1D_Z_P_AR_D_64_unscaled 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDNT1D_Z_P_AR_D_64_unscaled 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDNT1D_Z_P_AR_D_64_unscaled 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDNT1D_Z_P_AR_D_64_unscaled 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDNT1D_Z_P_AR_D_64_unscaled 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDNT1SB_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LDNT1SB_Z_P_AR_D_64_unscaled 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDNT1SB_Z_P_AR_D_64_unscaled 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDNT1SB_Z_P_AR_D_64_unscaled 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDNT1SB_Z_P_AR_D_64_unscaled 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDNT1SB_Z_P_AR_D_64_unscaled 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDNT1SH_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LDNT1SH_Z_P_AR_D_64_unscaled 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDNT1SH_Z_P_AR_D_64_unscaled 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDNT1SH_Z_P_AR_D_64_unscaled 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDNT1SH_Z_P_AR_D_64_unscaled 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDNT1SH_Z_P_AR_D_64_unscaled 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDNT1SW_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LDNT1SW_Z_P_AR_D_64_unscaled 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDNT1SW_Z_P_AR_D_64_unscaled 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDNT1SW_Z_P_AR_D_64_unscaled 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDNT1SW_Z_P_AR_D_64_unscaled 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDNT1SW_Z_P_AR_D_64_unscaled 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_STNT1B_Z_P_AR_S_x32_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  match VL with
  | 128 => (execute_STNT1B_Z_P_AR_S_x32_unscaled 128 esize g m msize n t)
  | 256 => (execute_STNT1B_Z_P_AR_S_x32_unscaled 256 esize g m msize n t)
  | 512 => (execute_STNT1B_Z_P_AR_S_x32_unscaled 512 esize g m msize n t)
  | 1024 => (execute_STNT1B_Z_P_AR_S_x32_unscaled 1024 esize g m msize n t)
  | 2048 => (execute_STNT1B_Z_P_AR_S_x32_unscaled 2048 esize g m msize n t)
  | _ => (pure ())

def decode_STNT1H_Z_P_AR_S_x32_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  match VL with
  | 128 => (execute_STNT1H_Z_P_AR_S_x32_unscaled 128 esize g m msize n t)
  | 256 => (execute_STNT1H_Z_P_AR_S_x32_unscaled 256 esize g m msize n t)
  | 512 => (execute_STNT1H_Z_P_AR_S_x32_unscaled 512 esize g m msize n t)
  | 1024 => (execute_STNT1H_Z_P_AR_S_x32_unscaled 1024 esize g m msize n t)
  | 2048 => (execute_STNT1H_Z_P_AR_S_x32_unscaled 2048 esize g m msize n t)
  | _ => (pure ())

def decode_STNT1W_Z_P_AR_S_x32_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 32
  match VL with
  | 128 => (execute_STNT1W_Z_P_AR_S_x32_unscaled 128 esize g m msize n t)
  | 256 => (execute_STNT1W_Z_P_AR_S_x32_unscaled 256 esize g m msize n t)
  | 512 => (execute_STNT1W_Z_P_AR_S_x32_unscaled 512 esize g m msize n t)
  | 1024 => (execute_STNT1W_Z_P_AR_S_x32_unscaled 1024 esize g m msize n t)
  | 2048 => (execute_STNT1W_Z_P_AR_S_x32_unscaled 2048 esize g m msize n t)
  | _ => (pure ())

def decode_STNT1B_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  match VL with
  | 128 => (execute_STNT1B_Z_P_AR_D_64_unscaled 128 esize g m msize n t)
  | 256 => (execute_STNT1B_Z_P_AR_D_64_unscaled 256 esize g m msize n t)
  | 512 => (execute_STNT1B_Z_P_AR_D_64_unscaled 512 esize g m msize n t)
  | 1024 => (execute_STNT1B_Z_P_AR_D_64_unscaled 1024 esize g m msize n t)
  | 2048 => (execute_STNT1B_Z_P_AR_D_64_unscaled 2048 esize g m msize n t)
  | _ => (pure ())

def decode_STNT1H_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  match VL with
  | 128 => (execute_STNT1H_Z_P_AR_D_64_unscaled 128 esize g m msize n t)
  | 256 => (execute_STNT1H_Z_P_AR_D_64_unscaled 256 esize g m msize n t)
  | 512 => (execute_STNT1H_Z_P_AR_D_64_unscaled 512 esize g m msize n t)
  | 1024 => (execute_STNT1H_Z_P_AR_D_64_unscaled 1024 esize g m msize n t)
  | 2048 => (execute_STNT1H_Z_P_AR_D_64_unscaled 2048 esize g m msize n t)
  | _ => (pure ())

def decode_STNT1W_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  match VL with
  | 128 => (execute_STNT1W_Z_P_AR_D_64_unscaled 128 esize g m msize n t)
  | 256 => (execute_STNT1W_Z_P_AR_D_64_unscaled 256 esize g m msize n t)
  | 512 => (execute_STNT1W_Z_P_AR_D_64_unscaled 512 esize g m msize n t)
  | 1024 => (execute_STNT1W_Z_P_AR_D_64_unscaled 1024 esize g m msize n t)
  | 2048 => (execute_STNT1W_Z_P_AR_D_64_unscaled 2048 esize g m msize n t)
  | _ => (pure ())

def decode_STNT1D_Z_P_AR_D_64_unscaled (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 64
  match VL with
  | 128 => (execute_STNT1D_Z_P_AR_D_64_unscaled 128 esize g m msize n t)
  | 256 => (execute_STNT1D_Z_P_AR_D_64_unscaled 256 esize g m msize n t)
  | 512 => (execute_STNT1D_Z_P_AR_D_64_unscaled 512 esize g m msize n t)
  | 1024 => (execute_STNT1D_Z_P_AR_D_64_unscaled 1024 esize g m msize n t)
  | 2048 => (execute_STNT1D_Z_P_AR_D_64_unscaled 2048 esize g m msize n t)
  | _ => (pure ())

def decode_LD1Q_Z_P_AR_D_64_unscaled (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  match VL with
  | 128 => (execute_LD1Q_Z_P_AR_D_64_unscaled 128 g m n t)
  | 256 => (execute_LD1Q_Z_P_AR_D_64_unscaled 256 g m n t)
  | 512 => (execute_LD1Q_Z_P_AR_D_64_unscaled 512 g m n t)
  | 1024 => (execute_LD1Q_Z_P_AR_D_64_unscaled 1024 g m n t)
  | 2048 => (execute_LD1Q_Z_P_AR_D_64_unscaled 2048 g m n t)
  | _ => (pure ())

def decode_ST1Q_Z_P_AR_D_64_unscaled (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  match VL with
  | 128 => (execute_ST1Q_Z_P_AR_D_64_unscaled 128 g m n t)
  | 256 => (execute_ST1Q_Z_P_AR_D_64_unscaled 256 g m n t)
  | 512 => (execute_ST1Q_Z_P_AR_D_64_unscaled 512 g m n t)
  | 1024 => (execute_ST1Q_Z_P_AR_D_64_unscaled 1024 g m n t)
  | 2048 => (execute_ST1Q_Z_P_AR_D_64_unscaled 2048 g m n t)
  | _ => (pure ())

def decode_LD1B_MZ_P_BR_2 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 8
  match VL with
  | 128 => (execute_LD1B_MZ_P_BR_2 128 esize g m n nreg t)
  | 256 => (execute_LD1B_MZ_P_BR_2 256 esize g m n nreg t)
  | 512 => (execute_LD1B_MZ_P_BR_2 512 esize g m n nreg t)
  | 1024 => (execute_LD1B_MZ_P_BR_2 1024 esize g m n nreg t)
  | 2048 => (execute_LD1B_MZ_P_BR_2 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD1H_MZ_P_BR_2 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 16
  match VL with
  | 128 => (execute_LD1H_MZ_P_BR_2 128 esize g m n nreg t)
  | 256 => (execute_LD1H_MZ_P_BR_2 256 esize g m n nreg t)
  | 512 => (execute_LD1H_MZ_P_BR_2 512 esize g m n nreg t)
  | 1024 => (execute_LD1H_MZ_P_BR_2 1024 esize g m n nreg t)
  | 2048 => (execute_LD1H_MZ_P_BR_2 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD1W_MZ_P_BR_2 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 32
  match VL with
  | 128 => (execute_LD1W_MZ_P_BR_2 128 esize g m n nreg t)
  | 256 => (execute_LD1W_MZ_P_BR_2 256 esize g m n nreg t)
  | 512 => (execute_LD1W_MZ_P_BR_2 512 esize g m n nreg t)
  | 1024 => (execute_LD1W_MZ_P_BR_2 1024 esize g m n nreg t)
  | 2048 => (execute_LD1W_MZ_P_BR_2 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD1D_MZ_P_BR_2 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 64
  match VL with
  | 128 => (execute_LD1D_MZ_P_BR_2 128 esize g m n nreg t)
  | 256 => (execute_LD1D_MZ_P_BR_2 256 esize g m n nreg t)
  | 512 => (execute_LD1D_MZ_P_BR_2 512 esize g m n nreg t)
  | 1024 => (execute_LD1D_MZ_P_BR_2 1024 esize g m n nreg t)
  | 2048 => (execute_LD1D_MZ_P_BR_2 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD1B_MZ_P_BR_4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 8
  match VL with
  | 128 => (execute_LD1B_MZ_P_BR_4 128 esize g m n nreg t)
  | 256 => (execute_LD1B_MZ_P_BR_4 256 esize g m n nreg t)
  | 512 => (execute_LD1B_MZ_P_BR_4 512 esize g m n nreg t)
  | 1024 => (execute_LD1B_MZ_P_BR_4 1024 esize g m n nreg t)
  | 2048 => (execute_LD1B_MZ_P_BR_4 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD1H_MZ_P_BR_4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 16
  match VL with
  | 128 => (execute_LD1H_MZ_P_BR_4 128 esize g m n nreg t)
  | 256 => (execute_LD1H_MZ_P_BR_4 256 esize g m n nreg t)
  | 512 => (execute_LD1H_MZ_P_BR_4 512 esize g m n nreg t)
  | 1024 => (execute_LD1H_MZ_P_BR_4 1024 esize g m n nreg t)
  | 2048 => (execute_LD1H_MZ_P_BR_4 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD1W_MZ_P_BR_4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 32
  match VL with
  | 128 => (execute_LD1W_MZ_P_BR_4 128 esize g m n nreg t)
  | 256 => (execute_LD1W_MZ_P_BR_4 256 esize g m n nreg t)
  | 512 => (execute_LD1W_MZ_P_BR_4 512 esize g m n nreg t)
  | 1024 => (execute_LD1W_MZ_P_BR_4 1024 esize g m n nreg t)
  | 2048 => (execute_LD1W_MZ_P_BR_4 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD1D_MZ_P_BR_4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 64
  match VL with
  | 128 => (execute_LD1D_MZ_P_BR_4 128 esize g m n nreg t)
  | 256 => (execute_LD1D_MZ_P_BR_4 256 esize g m n nreg t)
  | 512 => (execute_LD1D_MZ_P_BR_4 512 esize g m n nreg t)
  | 1024 => (execute_LD1D_MZ_P_BR_4 1024 esize g m n nreg t)
  | 2048 => (execute_LD1D_MZ_P_BR_4 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LDNT1B_MZ_P_BR_2 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 8
  match VL with
  | 128 => (execute_LDNT1B_MZ_P_BR_2 128 esize g m n nreg t)
  | 256 => (execute_LDNT1B_MZ_P_BR_2 256 esize g m n nreg t)
  | 512 => (execute_LDNT1B_MZ_P_BR_2 512 esize g m n nreg t)
  | 1024 => (execute_LDNT1B_MZ_P_BR_2 1024 esize g m n nreg t)
  | 2048 => (execute_LDNT1B_MZ_P_BR_2 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LDNT1H_MZ_P_BR_2 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 16
  match VL with
  | 128 => (execute_LDNT1H_MZ_P_BR_2 128 esize g m n nreg t)
  | 256 => (execute_LDNT1H_MZ_P_BR_2 256 esize g m n nreg t)
  | 512 => (execute_LDNT1H_MZ_P_BR_2 512 esize g m n nreg t)
  | 1024 => (execute_LDNT1H_MZ_P_BR_2 1024 esize g m n nreg t)
  | 2048 => (execute_LDNT1H_MZ_P_BR_2 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LDNT1W_MZ_P_BR_2 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 32
  match VL with
  | 128 => (execute_LDNT1W_MZ_P_BR_2 128 esize g m n nreg t)
  | 256 => (execute_LDNT1W_MZ_P_BR_2 256 esize g m n nreg t)
  | 512 => (execute_LDNT1W_MZ_P_BR_2 512 esize g m n nreg t)
  | 1024 => (execute_LDNT1W_MZ_P_BR_2 1024 esize g m n nreg t)
  | 2048 => (execute_LDNT1W_MZ_P_BR_2 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LDNT1D_MZ_P_BR_2 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 64
  match VL with
  | 128 => (execute_LDNT1D_MZ_P_BR_2 128 esize g m n nreg t)
  | 256 => (execute_LDNT1D_MZ_P_BR_2 256 esize g m n nreg t)
  | 512 => (execute_LDNT1D_MZ_P_BR_2 512 esize g m n nreg t)
  | 1024 => (execute_LDNT1D_MZ_P_BR_2 1024 esize g m n nreg t)
  | 2048 => (execute_LDNT1D_MZ_P_BR_2 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LDNT1B_MZ_P_BR_4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 8
  match VL with
  | 128 => (execute_LDNT1B_MZ_P_BR_4 128 esize g m n nreg t)
  | 256 => (execute_LDNT1B_MZ_P_BR_4 256 esize g m n nreg t)
  | 512 => (execute_LDNT1B_MZ_P_BR_4 512 esize g m n nreg t)
  | 1024 => (execute_LDNT1B_MZ_P_BR_4 1024 esize g m n nreg t)
  | 2048 => (execute_LDNT1B_MZ_P_BR_4 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LDNT1H_MZ_P_BR_4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 16
  match VL with
  | 128 => (execute_LDNT1H_MZ_P_BR_4 128 esize g m n nreg t)
  | 256 => (execute_LDNT1H_MZ_P_BR_4 256 esize g m n nreg t)
  | 512 => (execute_LDNT1H_MZ_P_BR_4 512 esize g m n nreg t)
  | 1024 => (execute_LDNT1H_MZ_P_BR_4 1024 esize g m n nreg t)
  | 2048 => (execute_LDNT1H_MZ_P_BR_4 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LDNT1W_MZ_P_BR_4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 32
  match VL with
  | 128 => (execute_LDNT1W_MZ_P_BR_4 128 esize g m n nreg t)
  | 256 => (execute_LDNT1W_MZ_P_BR_4 256 esize g m n nreg t)
  | 512 => (execute_LDNT1W_MZ_P_BR_4 512 esize g m n nreg t)
  | 1024 => (execute_LDNT1W_MZ_P_BR_4 1024 esize g m n nreg t)
  | 2048 => (execute_LDNT1W_MZ_P_BR_4 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LDNT1D_MZ_P_BR_4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 64
  match VL with
  | 128 => (execute_LDNT1D_MZ_P_BR_4 128 esize g m n nreg t)
  | 256 => (execute_LDNT1D_MZ_P_BR_4 256 esize g m n nreg t)
  | 512 => (execute_LDNT1D_MZ_P_BR_4 512 esize g m n nreg t)
  | 1024 => (execute_LDNT1D_MZ_P_BR_4 1024 esize g m n nreg t)
  | 2048 => (execute_LDNT1D_MZ_P_BR_4 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST1B_MZ_P_BR_2 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 8
  match VL with
  | 128 => (execute_ST1B_MZ_P_BR_2 128 esize g m n nreg t)
  | 256 => (execute_ST1B_MZ_P_BR_2 256 esize g m n nreg t)
  | 512 => (execute_ST1B_MZ_P_BR_2 512 esize g m n nreg t)
  | 1024 => (execute_ST1B_MZ_P_BR_2 1024 esize g m n nreg t)
  | 2048 => (execute_ST1B_MZ_P_BR_2 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST1H_MZ_P_BR_2 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 16
  match VL with
  | 128 => (execute_ST1H_MZ_P_BR_2 128 esize g m n nreg t)
  | 256 => (execute_ST1H_MZ_P_BR_2 256 esize g m n nreg t)
  | 512 => (execute_ST1H_MZ_P_BR_2 512 esize g m n nreg t)
  | 1024 => (execute_ST1H_MZ_P_BR_2 1024 esize g m n nreg t)
  | 2048 => (execute_ST1H_MZ_P_BR_2 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST1W_MZ_P_BR_2 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 32
  match VL with
  | 128 => (execute_ST1W_MZ_P_BR_2 128 esize g m n nreg t)
  | 256 => (execute_ST1W_MZ_P_BR_2 256 esize g m n nreg t)
  | 512 => (execute_ST1W_MZ_P_BR_2 512 esize g m n nreg t)
  | 1024 => (execute_ST1W_MZ_P_BR_2 1024 esize g m n nreg t)
  | 2048 => (execute_ST1W_MZ_P_BR_2 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST1D_MZ_P_BR_2 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 64
  match VL with
  | 128 => (execute_ST1D_MZ_P_BR_2 128 esize g m n nreg t)
  | 256 => (execute_ST1D_MZ_P_BR_2 256 esize g m n nreg t)
  | 512 => (execute_ST1D_MZ_P_BR_2 512 esize g m n nreg t)
  | 1024 => (execute_ST1D_MZ_P_BR_2 1024 esize g m n nreg t)
  | 2048 => (execute_ST1D_MZ_P_BR_2 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST1B_MZ_P_BR_4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 8
  match VL with
  | 128 => (execute_ST1B_MZ_P_BR_4 128 esize g m n nreg t)
  | 256 => (execute_ST1B_MZ_P_BR_4 256 esize g m n nreg t)
  | 512 => (execute_ST1B_MZ_P_BR_4 512 esize g m n nreg t)
  | 1024 => (execute_ST1B_MZ_P_BR_4 1024 esize g m n nreg t)
  | 2048 => (execute_ST1B_MZ_P_BR_4 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST1H_MZ_P_BR_4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 16
  match VL with
  | 128 => (execute_ST1H_MZ_P_BR_4 128 esize g m n nreg t)
  | 256 => (execute_ST1H_MZ_P_BR_4 256 esize g m n nreg t)
  | 512 => (execute_ST1H_MZ_P_BR_4 512 esize g m n nreg t)
  | 1024 => (execute_ST1H_MZ_P_BR_4 1024 esize g m n nreg t)
  | 2048 => (execute_ST1H_MZ_P_BR_4 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST1W_MZ_P_BR_4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 32
  match VL with
  | 128 => (execute_ST1W_MZ_P_BR_4 128 esize g m n nreg t)
  | 256 => (execute_ST1W_MZ_P_BR_4 256 esize g m n nreg t)
  | 512 => (execute_ST1W_MZ_P_BR_4 512 esize g m n nreg t)
  | 1024 => (execute_ST1W_MZ_P_BR_4 1024 esize g m n nreg t)
  | 2048 => (execute_ST1W_MZ_P_BR_4 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST1D_MZ_P_BR_4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 64
  match VL with
  | 128 => (execute_ST1D_MZ_P_BR_4 128 esize g m n nreg t)
  | 256 => (execute_ST1D_MZ_P_BR_4 256 esize g m n nreg t)
  | 512 => (execute_ST1D_MZ_P_BR_4 512 esize g m n nreg t)
  | 1024 => (execute_ST1D_MZ_P_BR_4 1024 esize g m n nreg t)
  | 2048 => (execute_ST1D_MZ_P_BR_4 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_STNT1B_MZ_P_BR_2 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 8
  match VL with
  | 128 => (execute_STNT1B_MZ_P_BR_2 128 esize g m n nreg t)
  | 256 => (execute_STNT1B_MZ_P_BR_2 256 esize g m n nreg t)
  | 512 => (execute_STNT1B_MZ_P_BR_2 512 esize g m n nreg t)
  | 1024 => (execute_STNT1B_MZ_P_BR_2 1024 esize g m n nreg t)
  | 2048 => (execute_STNT1B_MZ_P_BR_2 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_STNT1H_MZ_P_BR_2 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 16
  match VL with
  | 128 => (execute_STNT1H_MZ_P_BR_2 128 esize g m n nreg t)
  | 256 => (execute_STNT1H_MZ_P_BR_2 256 esize g m n nreg t)
  | 512 => (execute_STNT1H_MZ_P_BR_2 512 esize g m n nreg t)
  | 1024 => (execute_STNT1H_MZ_P_BR_2 1024 esize g m n nreg t)
  | 2048 => (execute_STNT1H_MZ_P_BR_2 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_STNT1W_MZ_P_BR_2 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 32
  match VL with
  | 128 => (execute_STNT1W_MZ_P_BR_2 128 esize g m n nreg t)
  | 256 => (execute_STNT1W_MZ_P_BR_2 256 esize g m n nreg t)
  | 512 => (execute_STNT1W_MZ_P_BR_2 512 esize g m n nreg t)
  | 1024 => (execute_STNT1W_MZ_P_BR_2 1024 esize g m n nreg t)
  | 2048 => (execute_STNT1W_MZ_P_BR_2 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_STNT1D_MZ_P_BR_2 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 64
  match VL with
  | 128 => (execute_STNT1D_MZ_P_BR_2 128 esize g m n nreg t)
  | 256 => (execute_STNT1D_MZ_P_BR_2 256 esize g m n nreg t)
  | 512 => (execute_STNT1D_MZ_P_BR_2 512 esize g m n nreg t)
  | 1024 => (execute_STNT1D_MZ_P_BR_2 1024 esize g m n nreg t)
  | 2048 => (execute_STNT1D_MZ_P_BR_2 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_STNT1B_MZ_P_BR_4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 8
  match VL with
  | 128 => (execute_STNT1B_MZ_P_BR_4 128 esize g m n nreg t)
  | 256 => (execute_STNT1B_MZ_P_BR_4 256 esize g m n nreg t)
  | 512 => (execute_STNT1B_MZ_P_BR_4 512 esize g m n nreg t)
  | 1024 => (execute_STNT1B_MZ_P_BR_4 1024 esize g m n nreg t)
  | 2048 => (execute_STNT1B_MZ_P_BR_4 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_STNT1H_MZ_P_BR_4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 16
  match VL with
  | 128 => (execute_STNT1H_MZ_P_BR_4 128 esize g m n nreg t)
  | 256 => (execute_STNT1H_MZ_P_BR_4 256 esize g m n nreg t)
  | 512 => (execute_STNT1H_MZ_P_BR_4 512 esize g m n nreg t)
  | 1024 => (execute_STNT1H_MZ_P_BR_4 1024 esize g m n nreg t)
  | 2048 => (execute_STNT1H_MZ_P_BR_4 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_STNT1W_MZ_P_BR_4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 32
  match VL with
  | 128 => (execute_STNT1W_MZ_P_BR_4 128 esize g m n nreg t)
  | 256 => (execute_STNT1W_MZ_P_BR_4 256 esize g m n nreg t)
  | 512 => (execute_STNT1W_MZ_P_BR_4 512 esize g m n nreg t)
  | 1024 => (execute_STNT1W_MZ_P_BR_4 1024 esize g m n nreg t)
  | 2048 => (execute_STNT1W_MZ_P_BR_4 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_STNT1D_MZ_P_BR_4 (Rm : (BitVec 5)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 64
  match VL with
  | 128 => (execute_STNT1D_MZ_P_BR_4 128 esize g m n nreg t)
  | 256 => (execute_STNT1D_MZ_P_BR_4 256 esize g m n nreg t)
  | 512 => (execute_STNT1D_MZ_P_BR_4 512 esize g m n nreg t)
  | 1024 => (execute_STNT1D_MZ_P_BR_4 1024 esize g m n nreg t)
  | 2048 => (execute_STNT1D_MZ_P_BR_4 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD1B_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1B_MZ_P_BI_2 128 esize g n nreg offset t)
  | 256 => (execute_LD1B_MZ_P_BI_2 256 esize g n nreg offset t)
  | 512 => (execute_LD1B_MZ_P_BI_2 512 esize g n nreg offset t)
  | 1024 => (execute_LD1B_MZ_P_BI_2 1024 esize g n nreg offset t)
  | 2048 => (execute_LD1B_MZ_P_BI_2 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD1H_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1H_MZ_P_BI_2 128 esize g n nreg offset t)
  | 256 => (execute_LD1H_MZ_P_BI_2 256 esize g n nreg offset t)
  | 512 => (execute_LD1H_MZ_P_BI_2 512 esize g n nreg offset t)
  | 1024 => (execute_LD1H_MZ_P_BI_2 1024 esize g n nreg offset t)
  | 2048 => (execute_LD1H_MZ_P_BI_2 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD1W_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1W_MZ_P_BI_2 128 esize g n nreg offset t)
  | 256 => (execute_LD1W_MZ_P_BI_2 256 esize g n nreg offset t)
  | 512 => (execute_LD1W_MZ_P_BI_2 512 esize g n nreg offset t)
  | 1024 => (execute_LD1W_MZ_P_BI_2 1024 esize g n nreg offset t)
  | 2048 => (execute_LD1W_MZ_P_BI_2 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD1D_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1D_MZ_P_BI_2 128 esize g n nreg offset t)
  | 256 => (execute_LD1D_MZ_P_BI_2 256 esize g n nreg offset t)
  | 512 => (execute_LD1D_MZ_P_BI_2 512 esize g n nreg offset t)
  | 1024 => (execute_LD1D_MZ_P_BI_2 1024 esize g n nreg offset t)
  | 2048 => (execute_LD1D_MZ_P_BI_2 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD1B_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1B_MZ_P_BI_4 128 esize g n nreg offset t)
  | 256 => (execute_LD1B_MZ_P_BI_4 256 esize g n nreg offset t)
  | 512 => (execute_LD1B_MZ_P_BI_4 512 esize g n nreg offset t)
  | 1024 => (execute_LD1B_MZ_P_BI_4 1024 esize g n nreg offset t)
  | 2048 => (execute_LD1B_MZ_P_BI_4 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD1H_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1H_MZ_P_BI_4 128 esize g n nreg offset t)
  | 256 => (execute_LD1H_MZ_P_BI_4 256 esize g n nreg offset t)
  | 512 => (execute_LD1H_MZ_P_BI_4 512 esize g n nreg offset t)
  | 1024 => (execute_LD1H_MZ_P_BI_4 1024 esize g n nreg offset t)
  | 2048 => (execute_LD1H_MZ_P_BI_4 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD1W_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1W_MZ_P_BI_4 128 esize g n nreg offset t)
  | 256 => (execute_LD1W_MZ_P_BI_4 256 esize g n nreg offset t)
  | 512 => (execute_LD1W_MZ_P_BI_4 512 esize g n nreg offset t)
  | 1024 => (execute_LD1W_MZ_P_BI_4 1024 esize g n nreg offset t)
  | 2048 => (execute_LD1W_MZ_P_BI_4 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD1D_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1D_MZ_P_BI_4 128 esize g n nreg offset t)
  | 256 => (execute_LD1D_MZ_P_BI_4 256 esize g n nreg offset t)
  | 512 => (execute_LD1D_MZ_P_BI_4 512 esize g n nreg offset t)
  | 1024 => (execute_LD1D_MZ_P_BI_4 1024 esize g n nreg offset t)
  | 2048 => (execute_LD1D_MZ_P_BI_4 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LDNT1B_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNT1B_MZ_P_BI_2 128 esize g n nreg offset t)
  | 256 => (execute_LDNT1B_MZ_P_BI_2 256 esize g n nreg offset t)
  | 512 => (execute_LDNT1B_MZ_P_BI_2 512 esize g n nreg offset t)
  | 1024 => (execute_LDNT1B_MZ_P_BI_2 1024 esize g n nreg offset t)
  | 2048 => (execute_LDNT1B_MZ_P_BI_2 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LDNT1H_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNT1H_MZ_P_BI_2 128 esize g n nreg offset t)
  | 256 => (execute_LDNT1H_MZ_P_BI_2 256 esize g n nreg offset t)
  | 512 => (execute_LDNT1H_MZ_P_BI_2 512 esize g n nreg offset t)
  | 1024 => (execute_LDNT1H_MZ_P_BI_2 1024 esize g n nreg offset t)
  | 2048 => (execute_LDNT1H_MZ_P_BI_2 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LDNT1W_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNT1W_MZ_P_BI_2 128 esize g n nreg offset t)
  | 256 => (execute_LDNT1W_MZ_P_BI_2 256 esize g n nreg offset t)
  | 512 => (execute_LDNT1W_MZ_P_BI_2 512 esize g n nreg offset t)
  | 1024 => (execute_LDNT1W_MZ_P_BI_2 1024 esize g n nreg offset t)
  | 2048 => (execute_LDNT1W_MZ_P_BI_2 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LDNT1D_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNT1D_MZ_P_BI_2 128 esize g n nreg offset t)
  | 256 => (execute_LDNT1D_MZ_P_BI_2 256 esize g n nreg offset t)
  | 512 => (execute_LDNT1D_MZ_P_BI_2 512 esize g n nreg offset t)
  | 1024 => (execute_LDNT1D_MZ_P_BI_2 1024 esize g n nreg offset t)
  | 2048 => (execute_LDNT1D_MZ_P_BI_2 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LDNT1B_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNT1B_MZ_P_BI_4 128 esize g n nreg offset t)
  | 256 => (execute_LDNT1B_MZ_P_BI_4 256 esize g n nreg offset t)
  | 512 => (execute_LDNT1B_MZ_P_BI_4 512 esize g n nreg offset t)
  | 1024 => (execute_LDNT1B_MZ_P_BI_4 1024 esize g n nreg offset t)
  | 2048 => (execute_LDNT1B_MZ_P_BI_4 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LDNT1H_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNT1H_MZ_P_BI_4 128 esize g n nreg offset t)
  | 256 => (execute_LDNT1H_MZ_P_BI_4 256 esize g n nreg offset t)
  | 512 => (execute_LDNT1H_MZ_P_BI_4 512 esize g n nreg offset t)
  | 1024 => (execute_LDNT1H_MZ_P_BI_4 1024 esize g n nreg offset t)
  | 2048 => (execute_LDNT1H_MZ_P_BI_4 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LDNT1W_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNT1W_MZ_P_BI_4 128 esize g n nreg offset t)
  | 256 => (execute_LDNT1W_MZ_P_BI_4 256 esize g n nreg offset t)
  | 512 => (execute_LDNT1W_MZ_P_BI_4 512 esize g n nreg offset t)
  | 1024 => (execute_LDNT1W_MZ_P_BI_4 1024 esize g n nreg offset t)
  | 2048 => (execute_LDNT1W_MZ_P_BI_4 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LDNT1D_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNT1D_MZ_P_BI_4 128 esize g n nreg offset t)
  | 256 => (execute_LDNT1D_MZ_P_BI_4 256 esize g n nreg offset t)
  | 512 => (execute_LDNT1D_MZ_P_BI_4 512 esize g n nreg offset t)
  | 1024 => (execute_LDNT1D_MZ_P_BI_4 1024 esize g n nreg offset t)
  | 2048 => (execute_LDNT1D_MZ_P_BI_4 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST1B_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1B_MZ_P_BI_2 128 esize g n nreg offset t)
  | 256 => (execute_ST1B_MZ_P_BI_2 256 esize g n nreg offset t)
  | 512 => (execute_ST1B_MZ_P_BI_2 512 esize g n nreg offset t)
  | 1024 => (execute_ST1B_MZ_P_BI_2 1024 esize g n nreg offset t)
  | 2048 => (execute_ST1B_MZ_P_BI_2 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST1H_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1H_MZ_P_BI_2 128 esize g n nreg offset t)
  | 256 => (execute_ST1H_MZ_P_BI_2 256 esize g n nreg offset t)
  | 512 => (execute_ST1H_MZ_P_BI_2 512 esize g n nreg offset t)
  | 1024 => (execute_ST1H_MZ_P_BI_2 1024 esize g n nreg offset t)
  | 2048 => (execute_ST1H_MZ_P_BI_2 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST1W_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1W_MZ_P_BI_2 128 esize g n nreg offset t)
  | 256 => (execute_ST1W_MZ_P_BI_2 256 esize g n nreg offset t)
  | 512 => (execute_ST1W_MZ_P_BI_2 512 esize g n nreg offset t)
  | 1024 => (execute_ST1W_MZ_P_BI_2 1024 esize g n nreg offset t)
  | 2048 => (execute_ST1W_MZ_P_BI_2 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST1D_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1D_MZ_P_BI_2 128 esize g n nreg offset t)
  | 256 => (execute_ST1D_MZ_P_BI_2 256 esize g n nreg offset t)
  | 512 => (execute_ST1D_MZ_P_BI_2 512 esize g n nreg offset t)
  | 1024 => (execute_ST1D_MZ_P_BI_2 1024 esize g n nreg offset t)
  | 2048 => (execute_ST1D_MZ_P_BI_2 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST1B_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1B_MZ_P_BI_4 128 esize g n nreg offset t)
  | 256 => (execute_ST1B_MZ_P_BI_4 256 esize g n nreg offset t)
  | 512 => (execute_ST1B_MZ_P_BI_4 512 esize g n nreg offset t)
  | 1024 => (execute_ST1B_MZ_P_BI_4 1024 esize g n nreg offset t)
  | 2048 => (execute_ST1B_MZ_P_BI_4 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST1H_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1H_MZ_P_BI_4 128 esize g n nreg offset t)
  | 256 => (execute_ST1H_MZ_P_BI_4 256 esize g n nreg offset t)
  | 512 => (execute_ST1H_MZ_P_BI_4 512 esize g n nreg offset t)
  | 1024 => (execute_ST1H_MZ_P_BI_4 1024 esize g n nreg offset t)
  | 2048 => (execute_ST1H_MZ_P_BI_4 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST1W_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1W_MZ_P_BI_4 128 esize g n nreg offset t)
  | 256 => (execute_ST1W_MZ_P_BI_4 256 esize g n nreg offset t)
  | 512 => (execute_ST1W_MZ_P_BI_4 512 esize g n nreg offset t)
  | 1024 => (execute_ST1W_MZ_P_BI_4 1024 esize g n nreg offset t)
  | 2048 => (execute_ST1W_MZ_P_BI_4 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_ST1D_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_ST1D_MZ_P_BI_4 128 esize g n nreg offset t)
  | 256 => (execute_ST1D_MZ_P_BI_4 256 esize g n nreg offset t)
  | 512 => (execute_ST1D_MZ_P_BI_4 512 esize g n nreg offset t)
  | 1024 => (execute_ST1D_MZ_P_BI_4 1024 esize g n nreg offset t)
  | 2048 => (execute_ST1D_MZ_P_BI_4 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_STNT1B_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1B_MZ_P_BI_2 128 esize g n nreg offset t)
  | 256 => (execute_STNT1B_MZ_P_BI_2 256 esize g n nreg offset t)
  | 512 => (execute_STNT1B_MZ_P_BI_2 512 esize g n nreg offset t)
  | 1024 => (execute_STNT1B_MZ_P_BI_2 1024 esize g n nreg offset t)
  | 2048 => (execute_STNT1B_MZ_P_BI_2 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_STNT1H_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1H_MZ_P_BI_2 128 esize g n nreg offset t)
  | 256 => (execute_STNT1H_MZ_P_BI_2 256 esize g n nreg offset t)
  | 512 => (execute_STNT1H_MZ_P_BI_2 512 esize g n nreg offset t)
  | 1024 => (execute_STNT1H_MZ_P_BI_2 1024 esize g n nreg offset t)
  | 2048 => (execute_STNT1H_MZ_P_BI_2 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_STNT1W_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1W_MZ_P_BI_2 128 esize g n nreg offset t)
  | 256 => (execute_STNT1W_MZ_P_BI_2 256 esize g n nreg offset t)
  | 512 => (execute_STNT1W_MZ_P_BI_2 512 esize g n nreg offset t)
  | 1024 => (execute_STNT1W_MZ_P_BI_2 1024 esize g n nreg offset t)
  | 2048 => (execute_STNT1W_MZ_P_BI_2 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_STNT1D_MZ_P_BI_2 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 4)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 2
  let t := (BitVec.toNat (Zt +++ 0#1))
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1D_MZ_P_BI_2 128 esize g n nreg offset t)
  | 256 => (execute_STNT1D_MZ_P_BI_2 256 esize g n nreg offset t)
  | 512 => (execute_STNT1D_MZ_P_BI_2 512 esize g n nreg offset t)
  | 1024 => (execute_STNT1D_MZ_P_BI_2 1024 esize g n nreg offset t)
  | 2048 => (execute_STNT1D_MZ_P_BI_2 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_STNT1B_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1B_MZ_P_BI_4 128 esize g n nreg offset t)
  | 256 => (execute_STNT1B_MZ_P_BI_4 256 esize g n nreg offset t)
  | 512 => (execute_STNT1B_MZ_P_BI_4 512 esize g n nreg offset t)
  | 1024 => (execute_STNT1B_MZ_P_BI_4 1024 esize g n nreg offset t)
  | 2048 => (execute_STNT1B_MZ_P_BI_4 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_STNT1H_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1H_MZ_P_BI_4 128 esize g n nreg offset t)
  | 256 => (execute_STNT1H_MZ_P_BI_4 256 esize g n nreg offset t)
  | 512 => (execute_STNT1H_MZ_P_BI_4 512 esize g n nreg offset t)
  | 1024 => (execute_STNT1H_MZ_P_BI_4 1024 esize g n nreg offset t)
  | 2048 => (execute_STNT1H_MZ_P_BI_4 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_STNT1W_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1W_MZ_P_BI_4 128 esize g n nreg offset t)
  | 256 => (execute_STNT1W_MZ_P_BI_4 256 esize g n nreg offset t)
  | 512 => (execute_STNT1W_MZ_P_BI_4 512 esize g n nreg offset t)
  | 1024 => (execute_STNT1W_MZ_P_BI_4 1024 esize g n nreg offset t)
  | 2048 => (execute_STNT1W_MZ_P_BI_4 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_STNT1D_MZ_P_BI_4 (imm4 : (BitVec 4)) (msz : (BitVec 2)) (PNg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 3)) (N : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat (1#1 +++ PNg))
  let nreg := 4
  let t := (BitVec.toNat (Zt +++ 0b00#2))
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_STNT1D_MZ_P_BI_4 128 esize g n nreg offset t)
  | 256 => (execute_STNT1D_MZ_P_BI_4 256 esize g n nreg offset t)
  | 512 => (execute_STNT1D_MZ_P_BI_4 512 esize g n nreg offset t)
  | 1024 => (execute_STNT1D_MZ_P_BI_4 1024 esize g n nreg offset t)
  | 2048 => (execute_STNT1D_MZ_P_BI_4 2048 esize g n nreg offset t)
  | _ => (pure ())

