import Armv9.Armv9
import Armv9.Flow
import Armv9.Arith
import Armv9.Vector
import Armv9.MonoRewrites
import Armv9.Prelude
import Armv9.Builtins
import Armv9.V8Base
import Armv9.Instrs64Sve.P01
import Armv9.Instrs64Sve.P02
import Armv9.Instrs64Sve.P03

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

def decode_SQDMLALB_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  let sel1 := 0
  let sel2 := 0
  match VL with
  | 128 => (execute_SQDMLALB_Z_ZZZ__ 128 da esize m n sel1 sel2)
  | 256 => (execute_SQDMLALB_Z_ZZZ__ 256 da esize m n sel1 sel2)
  | 512 => (execute_SQDMLALB_Z_ZZZ__ 512 da esize m n sel1 sel2)
  | 1024 => (execute_SQDMLALB_Z_ZZZ__ 1024 da esize m n sel1 sel2)
  | 2048 => (execute_SQDMLALB_Z_ZZZ__ 2048 da esize m n sel1 sel2)
  | _ => (pure ())

def decode_SMLSLT_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SMLSLT_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_SMLSLT_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_SMLSLT_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_SMLSLT_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_SMLSLT_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_SMLSLB_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SMLSLB_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_SMLSLB_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_SMLSLB_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_SMLSLB_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_SMLSLB_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_UMLSLT_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_UMLSLT_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_UMLSLT_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_UMLSLT_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_UMLSLT_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_UMLSLT_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_UMLSLB_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_UMLSLB_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_UMLSLB_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_UMLSLB_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_UMLSLB_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_UMLSLB_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_SQDMLSLT_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SQDMLSLT_Z_ZZZ__ 128 da esize m n sel1 sel2)
  | 256 => (execute_SQDMLSLT_Z_ZZZ__ 256 da esize m n sel1 sel2)
  | 512 => (execute_SQDMLSLT_Z_ZZZ__ 512 da esize m n sel1 sel2)
  | 1024 => (execute_SQDMLSLT_Z_ZZZ__ 1024 da esize m n sel1 sel2)
  | 2048 => (execute_SQDMLSLT_Z_ZZZ__ 2048 da esize m n sel1 sel2)
  | _ => (pure ())

def decode_SQDMLSLB_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  let sel1 := 0
  let sel2 := 0
  match VL with
  | 128 => (execute_SQDMLSLB_Z_ZZZ__ 128 da esize m n sel1 sel2)
  | 256 => (execute_SQDMLSLB_Z_ZZZ__ 256 da esize m n sel1 sel2)
  | 512 => (execute_SQDMLSLB_Z_ZZZ__ 512 da esize m n sel1 sel2)
  | 1024 => (execute_SQDMLSLB_Z_ZZZ__ 1024 da esize m n sel1 sel2)
  | 2048 => (execute_SQDMLSLB_Z_ZZZ__ 2048 da esize m n sel1 sel2)
  | _ => (pure ())

def decode_SABALT_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SABALT_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_SABALT_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_SABALT_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_SABALT_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_SABALT_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_SABALB_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SABALB_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_SABALB_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_SABALB_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_SABALB_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_SABALB_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_UABALT_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_UABALT_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_UABALT_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_UABALT_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_UABALT_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_UABALT_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_UABALB_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_UABALB_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_UABALB_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_UABALB_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_UABALB_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_UABALB_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_SABA_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SABA_Z_ZZZ__ 128 da esize m n is_unsigned)
  | 256 => (execute_SABA_Z_ZZZ__ 256 da esize m n is_unsigned)
  | 512 => (execute_SABA_Z_ZZZ__ 512 da esize m n is_unsigned)
  | 1024 => (execute_SABA_Z_ZZZ__ 1024 da esize m n is_unsigned)
  | 2048 => (execute_SABA_Z_ZZZ__ 2048 da esize m n is_unsigned)
  | _ => (pure ())

def decode_UABA_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UABA_Z_ZZZ__ 128 da esize m n is_unsigned)
  | 256 => (execute_UABA_Z_ZZZ__ 256 da esize m n is_unsigned)
  | 512 => (execute_UABA_Z_ZZZ__ 512 da esize m n is_unsigned)
  | 1024 => (execute_UABA_Z_ZZZ__ 1024 da esize m n is_unsigned)
  | 2048 => (execute_UABA_Z_ZZZ__ 2048 da esize m n is_unsigned)
  | _ => (pure ())

def decode_SADDWT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SADDWT_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_SADDWT_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_SADDWT_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_SADDWT_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_SADDWT_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_SADDWB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SADDWB_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_SADDWB_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_SADDWB_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_SADDWB_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_SADDWB_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_UADDWT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_UADDWT_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_UADDWT_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_UADDWT_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_UADDWT_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_UADDWT_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_UADDWB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_UADDWB_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_UADDWB_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_UADDWB_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_UADDWB_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_UADDWB_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_SSUBWT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SSUBWT_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_SSUBWT_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_SSUBWT_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_SSUBWT_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_SSUBWT_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_SSUBWB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SSUBWB_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_SSUBWB_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_SSUBWB_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_SSUBWB_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_SSUBWB_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_USUBWT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_USUBWT_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_USUBWT_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_USUBWT_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_USUBWT_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_USUBWT_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_USUBWB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_USUBWB_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_USUBWB_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_USUBWB_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_USUBWB_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_USUBWB_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_PMUL_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_PMUL_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_PMUL_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_PMUL_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_PMUL_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_PMUL_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_PMULLT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize : Nat := 16
  let esize ← (( do
    match (size : BitVec 2) with
    | 0b01 => (pure 16)
    | 0b11 => (pure 64)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_PMULLT_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_PMULLT_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_PMULLT_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_PMULLT_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_PMULLT_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_PMULLB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize : Nat := 16
  let esize ← (( do
    match (size : BitVec 2) with
    | 0b01 => (pure 16)
    | 0b11 => (pure 64)
    | _ => sailThrow ((Error_Undefined ())) ) : SailM Int )
  let esize := esize
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_PMULLB_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_PMULLB_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_PMULLB_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_PMULLB_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_PMULLB_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_PMULLT_Z_ZZ_Q (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2PMULL128 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 128
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_PMULLT_Z_ZZ_Q 128 d esize m n)
  | 256 => (execute_PMULLT_Z_ZZ_Q 256 d esize m n)
  | 512 => (execute_PMULLT_Z_ZZ_Q 512 d esize m n)
  | 1024 => (execute_PMULLT_Z_ZZ_Q 1024 d esize m n)
  | 2048 => (execute_PMULLT_Z_ZZ_Q 2048 d esize m n)
  | _ => (pure ())

def decode_PMULLB_Z_ZZ_Q (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2PMULL128 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 128
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_PMULLB_Z_ZZ_Q 128 d esize m n)
  | 256 => (execute_PMULLB_Z_ZZ_Q 256 d esize m n)
  | 512 => (execute_PMULLB_Z_ZZ_Q 512 d esize m n)
  | 1024 => (execute_PMULLB_Z_ZZ_Q 1024 d esize m n)
  | 2048 => (execute_PMULLB_Z_ZZ_Q 2048 d esize m n)
  | _ => (pure ())

def decode_SQSHL_Z_P_ZZ__ (size : (BitVec 2)) (Q : (BitVec 1)) (R : (BitVec 1)) (N : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SQSHL_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_SQSHL_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_SQSHL_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_SQSHL_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_SQSHL_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_UQSHL_Z_P_ZZ__ (size : (BitVec 2)) (Q : (BitVec 1)) (R : (BitVec 1)) (N : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_UQSHL_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_UQSHL_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_UQSHL_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_UQSHL_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_UQSHL_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_SRSHL_Z_P_ZZ__ (size : (BitVec 2)) (Q : (BitVec 1)) (R : (BitVec 1)) (N : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SRSHL_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_SRSHL_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_SRSHL_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_SRSHL_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_SRSHL_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_URSHL_Z_P_ZZ__ (size : (BitVec 2)) (Q : (BitVec 1)) (R : (BitVec 1)) (N : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_URSHL_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_URSHL_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_URSHL_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_URSHL_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_URSHL_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_SQRSHL_Z_P_ZZ__ (size : (BitVec 2)) (Q : (BitVec 1)) (R : (BitVec 1)) (N : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SQRSHL_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_SQRSHL_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_SQRSHL_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_SQRSHL_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_SQRSHL_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_UQRSHL_Z_P_ZZ__ (size : (BitVec 2)) (Q : (BitVec 1)) (R : (BitVec 1)) (N : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_UQRSHL_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_UQRSHL_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_UQRSHL_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_UQRSHL_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_UQRSHL_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_SQSHLR_Z_P_ZZ__ (size : (BitVec 2)) (Q : (BitVec 1)) (R : (BitVec 1)) (N : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SQSHLR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_SQSHLR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_SQSHLR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_SQSHLR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_SQSHLR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_UQSHLR_Z_P_ZZ__ (size : (BitVec 2)) (Q : (BitVec 1)) (R : (BitVec 1)) (N : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_UQSHLR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_UQSHLR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_UQSHLR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_UQSHLR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_UQSHLR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_SRSHLR_Z_P_ZZ__ (size : (BitVec 2)) (Q : (BitVec 1)) (R : (BitVec 1)) (N : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SRSHLR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_SRSHLR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_SRSHLR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_SRSHLR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_SRSHLR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_URSHLR_Z_P_ZZ__ (size : (BitVec 2)) (Q : (BitVec 1)) (R : (BitVec 1)) (N : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_URSHLR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_URSHLR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_URSHLR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_URSHLR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_URSHLR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_SQRSHLR_Z_P_ZZ__ (size : (BitVec 2)) (Q : (BitVec 1)) (R : (BitVec 1)) (N : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SQRSHLR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_SQRSHLR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_SQRSHLR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_SQRSHLR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_SQRSHLR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_UQRSHLR_Z_P_ZZ__ (size : (BitVec 2)) (Q : (BitVec 1)) (R : (BitVec 1)) (N : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_UQRSHLR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_UQRSHLR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_UQRSHLR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_UQRSHLR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_UQRSHLR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_ADDHNB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_ADDHNB_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_ADDHNB_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_ADDHNB_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_ADDHNB_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_ADDHNB_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_ADDHNT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_ADDHNT_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_ADDHNT_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_ADDHNT_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_ADDHNT_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_ADDHNT_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_SUBHNB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SUBHNB_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_SUBHNB_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_SUBHNB_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_SUBHNB_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_SUBHNB_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_SUBHNT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SUBHNT_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_SUBHNT_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_SUBHNT_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_SUBHNT_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_SUBHNT_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_RADDHNB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_RADDHNB_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_RADDHNB_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_RADDHNB_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_RADDHNB_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_RADDHNB_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_RADDHNT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_RADDHNT_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_RADDHNT_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_RADDHNT_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_RADDHNT_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_RADDHNT_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_RSUBHNB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_RSUBHNB_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_RSUBHNB_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_RSUBHNB_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_RSUBHNB_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_RSUBHNB_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_RSUBHNT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (R : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_RSUBHNT_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_RSUBHNT_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_RSUBHNT_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_RSUBHNT_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_RSUBHNT_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_SABDLB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SABDLB_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_SABDLB_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_SABDLB_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_SABDLB_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_SABDLB_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_SABDLT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_SABDLT_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_SABDLT_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_SABDLT_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_SABDLT_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_SABDLT_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_UABDLB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_UABDLB_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_UABDLB_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_UABDLB_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_UABDLB_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_UABDLB_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_UABDLT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_UABDLT_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_UABDLT_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_UABDLT_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_UABDLT_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_UABDLT_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_SADDLB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let sel1 := 0
  let sel2 := 0
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SADDLB_Z_ZZ__ 128 d esize m n sel1 sel2 is_unsigned)
  | 256 => (execute_SADDLB_Z_ZZ__ 256 d esize m n sel1 sel2 is_unsigned)
  | 512 => (execute_SADDLB_Z_ZZ__ 512 d esize m n sel1 sel2 is_unsigned)
  | 1024 => (execute_SADDLB_Z_ZZ__ 1024 d esize m n sel1 sel2 is_unsigned)
  | 2048 => (execute_SADDLB_Z_ZZ__ 2048 d esize m n sel1 sel2 is_unsigned)
  | _ => (pure ())

def decode_SADDLT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let sel1 := 1
  let sel2 := 1
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SADDLT_Z_ZZ__ 128 d esize m n sel1 sel2 is_unsigned)
  | 256 => (execute_SADDLT_Z_ZZ__ 256 d esize m n sel1 sel2 is_unsigned)
  | 512 => (execute_SADDLT_Z_ZZ__ 512 d esize m n sel1 sel2 is_unsigned)
  | 1024 => (execute_SADDLT_Z_ZZ__ 1024 d esize m n sel1 sel2 is_unsigned)
  | 2048 => (execute_SADDLT_Z_ZZ__ 2048 d esize m n sel1 sel2 is_unsigned)
  | _ => (pure ())

def decode_SSUBLB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let sel1 := 0
  let sel2 := 0
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SSUBLB_Z_ZZ__ 128 d esize m n sel1 sel2 is_unsigned)
  | 256 => (execute_SSUBLB_Z_ZZ__ 256 d esize m n sel1 sel2 is_unsigned)
  | 512 => (execute_SSUBLB_Z_ZZ__ 512 d esize m n sel1 sel2 is_unsigned)
  | 1024 => (execute_SSUBLB_Z_ZZ__ 1024 d esize m n sel1 sel2 is_unsigned)
  | 2048 => (execute_SSUBLB_Z_ZZ__ 2048 d esize m n sel1 sel2 is_unsigned)
  | _ => (pure ())

def decode_SSUBLT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let sel1 := 1
  let sel2 := 1
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SSUBLT_Z_ZZ__ 128 d esize m n sel1 sel2 is_unsigned)
  | 256 => (execute_SSUBLT_Z_ZZ__ 256 d esize m n sel1 sel2 is_unsigned)
  | 512 => (execute_SSUBLT_Z_ZZ__ 512 d esize m n sel1 sel2 is_unsigned)
  | 1024 => (execute_SSUBLT_Z_ZZ__ 1024 d esize m n sel1 sel2 is_unsigned)
  | 2048 => (execute_SSUBLT_Z_ZZ__ 2048 d esize m n sel1 sel2 is_unsigned)
  | _ => (pure ())

def decode_UADDLB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let sel1 := 0
  let sel2 := 0
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UADDLB_Z_ZZ__ 128 d esize m n sel1 sel2 is_unsigned)
  | 256 => (execute_UADDLB_Z_ZZ__ 256 d esize m n sel1 sel2 is_unsigned)
  | 512 => (execute_UADDLB_Z_ZZ__ 512 d esize m n sel1 sel2 is_unsigned)
  | 1024 => (execute_UADDLB_Z_ZZ__ 1024 d esize m n sel1 sel2 is_unsigned)
  | 2048 => (execute_UADDLB_Z_ZZ__ 2048 d esize m n sel1 sel2 is_unsigned)
  | _ => (pure ())

def decode_UADDLT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let sel1 := 1
  let sel2 := 1
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UADDLT_Z_ZZ__ 128 d esize m n sel1 sel2 is_unsigned)
  | 256 => (execute_UADDLT_Z_ZZ__ 256 d esize m n sel1 sel2 is_unsigned)
  | 512 => (execute_UADDLT_Z_ZZ__ 512 d esize m n sel1 sel2 is_unsigned)
  | 1024 => (execute_UADDLT_Z_ZZ__ 1024 d esize m n sel1 sel2 is_unsigned)
  | 2048 => (execute_UADDLT_Z_ZZ__ 2048 d esize m n sel1 sel2 is_unsigned)
  | _ => (pure ())

def decode_USUBLB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let sel1 := 0
  let sel2 := 0
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_USUBLB_Z_ZZ__ 128 d esize m n sel1 sel2 is_unsigned)
  | 256 => (execute_USUBLB_Z_ZZ__ 256 d esize m n sel1 sel2 is_unsigned)
  | 512 => (execute_USUBLB_Z_ZZ__ 512 d esize m n sel1 sel2 is_unsigned)
  | 1024 => (execute_USUBLB_Z_ZZ__ 1024 d esize m n sel1 sel2 is_unsigned)
  | 2048 => (execute_USUBLB_Z_ZZ__ 2048 d esize m n sel1 sel2 is_unsigned)
  | _ => (pure ())

def decode_USUBLT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let sel1 := 1
  let sel2 := 1
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_USUBLT_Z_ZZ__ 128 d esize m n sel1 sel2 is_unsigned)
  | 256 => (execute_USUBLT_Z_ZZ__ 256 d esize m n sel1 sel2 is_unsigned)
  | 512 => (execute_USUBLT_Z_ZZ__ 512 d esize m n sel1 sel2 is_unsigned)
  | 1024 => (execute_USUBLT_Z_ZZ__ 1024 d esize m n sel1 sel2 is_unsigned)
  | 2048 => (execute_USUBLT_Z_ZZ__ 2048 d esize m n sel1 sel2 is_unsigned)
  | _ => (pure ())

def decode_SADDLBT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (tb : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let sel1 := 0
  let sel2 := 1
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SADDLBT_Z_ZZ__ 128 d esize m n sel1 sel2 is_unsigned)
  | 256 => (execute_SADDLBT_Z_ZZ__ 256 d esize m n sel1 sel2 is_unsigned)
  | 512 => (execute_SADDLBT_Z_ZZ__ 512 d esize m n sel1 sel2 is_unsigned)
  | 1024 => (execute_SADDLBT_Z_ZZ__ 1024 d esize m n sel1 sel2 is_unsigned)
  | 2048 => (execute_SADDLBT_Z_ZZ__ 2048 d esize m n sel1 sel2 is_unsigned)
  | _ => (pure ())

def decode_SSUBLBT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (tb : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let sel1 := 0
  let sel2 := 1
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SSUBLBT_Z_ZZ__ 128 d esize m n sel1 sel2 is_unsigned)
  | 256 => (execute_SSUBLBT_Z_ZZ__ 256 d esize m n sel1 sel2 is_unsigned)
  | 512 => (execute_SSUBLBT_Z_ZZ__ 512 d esize m n sel1 sel2 is_unsigned)
  | 1024 => (execute_SSUBLBT_Z_ZZ__ 1024 d esize m n sel1 sel2 is_unsigned)
  | 2048 => (execute_SSUBLBT_Z_ZZ__ 2048 d esize m n sel1 sel2 is_unsigned)
  | _ => (pure ())

def decode_SSUBLTB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (tb : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let sel1 := 1
  let sel2 := 0
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SSUBLTB_Z_ZZ__ 128 d esize m n sel1 sel2 is_unsigned)
  | 256 => (execute_SSUBLTB_Z_ZZ__ 256 d esize m n sel1 sel2 is_unsigned)
  | 512 => (execute_SSUBLTB_Z_ZZ__ 512 d esize m n sel1 sel2 is_unsigned)
  | 1024 => (execute_SSUBLTB_Z_ZZ__ 1024 d esize m n sel1 sel2 is_unsigned)
  | 2048 => (execute_SSUBLTB_Z_ZZ__ 2048 d esize m n sel1 sel2 is_unsigned)
  | _ => (pure ())

def decode_CADD_Z_ZZ__ (size : (BitVec 2)) (rot : (BitVec 1)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Zm)
  let dn := (BitVec.toNat Zdn)
  let sub_i : Bool := (rot == 0#1)
  let sub_r : Bool := (rot == 1#1)
  match VL with
  | 128 => (execute_CADD_Z_ZZ__ 128 dn esize m sub_i sub_r)
  | 256 => (execute_CADD_Z_ZZ__ 256 dn esize m sub_i sub_r)
  | 512 => (execute_CADD_Z_ZZ__ 512 dn esize m sub_i sub_r)
  | 1024 => (execute_CADD_Z_ZZ__ 1024 dn esize m sub_i sub_r)
  | 2048 => (execute_CADD_Z_ZZ__ 2048 dn esize m sub_i sub_r)
  | _ => (pure ())

def decode_SQCADD_Z_ZZ__ (size : (BitVec 2)) (rot : (BitVec 1)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let m := (BitVec.toNat Zm)
  let dn := (BitVec.toNat Zdn)
  let sub_i : Bool := (rot == 0#1)
  let sub_r : Bool := (rot == 1#1)
  match VL with
  | 128 => (execute_SQCADD_Z_ZZ__ 128 dn esize m sub_i sub_r)
  | 256 => (execute_SQCADD_Z_ZZ__ 256 dn esize m sub_i sub_r)
  | 512 => (execute_SQCADD_Z_ZZ__ 512 dn esize m sub_i sub_r)
  | 1024 => (execute_SQCADD_Z_ZZ__ 1024 dn esize m sub_i sub_r)
  | 2048 => (execute_SQCADD_Z_ZZ__ 2048 dn esize m sub_i sub_r)
  | _ => (pure ())

def decode_CMLA_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel_a := (BitVec.toNat (BitVec.join1 [(BitVec.access rot 0)]))
  let sel_b := (BitVec.toNat (Complement.complement (BitVec.join1 [(BitVec.access rot 0)])))
  let sub_r : Bool := ((BitVec.join1 [(BitVec.access rot 0)]) != (BitVec.join1 [(BitVec.access rot 1)]))
  let sub_i : Bool := ((BitVec.join1 [(BitVec.access rot 1)]) == 1#1)
  match VL with
  | 128 => (execute_CMLA_Z_ZZZ__ 128 da esize m n sel_a sel_b sub_i sub_r)
  | 256 => (execute_CMLA_Z_ZZZ__ 256 da esize m n sel_a sel_b sub_i sub_r)
  | 512 => (execute_CMLA_Z_ZZZ__ 512 da esize m n sel_a sel_b sub_i sub_r)
  | 1024 => (execute_CMLA_Z_ZZZ__ 1024 da esize m n sel_a sel_b sub_i sub_r)
  | 2048 => (execute_CMLA_Z_ZZZ__ 2048 da esize m n sel_a sel_b sub_i sub_r)
  | _ => (pure ())

def decode_CMLA_Z_ZZZi_H (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
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
  let sub_r : Bool := ((BitVec.join1 [(BitVec.access rot 0)]) != (BitVec.join1 [(BitVec.access rot 1)]))
  let sub_i : Bool := ((BitVec.join1 [(BitVec.access rot 1)]) == 1#1)
  match VL with
  | 128 => (execute_CMLA_Z_ZZZi_H 128 da esize index m n sel_a sel_b sub_i sub_r)
  | 256 => (execute_CMLA_Z_ZZZi_H 256 da esize index m n sel_a sel_b sub_i sub_r)
  | 512 => (execute_CMLA_Z_ZZZi_H 512 da esize index m n sel_a sel_b sub_i sub_r)
  | 1024 => (execute_CMLA_Z_ZZZi_H 1024 da esize index m n sel_a sel_b sub_i sub_r)
  | 2048 => (execute_CMLA_Z_ZZZi_H 2048 da esize index m n sel_a sel_b sub_i sub_r)
  | _ => (pure ())

def decode_CMLA_Z_ZZZi_S (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
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
  let sub_r : Bool := ((BitVec.join1 [(BitVec.access rot 0)]) != (BitVec.join1 [(BitVec.access rot 1)]))
  let sub_i : Bool := ((BitVec.join1 [(BitVec.access rot 1)]) == 1#1)
  match VL with
  | 128 => (execute_CMLA_Z_ZZZi_S 128 da esize index m n sel_a sel_b sub_i sub_r)
  | 256 => (execute_CMLA_Z_ZZZi_S 256 da esize index m n sel_a sel_b sub_i sub_r)
  | 512 => (execute_CMLA_Z_ZZZi_S 512 da esize index m n sel_a sel_b sub_i sub_r)
  | 1024 => (execute_CMLA_Z_ZZZi_S 1024 da esize index m n sel_a sel_b sub_i sub_r)
  | 2048 => (execute_CMLA_Z_ZZZi_S 2048 da esize index m n sel_a sel_b sub_i sub_r)
  | _ => (pure ())

def decode_SQRDCMLAH_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel_a := (BitVec.toNat (BitVec.join1 [(BitVec.access rot 0)]))
  let sel_b := (BitVec.toNat (Complement.complement (BitVec.join1 [(BitVec.access rot 0)])))
  let sub_r : Bool := ((BitVec.join1 [(BitVec.access rot 0)]) != (BitVec.join1 [(BitVec.access rot 1)]))
  let sub_i : Bool := ((BitVec.join1 [(BitVec.access rot 1)]) == 1#1)
  match VL with
  | 128 => (execute_SQRDCMLAH_Z_ZZZ__ 128 da esize m n sel_a sel_b sub_i sub_r)
  | 256 => (execute_SQRDCMLAH_Z_ZZZ__ 256 da esize m n sel_a sel_b sub_i sub_r)
  | 512 => (execute_SQRDCMLAH_Z_ZZZ__ 512 da esize m n sel_a sel_b sub_i sub_r)
  | 1024 => (execute_SQRDCMLAH_Z_ZZZ__ 1024 da esize m n sel_a sel_b sub_i sub_r)
  | 2048 => (execute_SQRDCMLAH_Z_ZZZ__ 2048 da esize m n sel_a sel_b sub_i sub_r)
  | _ => (pure ())

def decode_SQRDCMLAH_Z_ZZZi_H (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
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
  let sub_r : Bool := ((BitVec.join1 [(BitVec.access rot 0)]) != (BitVec.join1 [(BitVec.access rot 1)]))
  let sub_i : Bool := ((BitVec.join1 [(BitVec.access rot 1)]) == 1#1)
  match VL with
  | 128 => (execute_SQRDCMLAH_Z_ZZZi_H 128 da esize index m n sel_a sel_b sub_i sub_r)
  | 256 => (execute_SQRDCMLAH_Z_ZZZi_H 256 da esize index m n sel_a sel_b sub_i sub_r)
  | 512 => (execute_SQRDCMLAH_Z_ZZZi_H 512 da esize index m n sel_a sel_b sub_i sub_r)
  | 1024 => (execute_SQRDCMLAH_Z_ZZZi_H 1024 da esize index m n sel_a sel_b sub_i sub_r)
  | 2048 => (execute_SQRDCMLAH_Z_ZZZi_H 2048 da esize index m n sel_a sel_b sub_i sub_r)
  | _ => (pure ())

def decode_SQRDCMLAH_Z_ZZZi_S (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
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
  let sub_r : Bool := ((BitVec.join1 [(BitVec.access rot 0)]) != (BitVec.join1 [(BitVec.access rot 1)]))
  let sub_i : Bool := ((BitVec.join1 [(BitVec.access rot 1)]) == 1#1)
  match VL with
  | 128 => (execute_SQRDCMLAH_Z_ZZZi_S 128 da esize index m n sel_a sel_b sub_i sub_r)
  | 256 => (execute_SQRDCMLAH_Z_ZZZi_S 256 da esize index m n sel_a sel_b sub_i sub_r)
  | 512 => (execute_SQRDCMLAH_Z_ZZZi_S 512 da esize index m n sel_a sel_b sub_i sub_r)
  | 1024 => (execute_SQRDCMLAH_Z_ZZZi_S 1024 da esize index m n sel_a sel_b sub_i sub_r)
  | 2048 => (execute_SQRDCMLAH_Z_ZZZi_S 2048 da esize index m n sel_a sel_b sub_i sub_r)
  | _ => (pure ())

def decode_MUL_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_MUL_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_MUL_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_MUL_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_MUL_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_MUL_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_MUL_Z_ZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_MUL_Z_ZZi_H 128 d esize index m n)
  | 256 => (execute_MUL_Z_ZZi_H 256 d esize index m n)
  | 512 => (execute_MUL_Z_ZZi_H 512 d esize index m n)
  | 1024 => (execute_MUL_Z_ZZi_H 1024 d esize index m n)
  | 2048 => (execute_MUL_Z_ZZi_H 2048 d esize index m n)
  | _ => (pure ())

def decode_MUL_Z_ZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_MUL_Z_ZZi_S 128 d esize index m n)
  | 256 => (execute_MUL_Z_ZZi_S 256 d esize index m n)
  | 512 => (execute_MUL_Z_ZZi_S 512 d esize index m n)
  | 1024 => (execute_MUL_Z_ZZi_S 1024 d esize index m n)
  | 2048 => (execute_MUL_Z_ZZi_S 2048 d esize index m n)
  | _ => (pure ())

def decode_MUL_Z_ZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let index := (BitVec.toNat i1)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_MUL_Z_ZZi_D 128 d esize index m n)
  | 256 => (execute_MUL_Z_ZZi_D 256 d esize index m n)
  | 512 => (execute_MUL_Z_ZZi_D 512 d esize index m n)
  | 1024 => (execute_MUL_Z_ZZi_D 1024 d esize index m n)
  | 2048 => (execute_MUL_Z_ZZi_D 2048 d esize index m n)
  | _ => (pure ())

def decode_MLA_Z_ZZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_MLA_Z_ZZZi_H 128 da esize index m n)
  | 256 => (execute_MLA_Z_ZZZi_H 256 da esize index m n)
  | 512 => (execute_MLA_Z_ZZZi_H 512 da esize index m n)
  | 1024 => (execute_MLA_Z_ZZZi_H 1024 da esize index m n)
  | 2048 => (execute_MLA_Z_ZZZi_H 2048 da esize index m n)
  | _ => (pure ())

def decode_MLA_Z_ZZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_MLA_Z_ZZZi_S 128 da esize index m n)
  | 256 => (execute_MLA_Z_ZZZi_S 256 da esize index m n)
  | 512 => (execute_MLA_Z_ZZZi_S 512 da esize index m n)
  | 1024 => (execute_MLA_Z_ZZZi_S 1024 da esize index m n)
  | 2048 => (execute_MLA_Z_ZZZi_S 2048 da esize index m n)
  | _ => (pure ())

def decode_MLA_Z_ZZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let index := (BitVec.toNat i1)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_MLA_Z_ZZZi_D 128 da esize index m n)
  | 256 => (execute_MLA_Z_ZZZi_D 256 da esize index m n)
  | 512 => (execute_MLA_Z_ZZZi_D 512 da esize index m n)
  | 1024 => (execute_MLA_Z_ZZZi_D 1024 da esize index m n)
  | 2048 => (execute_MLA_Z_ZZZi_D 2048 da esize index m n)
  | _ => (pure ())

def decode_MLS_Z_ZZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_MLS_Z_ZZZi_H 128 da esize index m n)
  | 256 => (execute_MLS_Z_ZZZi_H 256 da esize index m n)
  | 512 => (execute_MLS_Z_ZZZi_H 512 da esize index m n)
  | 1024 => (execute_MLS_Z_ZZZi_H 1024 da esize index m n)
  | 2048 => (execute_MLS_Z_ZZZi_H 2048 da esize index m n)
  | _ => (pure ())

def decode_MLS_Z_ZZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_MLS_Z_ZZZi_S 128 da esize index m n)
  | 256 => (execute_MLS_Z_ZZZi_S 256 da esize index m n)
  | 512 => (execute_MLS_Z_ZZZi_S 512 da esize index m n)
  | 1024 => (execute_MLS_Z_ZZZi_S 1024 da esize index m n)
  | 2048 => (execute_MLS_Z_ZZZi_S 2048 da esize index m n)
  | _ => (pure ())

def decode_MLS_Z_ZZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let index := (BitVec.toNat i1)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_MLS_Z_ZZZi_D 128 da esize index m n)
  | 256 => (execute_MLS_Z_ZZZi_D 256 da esize index m n)
  | 512 => (execute_MLS_Z_ZZZi_D 512 da esize index m n)
  | 1024 => (execute_MLS_Z_ZZZi_D 1024 da esize index m n)
  | 2048 => (execute_MLS_Z_ZZZi_D 2048 da esize index m n)
  | _ => (pure ())

def decode_SMULLB_Z_ZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let sel := 0
  match VL with
  | 128 => (execute_SMULLB_Z_ZZi_S 128 d esize index m n sel)
  | 256 => (execute_SMULLB_Z_ZZi_S 256 d esize index m n sel)
  | 512 => (execute_SMULLB_Z_ZZi_S 512 d esize index m n sel)
  | 1024 => (execute_SMULLB_Z_ZZi_S 1024 d esize index m n sel)
  | 2048 => (execute_SMULLB_Z_ZZi_S 2048 d esize index m n sel)
  | _ => (pure ())

def decode_SMULLB_Z_ZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let sel := 0
  match VL with
  | 128 => (execute_SMULLB_Z_ZZi_D 128 d esize index m n sel)
  | 256 => (execute_SMULLB_Z_ZZi_D 256 d esize index m n sel)
  | 512 => (execute_SMULLB_Z_ZZi_D 512 d esize index m n sel)
  | 1024 => (execute_SMULLB_Z_ZZi_D 1024 d esize index m n sel)
  | 2048 => (execute_SMULLB_Z_ZZi_D 2048 d esize index m n sel)
  | _ => (pure ())

def decode_SMULLT_Z_ZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let sel := 1
  match VL with
  | 128 => (execute_SMULLT_Z_ZZi_S 128 d esize index m n sel)
  | 256 => (execute_SMULLT_Z_ZZi_S 256 d esize index m n sel)
  | 512 => (execute_SMULLT_Z_ZZi_S 512 d esize index m n sel)
  | 1024 => (execute_SMULLT_Z_ZZi_S 1024 d esize index m n sel)
  | 2048 => (execute_SMULLT_Z_ZZi_S 2048 d esize index m n sel)
  | _ => (pure ())

def decode_SMULLT_Z_ZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let sel := 1
  match VL with
  | 128 => (execute_SMULLT_Z_ZZi_D 128 d esize index m n sel)
  | 256 => (execute_SMULLT_Z_ZZi_D 256 d esize index m n sel)
  | 512 => (execute_SMULLT_Z_ZZi_D 512 d esize index m n sel)
  | 1024 => (execute_SMULLT_Z_ZZi_D 1024 d esize index m n sel)
  | 2048 => (execute_SMULLT_Z_ZZi_D 2048 d esize index m n sel)
  | _ => (pure ())

def decode_UMULLB_Z_ZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let sel := 0
  match VL with
  | 128 => (execute_UMULLB_Z_ZZi_S 128 d esize index m n sel)
  | 256 => (execute_UMULLB_Z_ZZi_S 256 d esize index m n sel)
  | 512 => (execute_UMULLB_Z_ZZi_S 512 d esize index m n sel)
  | 1024 => (execute_UMULLB_Z_ZZi_S 1024 d esize index m n sel)
  | 2048 => (execute_UMULLB_Z_ZZi_S 2048 d esize index m n sel)
  | _ => (pure ())

def decode_UMULLB_Z_ZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let sel := 0
  match VL with
  | 128 => (execute_UMULLB_Z_ZZi_D 128 d esize index m n sel)
  | 256 => (execute_UMULLB_Z_ZZi_D 256 d esize index m n sel)
  | 512 => (execute_UMULLB_Z_ZZi_D 512 d esize index m n sel)
  | 1024 => (execute_UMULLB_Z_ZZi_D 1024 d esize index m n sel)
  | 2048 => (execute_UMULLB_Z_ZZi_D 2048 d esize index m n sel)
  | _ => (pure ())

def decode_UMULLT_Z_ZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let sel := 1
  match VL with
  | 128 => (execute_UMULLT_Z_ZZi_S 128 d esize index m n sel)
  | 256 => (execute_UMULLT_Z_ZZi_S 256 d esize index m n sel)
  | 512 => (execute_UMULLT_Z_ZZi_S 512 d esize index m n sel)
  | 1024 => (execute_UMULLT_Z_ZZi_S 1024 d esize index m n sel)
  | 2048 => (execute_UMULLT_Z_ZZi_S 2048 d esize index m n sel)
  | _ => (pure ())

def decode_UMULLT_Z_ZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let sel := 1
  match VL with
  | 128 => (execute_UMULLT_Z_ZZi_D 128 d esize index m n sel)
  | 256 => (execute_UMULLT_Z_ZZi_D 256 d esize index m n sel)
  | 512 => (execute_UMULLT_Z_ZZi_D 512 d esize index m n sel)
  | 1024 => (execute_UMULLT_Z_ZZi_D 1024 d esize index m n sel)
  | 2048 => (execute_UMULLT_Z_ZZi_D 2048 d esize index m n sel)
  | _ => (pure ())

def decode_SMLALB_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 0
  match VL with
  | 128 => (execute_SMLALB_Z_ZZZi_S 128 da esize index m n sel)
  | 256 => (execute_SMLALB_Z_ZZZi_S 256 da esize index m n sel)
  | 512 => (execute_SMLALB_Z_ZZZi_S 512 da esize index m n sel)
  | 1024 => (execute_SMLALB_Z_ZZZi_S 1024 da esize index m n sel)
  | 2048 => (execute_SMLALB_Z_ZZZi_S 2048 da esize index m n sel)
  | _ => (pure ())

def decode_SMLALB_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 0
  match VL with
  | 128 => (execute_SMLALB_Z_ZZZi_D 128 da esize index m n sel)
  | 256 => (execute_SMLALB_Z_ZZZi_D 256 da esize index m n sel)
  | 512 => (execute_SMLALB_Z_ZZZi_D 512 da esize index m n sel)
  | 1024 => (execute_SMLALB_Z_ZZZi_D 1024 da esize index m n sel)
  | 2048 => (execute_SMLALB_Z_ZZZi_D 2048 da esize index m n sel)
  | _ => (pure ())

def decode_SMLALT_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 1
  match VL with
  | 128 => (execute_SMLALT_Z_ZZZi_S 128 da esize index m n sel)
  | 256 => (execute_SMLALT_Z_ZZZi_S 256 da esize index m n sel)
  | 512 => (execute_SMLALT_Z_ZZZi_S 512 da esize index m n sel)
  | 1024 => (execute_SMLALT_Z_ZZZi_S 1024 da esize index m n sel)
  | 2048 => (execute_SMLALT_Z_ZZZi_S 2048 da esize index m n sel)
  | _ => (pure ())

def decode_SMLALT_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 1
  match VL with
  | 128 => (execute_SMLALT_Z_ZZZi_D 128 da esize index m n sel)
  | 256 => (execute_SMLALT_Z_ZZZi_D 256 da esize index m n sel)
  | 512 => (execute_SMLALT_Z_ZZZi_D 512 da esize index m n sel)
  | 1024 => (execute_SMLALT_Z_ZZZi_D 1024 da esize index m n sel)
  | 2048 => (execute_SMLALT_Z_ZZZi_D 2048 da esize index m n sel)
  | _ => (pure ())

def decode_UMLALB_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 0
  match VL with
  | 128 => (execute_UMLALB_Z_ZZZi_S 128 da esize index m n sel)
  | 256 => (execute_UMLALB_Z_ZZZi_S 256 da esize index m n sel)
  | 512 => (execute_UMLALB_Z_ZZZi_S 512 da esize index m n sel)
  | 1024 => (execute_UMLALB_Z_ZZZi_S 1024 da esize index m n sel)
  | 2048 => (execute_UMLALB_Z_ZZZi_S 2048 da esize index m n sel)
  | _ => (pure ())

def decode_UMLALB_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 0
  match VL with
  | 128 => (execute_UMLALB_Z_ZZZi_D 128 da esize index m n sel)
  | 256 => (execute_UMLALB_Z_ZZZi_D 256 da esize index m n sel)
  | 512 => (execute_UMLALB_Z_ZZZi_D 512 da esize index m n sel)
  | 1024 => (execute_UMLALB_Z_ZZZi_D 1024 da esize index m n sel)
  | 2048 => (execute_UMLALB_Z_ZZZi_D 2048 da esize index m n sel)
  | _ => (pure ())

def decode_UMLALT_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 1
  match VL with
  | 128 => (execute_UMLALT_Z_ZZZi_S 128 da esize index m n sel)
  | 256 => (execute_UMLALT_Z_ZZZi_S 256 da esize index m n sel)
  | 512 => (execute_UMLALT_Z_ZZZi_S 512 da esize index m n sel)
  | 1024 => (execute_UMLALT_Z_ZZZi_S 1024 da esize index m n sel)
  | 2048 => (execute_UMLALT_Z_ZZZi_S 2048 da esize index m n sel)
  | _ => (pure ())

def decode_UMLALT_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 1
  match VL with
  | 128 => (execute_UMLALT_Z_ZZZi_D 128 da esize index m n sel)
  | 256 => (execute_UMLALT_Z_ZZZi_D 256 da esize index m n sel)
  | 512 => (execute_UMLALT_Z_ZZZi_D 512 da esize index m n sel)
  | 1024 => (execute_UMLALT_Z_ZZZi_D 1024 da esize index m n sel)
  | 2048 => (execute_UMLALT_Z_ZZZi_D 2048 da esize index m n sel)
  | _ => (pure ())

def decode_SMLSLB_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 0
  match VL with
  | 128 => (execute_SMLSLB_Z_ZZZi_S 128 da esize index m n sel)
  | 256 => (execute_SMLSLB_Z_ZZZi_S 256 da esize index m n sel)
  | 512 => (execute_SMLSLB_Z_ZZZi_S 512 da esize index m n sel)
  | 1024 => (execute_SMLSLB_Z_ZZZi_S 1024 da esize index m n sel)
  | 2048 => (execute_SMLSLB_Z_ZZZi_S 2048 da esize index m n sel)
  | _ => (pure ())

def decode_SMLSLB_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 0
  match VL with
  | 128 => (execute_SMLSLB_Z_ZZZi_D 128 da esize index m n sel)
  | 256 => (execute_SMLSLB_Z_ZZZi_D 256 da esize index m n sel)
  | 512 => (execute_SMLSLB_Z_ZZZi_D 512 da esize index m n sel)
  | 1024 => (execute_SMLSLB_Z_ZZZi_D 1024 da esize index m n sel)
  | 2048 => (execute_SMLSLB_Z_ZZZi_D 2048 da esize index m n sel)
  | _ => (pure ())

def decode_SMLSLT_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 1
  match VL with
  | 128 => (execute_SMLSLT_Z_ZZZi_S 128 da esize index m n sel)
  | 256 => (execute_SMLSLT_Z_ZZZi_S 256 da esize index m n sel)
  | 512 => (execute_SMLSLT_Z_ZZZi_S 512 da esize index m n sel)
  | 1024 => (execute_SMLSLT_Z_ZZZi_S 1024 da esize index m n sel)
  | 2048 => (execute_SMLSLT_Z_ZZZi_S 2048 da esize index m n sel)
  | _ => (pure ())

def decode_SMLSLT_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 1
  match VL with
  | 128 => (execute_SMLSLT_Z_ZZZi_D 128 da esize index m n sel)
  | 256 => (execute_SMLSLT_Z_ZZZi_D 256 da esize index m n sel)
  | 512 => (execute_SMLSLT_Z_ZZZi_D 512 da esize index m n sel)
  | 1024 => (execute_SMLSLT_Z_ZZZi_D 1024 da esize index m n sel)
  | 2048 => (execute_SMLSLT_Z_ZZZi_D 2048 da esize index m n sel)
  | _ => (pure ())

def decode_UMLSLB_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 0
  match VL with
  | 128 => (execute_UMLSLB_Z_ZZZi_S 128 da esize index m n sel)
  | 256 => (execute_UMLSLB_Z_ZZZi_S 256 da esize index m n sel)
  | 512 => (execute_UMLSLB_Z_ZZZi_S 512 da esize index m n sel)
  | 1024 => (execute_UMLSLB_Z_ZZZi_S 1024 da esize index m n sel)
  | 2048 => (execute_UMLSLB_Z_ZZZi_S 2048 da esize index m n sel)
  | _ => (pure ())

def decode_UMLSLB_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 0
  match VL with
  | 128 => (execute_UMLSLB_Z_ZZZi_D 128 da esize index m n sel)
  | 256 => (execute_UMLSLB_Z_ZZZi_D 256 da esize index m n sel)
  | 512 => (execute_UMLSLB_Z_ZZZi_D 512 da esize index m n sel)
  | 1024 => (execute_UMLSLB_Z_ZZZi_D 1024 da esize index m n sel)
  | 2048 => (execute_UMLSLB_Z_ZZZi_D 2048 da esize index m n sel)
  | _ => (pure ())

def decode_UMLSLT_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (U : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 1
  match VL with
  | 128 => (execute_UMLSLT_Z_ZZZi_S 128 da esize index m n sel)
  | 256 => (execute_UMLSLT_Z_ZZZi_S 256 da esize index m n sel)
  | 512 => (execute_UMLSLT_Z_ZZZi_S 512 da esize index m n sel)
  | 1024 => (execute_UMLSLT_Z_ZZZi_S 1024 da esize index m n sel)
  | 2048 => (execute_UMLSLT_Z_ZZZi_S 2048 da esize index m n sel)
  | _ => (pure ())

def decode_UMLSLT_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (U : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 1
  match VL with
  | 128 => (execute_UMLSLT_Z_ZZZi_D 128 da esize index m n sel)
  | 256 => (execute_UMLSLT_Z_ZZZi_D 256 da esize index m n sel)
  | 512 => (execute_UMLSLT_Z_ZZZi_D 512 da esize index m n sel)
  | 1024 => (execute_UMLSLT_Z_ZZZi_D 1024 da esize index m n sel)
  | 2048 => (execute_UMLSLT_Z_ZZZi_D 2048 da esize index m n sel)
  | _ => (pure ())

def decode_SQDMULLB_Z_ZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let sel := 0
  match VL with
  | 128 => (execute_SQDMULLB_Z_ZZi_S 128 d esize index m n sel)
  | 256 => (execute_SQDMULLB_Z_ZZi_S 256 d esize index m n sel)
  | 512 => (execute_SQDMULLB_Z_ZZi_S 512 d esize index m n sel)
  | 1024 => (execute_SQDMULLB_Z_ZZi_S 1024 d esize index m n sel)
  | 2048 => (execute_SQDMULLB_Z_ZZi_S 2048 d esize index m n sel)
  | _ => (pure ())

def decode_SQDMULLB_Z_ZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let sel := 0
  match VL with
  | 128 => (execute_SQDMULLB_Z_ZZi_D 128 d esize index m n sel)
  | 256 => (execute_SQDMULLB_Z_ZZi_D 256 d esize index m n sel)
  | 512 => (execute_SQDMULLB_Z_ZZi_D 512 d esize index m n sel)
  | 1024 => (execute_SQDMULLB_Z_ZZi_D 1024 d esize index m n sel)
  | 2048 => (execute_SQDMULLB_Z_ZZi_D 2048 d esize index m n sel)
  | _ => (pure ())

def decode_SQDMULLT_Z_ZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let sel := 1
  match VL with
  | 128 => (execute_SQDMULLT_Z_ZZi_S 128 d esize index m n sel)
  | 256 => (execute_SQDMULLT_Z_ZZi_S 256 d esize index m n sel)
  | 512 => (execute_SQDMULLT_Z_ZZi_S 512 d esize index m n sel)
  | 1024 => (execute_SQDMULLT_Z_ZZi_S 1024 d esize index m n sel)
  | 2048 => (execute_SQDMULLT_Z_ZZi_S 2048 d esize index m n sel)
  | _ => (pure ())

def decode_SQDMULLT_Z_ZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let sel := 1
  match VL with
  | 128 => (execute_SQDMULLT_Z_ZZi_D 128 d esize index m n sel)
  | 256 => (execute_SQDMULLT_Z_ZZi_D 256 d esize index m n sel)
  | 512 => (execute_SQDMULLT_Z_ZZi_D 512 d esize index m n sel)
  | 1024 => (execute_SQDMULLT_Z_ZZi_D 1024 d esize index m n sel)
  | 2048 => (execute_SQDMULLT_Z_ZZi_D 2048 d esize index m n sel)
  | _ => (pure ())

def decode_SQDMLALB_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 0
  match VL with
  | 128 => (execute_SQDMLALB_Z_ZZZi_S 128 da esize index m n sel)
  | 256 => (execute_SQDMLALB_Z_ZZZi_S 256 da esize index m n sel)
  | 512 => (execute_SQDMLALB_Z_ZZZi_S 512 da esize index m n sel)
  | 1024 => (execute_SQDMLALB_Z_ZZZi_S 1024 da esize index m n sel)
  | 2048 => (execute_SQDMLALB_Z_ZZZi_S 2048 da esize index m n sel)
  | _ => (pure ())

def decode_SQDMLALB_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 0
  match VL with
  | 128 => (execute_SQDMLALB_Z_ZZZi_D 128 da esize index m n sel)
  | 256 => (execute_SQDMLALB_Z_ZZZi_D 256 da esize index m n sel)
  | 512 => (execute_SQDMLALB_Z_ZZZi_D 512 da esize index m n sel)
  | 1024 => (execute_SQDMLALB_Z_ZZZi_D 1024 da esize index m n sel)
  | 2048 => (execute_SQDMLALB_Z_ZZZi_D 2048 da esize index m n sel)
  | _ => (pure ())

def decode_SQDMLALT_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 1
  match VL with
  | 128 => (execute_SQDMLALT_Z_ZZZi_S 128 da esize index m n sel)
  | 256 => (execute_SQDMLALT_Z_ZZZi_S 256 da esize index m n sel)
  | 512 => (execute_SQDMLALT_Z_ZZZi_S 512 da esize index m n sel)
  | 1024 => (execute_SQDMLALT_Z_ZZZi_S 1024 da esize index m n sel)
  | 2048 => (execute_SQDMLALT_Z_ZZZi_S 2048 da esize index m n sel)
  | _ => (pure ())

def decode_SQDMLALT_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 1
  match VL with
  | 128 => (execute_SQDMLALT_Z_ZZZi_D 128 da esize index m n sel)
  | 256 => (execute_SQDMLALT_Z_ZZZi_D 256 da esize index m n sel)
  | 512 => (execute_SQDMLALT_Z_ZZZi_D 512 da esize index m n sel)
  | 1024 => (execute_SQDMLALT_Z_ZZZi_D 1024 da esize index m n sel)
  | 2048 => (execute_SQDMLALT_Z_ZZZi_D 2048 da esize index m n sel)
  | _ => (pure ())

def decode_SQDMLSLB_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 0
  match VL with
  | 128 => (execute_SQDMLSLB_Z_ZZZi_S 128 da esize index m n sel)
  | 256 => (execute_SQDMLSLB_Z_ZZZi_S 256 da esize index m n sel)
  | 512 => (execute_SQDMLSLB_Z_ZZZi_S 512 da esize index m n sel)
  | 1024 => (execute_SQDMLSLB_Z_ZZZi_S 1024 da esize index m n sel)
  | 2048 => (execute_SQDMLSLB_Z_ZZZi_S 2048 da esize index m n sel)
  | _ => (pure ())

def decode_SQDMLSLB_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 0
  match VL with
  | 128 => (execute_SQDMLSLB_Z_ZZZi_D 128 da esize index m n sel)
  | 256 => (execute_SQDMLSLB_Z_ZZZi_D 256 da esize index m n sel)
  | 512 => (execute_SQDMLSLB_Z_ZZZi_D 512 da esize index m n sel)
  | 1024 => (execute_SQDMLSLB_Z_ZZZi_D 1024 da esize index m n sel)
  | 2048 => (execute_SQDMLSLB_Z_ZZZi_D 2048 da esize index m n sel)
  | _ => (pure ())

def decode_SQDMLSLT_Z_ZZZi_S (size : (BitVec 2)) (i3h : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (i3l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 1
  match VL with
  | 128 => (execute_SQDMLSLT_Z_ZZZi_S 128 da esize index m n sel)
  | 256 => (execute_SQDMLSLT_Z_ZZZi_S 256 da esize index m n sel)
  | 512 => (execute_SQDMLSLT_Z_ZZZi_S 512 da esize index m n sel)
  | 1024 => (execute_SQDMLSLT_Z_ZZZi_S 1024 da esize index m n sel)
  | 2048 => (execute_SQDMLSLT_Z_ZZZi_S 2048 da esize index m n sel)
  | _ => (pure ())

def decode_SQDMLSLT_Z_ZZZi_D (size : (BitVec 2)) (i2h : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (i2l : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat (i2h +++ i2l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel := 1
  match VL with
  | 128 => (execute_SQDMLSLT_Z_ZZZi_D 128 da esize index m n sel)
  | 256 => (execute_SQDMLSLT_Z_ZZZi_D 256 da esize index m n sel)
  | 512 => (execute_SQDMLSLT_Z_ZZZi_D 512 da esize index m n sel)
  | 1024 => (execute_SQDMLSLT_Z_ZZZi_D 1024 da esize index m n sel)
  | 2048 => (execute_SQDMLSLT_Z_ZZZi_D 2048 da esize index m n sel)
  | _ => (pure ())

def decode_SQDMLALBT_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  let sel1 := 0
  let sel2 := 1
  match VL with
  | 128 => (execute_SQDMLALBT_Z_ZZZ__ 128 da esize m n sel1 sel2)
  | 256 => (execute_SQDMLALBT_Z_ZZZ__ 256 da esize m n sel1 sel2)
  | 512 => (execute_SQDMLALBT_Z_ZZZ__ 512 da esize m n sel1 sel2)
  | 1024 => (execute_SQDMLALBT_Z_ZZZ__ 1024 da esize m n sel1 sel2)
  | 2048 => (execute_SQDMLALBT_Z_ZZZ__ 2048 da esize m n sel1 sel2)
  | _ => (pure ())

def decode_SQDMLSLBT_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  let sel1 := 0
  let sel2 := 1
  match VL with
  | 128 => (execute_SQDMLSLBT_Z_ZZZ__ 128 da esize m n sel1 sel2)
  | 256 => (execute_SQDMLSLBT_Z_ZZZ__ 256 da esize m n sel1 sel2)
  | 512 => (execute_SQDMLSLBT_Z_ZZZ__ 512 da esize m n sel1 sel2)
  | 1024 => (execute_SQDMLSLBT_Z_ZZZ__ 1024 da esize m n sel1 sel2)
  | 2048 => (execute_SQDMLSLBT_Z_ZZZ__ 2048 da esize m n sel1 sel2)
  | _ => (pure ())

def decode_SQRDMULH_Z_ZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (R : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQRDMULH_Z_ZZi_H 128 d esize index m n)
  | 256 => (execute_SQRDMULH_Z_ZZi_H 256 d esize index m n)
  | 512 => (execute_SQRDMULH_Z_ZZi_H 512 d esize index m n)
  | 1024 => (execute_SQRDMULH_Z_ZZi_H 1024 d esize index m n)
  | 2048 => (execute_SQRDMULH_Z_ZZi_H 2048 d esize index m n)
  | _ => (pure ())

def decode_SQRDMULH_Z_ZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (R : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQRDMULH_Z_ZZi_S 128 d esize index m n)
  | 256 => (execute_SQRDMULH_Z_ZZi_S 256 d esize index m n)
  | 512 => (execute_SQRDMULH_Z_ZZi_S 512 d esize index m n)
  | 1024 => (execute_SQRDMULH_Z_ZZi_S 1024 d esize index m n)
  | 2048 => (execute_SQRDMULH_Z_ZZi_S 2048 d esize index m n)
  | _ => (pure ())

def decode_SQRDMULH_Z_ZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (R : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let index := (BitVec.toNat i1)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQRDMULH_Z_ZZi_D 128 d esize index m n)
  | 256 => (execute_SQRDMULH_Z_ZZi_D 256 d esize index m n)
  | 512 => (execute_SQRDMULH_Z_ZZi_D 512 d esize index m n)
  | 1024 => (execute_SQRDMULH_Z_ZZi_D 1024 d esize index m n)
  | 2048 => (execute_SQRDMULH_Z_ZZi_D 2048 d esize index m n)
  | _ => (pure ())

def decode_SQRDMLAH_Z_ZZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SQRDMLAH_Z_ZZZi_H 128 da esize index m n)
  | 256 => (execute_SQRDMLAH_Z_ZZZi_H 256 da esize index m n)
  | 512 => (execute_SQRDMLAH_Z_ZZZi_H 512 da esize index m n)
  | 1024 => (execute_SQRDMLAH_Z_ZZZi_H 1024 da esize index m n)
  | 2048 => (execute_SQRDMLAH_Z_ZZZi_H 2048 da esize index m n)
  | _ => (pure ())

def decode_SQRDMLAH_Z_ZZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SQRDMLAH_Z_ZZZi_S 128 da esize index m n)
  | 256 => (execute_SQRDMLAH_Z_ZZZi_S 256 da esize index m n)
  | 512 => (execute_SQRDMLAH_Z_ZZZi_S 512 da esize index m n)
  | 1024 => (execute_SQRDMLAH_Z_ZZZi_S 1024 da esize index m n)
  | 2048 => (execute_SQRDMLAH_Z_ZZZi_S 2048 da esize index m n)
  | _ => (pure ())

def decode_SQRDMLAH_Z_ZZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let index := (BitVec.toNat i1)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SQRDMLAH_Z_ZZZi_D 128 da esize index m n)
  | 256 => (execute_SQRDMLAH_Z_ZZZi_D 256 da esize index m n)
  | 512 => (execute_SQRDMLAH_Z_ZZZi_D 512 da esize index m n)
  | 1024 => (execute_SQRDMLAH_Z_ZZZi_D 1024 da esize index m n)
  | 2048 => (execute_SQRDMLAH_Z_ZZZi_D 2048 da esize index m n)
  | _ => (pure ())

def decode_SQRDMLSH_Z_ZZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SQRDMLSH_Z_ZZZi_H 128 da esize index m n)
  | 256 => (execute_SQRDMLSH_Z_ZZZi_H 256 da esize index m n)
  | 512 => (execute_SQRDMLSH_Z_ZZZi_H 512 da esize index m n)
  | 1024 => (execute_SQRDMLSH_Z_ZZZi_H 1024 da esize index m n)
  | 2048 => (execute_SQRDMLSH_Z_ZZZi_H 2048 da esize index m n)
  | _ => (pure ())

def decode_SQRDMLSH_Z_ZZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SQRDMLSH_Z_ZZZi_S 128 da esize index m n)
  | 256 => (execute_SQRDMLSH_Z_ZZZi_S 256 da esize index m n)
  | 512 => (execute_SQRDMLSH_Z_ZZZi_S 512 da esize index m n)
  | 1024 => (execute_SQRDMLSH_Z_ZZZi_S 1024 da esize index m n)
  | 2048 => (execute_SQRDMLSH_Z_ZZZi_S 2048 da esize index m n)
  | _ => (pure ())

def decode_SQRDMLSH_Z_ZZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (S : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let index := (BitVec.toNat i1)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SQRDMLSH_Z_ZZZi_D 128 da esize index m n)
  | 256 => (execute_SQRDMLSH_Z_ZZZi_D 256 da esize index m n)
  | 512 => (execute_SQRDMLSH_Z_ZZZi_D 512 da esize index m n)
  | 1024 => (execute_SQRDMLSH_Z_ZZZi_D 1024 da esize index m n)
  | 2048 => (execute_SQRDMLSH_Z_ZZZi_D 2048 da esize index m n)
  | _ => (pure ())

def decode_SHADD_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_SHADD_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_SHADD_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_SHADD_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_SHADD_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_SHADD_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_SHSUB_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_SHSUB_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_SHSUB_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_SHSUB_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_SHSUB_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_SHSUB_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_SHSUBR_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_SHSUBR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_SHSUBR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_SHSUBR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_SHSUBR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_SHSUBR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_SRHADD_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_SRHADD_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_SRHADD_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_SRHADD_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_SRHADD_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_SRHADD_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_UHADD_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_UHADD_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_UHADD_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_UHADD_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_UHADD_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_UHADD_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_UHSUB_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_UHSUB_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_UHSUB_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_UHSUB_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_UHSUB_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_UHSUB_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_UHSUBR_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_UHSUBR_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_UHSUBR_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_UHSUBR_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_UHSUBR_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_UHSUBR_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_URHADD_Z_P_ZZ__ (size : (BitVec 2)) (R : (BitVec 1)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_URHADD_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_URHADD_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_URHADD_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_URHADD_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_URHADD_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_SQADD_Z_P_ZZ__ (size : (BitVec 2)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SQADD_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_SQADD_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_SQADD_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_SQADD_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_SQADD_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_UQADD_Z_P_ZZ__ (size : (BitVec 2)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UQADD_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_UQADD_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_UQADD_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_UQADD_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_UQADD_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_SQSUB_Z_P_ZZ__ (size : (BitVec 2)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SQSUB_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_SQSUB_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_SQSUB_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_SQSUB_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_SQSUB_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_UQSUB_Z_P_ZZ__ (size : (BitVec 2)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UQSUB_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_UQSUB_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_UQSUB_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_UQSUB_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_UQSUB_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_SQSUBR_Z_P_ZZ__ (size : (BitVec 2)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SQSUBR_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_SQSUBR_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_SQSUBR_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_SQSUBR_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_SQSUBR_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_UQSUBR_Z_P_ZZ__ (size : (BitVec 2)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UQSUBR_Z_P_ZZ__ 128 dn esize g m is_unsigned)
  | 256 => (execute_UQSUBR_Z_P_ZZ__ 256 dn esize g m is_unsigned)
  | 512 => (execute_UQSUBR_Z_P_ZZ__ 512 dn esize g m is_unsigned)
  | 1024 => (execute_UQSUBR_Z_P_ZZ__ 1024 dn esize g m is_unsigned)
  | 2048 => (execute_UQSUBR_Z_P_ZZ__ 2048 dn esize g m is_unsigned)
  | _ => (pure ())

def decode_SUQADD_Z_P_ZZ__ (size : (BitVec 2)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_SUQADD_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_SUQADD_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_SUQADD_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_SUQADD_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_SUQADD_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_USQADD_Z_P_ZZ__ (size : (BitVec 2)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_USQADD_Z_P_ZZ__ 128 dn esize g m)
  | 256 => (execute_USQADD_Z_P_ZZ__ 256 dn esize g m)
  | 512 => (execute_USQADD_Z_P_ZZ__ 512 dn esize g m)
  | 1024 => (execute_USQADD_Z_P_ZZ__ 1024 dn esize g m)
  | 2048 => (execute_USQADD_Z_P_ZZ__ 2048 dn esize g m)
  | _ => (pure ())

def decode_SLI_Z_ZZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((BitVec.toNat (tsize +++ imm3)) -i esize)
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_SLI_Z_ZZI__ 128 d 8 n shift)
      | 256 => (execute_SLI_Z_ZZI__ 256 d 8 n shift)
      | 512 => (execute_SLI_Z_ZZI__ 512 d 8 n shift)
      | 1024 => (execute_SLI_Z_ZZI__ 1024 d 8 n shift)
      | 2048 => (execute_SLI_Z_ZZI__ 2048 d 8 n shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_SLI_Z_ZZI__ 128 d 16 n shift)
      | 256 => (execute_SLI_Z_ZZI__ 256 d 16 n shift)
      | 512 => (execute_SLI_Z_ZZI__ 512 d 16 n shift)
      | 1024 => (execute_SLI_Z_ZZI__ 1024 d 16 n shift)
      | 2048 => (execute_SLI_Z_ZZI__ 2048 d 16 n shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_SLI_Z_ZZI__ 128 d 32 n shift)
      | 256 => (execute_SLI_Z_ZZI__ 256 d 32 n shift)
      | 512 => (execute_SLI_Z_ZZI__ 512 d 32 n shift)
      | 1024 => (execute_SLI_Z_ZZI__ 1024 d 32 n shift)
      | 2048 => (execute_SLI_Z_ZZI__ 2048 d 32 n shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_SLI_Z_ZZI__ 128 d 64 n shift)
      | 256 => (execute_SLI_Z_ZZI__ 256 d 64 n shift)
      | 512 => (execute_SLI_Z_ZZI__ 512 d 64 n shift)
      | 1024 => (execute_SLI_Z_ZZI__ 1024 d 64 n shift)
      | 2048 => (execute_SLI_Z_ZZI__ 2048 d 64 n shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:49830.22-49830.23"

def decode_SRI_Z_ZZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_SRI_Z_ZZI__ 128 d 8 n shift)
      | 256 => (execute_SRI_Z_ZZI__ 256 d 8 n shift)
      | 512 => (execute_SRI_Z_ZZI__ 512 d 8 n shift)
      | 1024 => (execute_SRI_Z_ZZI__ 1024 d 8 n shift)
      | 2048 => (execute_SRI_Z_ZZI__ 2048 d 8 n shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_SRI_Z_ZZI__ 128 d 16 n shift)
      | 256 => (execute_SRI_Z_ZZI__ 256 d 16 n shift)
      | 512 => (execute_SRI_Z_ZZI__ 512 d 16 n shift)
      | 1024 => (execute_SRI_Z_ZZI__ 1024 d 16 n shift)
      | 2048 => (execute_SRI_Z_ZZI__ 2048 d 16 n shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_SRI_Z_ZZI__ 128 d 32 n shift)
      | 256 => (execute_SRI_Z_ZZI__ 256 d 32 n shift)
      | 512 => (execute_SRI_Z_ZZI__ 512 d 32 n shift)
      | 1024 => (execute_SRI_Z_ZZI__ 1024 d 32 n shift)
      | 2048 => (execute_SRI_Z_ZZI__ 2048 d 32 n shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_SRI_Z_ZZI__ 128 d 64 n shift)
      | 256 => (execute_SRI_Z_ZZI__ 256 d 64 n shift)
      | 512 => (execute_SRI_Z_ZZI__ 512 d 64 n shift)
      | 1024 => (execute_SRI_Z_ZZI__ 1024 d 64 n shift)
      | 2048 => (execute_SRI_Z_ZZI__ 2048 d 64 n shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:49978.22-49978.23"

def decode_TBX_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_TBX_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_TBX_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_TBX_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_TBX_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_TBX_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_URECPE_Z_P_Z__ (size : (BitVec 2)) (Q : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size != 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_URECPE_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_URECPE_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_URECPE_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_URECPE_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_URECPE_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_URSQRTE_Z_P_Z__ (size : (BitVec 2)) (Q : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size != 0b10#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_URSQRTE_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_URSQRTE_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_URSQRTE_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_URSQRTE_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_URSQRTE_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_MATCH_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((let b__0 := size
     if (((Sail.BitVec.extractLsb b__0 1 1) == (1#1 : (BitVec 1))) : Bool)
     then true
     else false : Bool) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let d := (BitVec.toNat Pd)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_MATCH_P_P_ZZ__ 128 d esize g m n)
  | 256 => (execute_MATCH_P_P_ZZ__ 256 d esize g m n)
  | 512 => (execute_MATCH_P_P_ZZ__ 512 d esize g m n)
  | 1024 => (execute_MATCH_P_P_ZZ__ 1024 d esize g m n)
  | 2048 => (execute_MATCH_P_P_ZZ__ 2048 d esize g m n)
  | _ => (pure ())

def decode_NMATCH_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((let b__0 := size
     if (((Sail.BitVec.extractLsb b__0 1 1) == (1#1 : (BitVec 1))) : Bool)
     then true
     else false : Bool) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let d := (BitVec.toNat Pd)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_NMATCH_P_P_ZZ__ 128 d esize g m n)
  | 256 => (execute_NMATCH_P_P_ZZ__ 256 d esize g m n)
  | 512 => (execute_NMATCH_P_P_ZZ__ 512 d esize g m n)
  | 1024 => (execute_NMATCH_P_P_ZZ__ 1024 d esize g m n)
  | 2048 => (execute_NMATCH_P_P_ZZ__ 2048 d esize g m n)
  | _ => (pure ())

def decode_HISTCNT_Z_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
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
  let d := (BitVec.toNat Zd)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_HISTCNT_Z_P_ZZ__ 128 d esize g m n)
  | 256 => (execute_HISTCNT_Z_P_ZZ__ 256 d esize g m n)
  | 512 => (execute_HISTCNT_Z_P_ZZ__ 512 d esize g m n)
  | 1024 => (execute_HISTCNT_Z_P_ZZ__ 1024 d esize g m n)
  | 2048 => (execute_HISTCNT_Z_P_ZZ__ 2048 d esize g m n)
  | _ => (pure ())

def decode_HISTSEG_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size != 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let d := (BitVec.toNat Zd)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  match VL with
  | 128 => (execute_HISTSEG_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_HISTSEG_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_HISTSEG_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_HISTSEG_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_HISTSEG_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_WHILEWR_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (Rn : (BitVec 5)) (rw : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Pd)
  match VL with
  | 128 => (execute_WHILEWR_P_RR__ 128 d esize m n)
  | 256 => (execute_WHILEWR_P_RR__ 256 d esize m n)
  | 512 => (execute_WHILEWR_P_RR__ 512 d esize m n)
  | 1024 => (execute_WHILEWR_P_RR__ 1024 d esize m n)
  | 2048 => (execute_WHILEWR_P_RR__ 2048 d esize m n)
  | _ => (pure ())

def decode_WHILERW_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (Rn : (BitVec 5)) (rw : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat Pd)
  match VL with
  | 128 => (execute_WHILERW_P_RR__ 128 d esize m n)
  | 256 => (execute_WHILERW_P_RR__ 256 d esize m n)
  | 512 => (execute_WHILERW_P_RR__ 512 d esize m n)
  | 1024 => (execute_WHILERW_P_RR__ 1024 d esize m n)
  | 2048 => (execute_WHILERW_P_RR__ 2048 d esize m n)
  | _ => (pure ())

def decode_BDEP_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVE2BitPerm ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_BDEP_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_BDEP_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_BDEP_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_BDEP_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_BDEP_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_BEXT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVE2BitPerm ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_BEXT_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_BEXT_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_BEXT_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_BEXT_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_BEXT_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_BGRP_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVE2BitPerm ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_BGRP_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_BGRP_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_BGRP_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_BGRP_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_BGRP_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_EORBT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (tb : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let sel1 := 0
  let sel2 := 1
  match VL with
  | 128 => (execute_EORBT_Z_ZZ__ 128 d esize m n sel1 sel2)
  | 256 => (execute_EORBT_Z_ZZ__ 256 d esize m n sel1 sel2)
  | 512 => (execute_EORBT_Z_ZZ__ 512 d esize m n sel1 sel2)
  | 1024 => (execute_EORBT_Z_ZZ__ 1024 d esize m n sel1 sel2)
  | 2048 => (execute_EORBT_Z_ZZ__ 2048 d esize m n sel1 sel2)
  | _ => (pure ())

def decode_EORTB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (tb : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let sel1 := 1
  let sel2 := 0
  match VL with
  | 128 => (execute_EORTB_Z_ZZ__ 128 d esize m n sel1 sel2)
  | 256 => (execute_EORTB_Z_ZZ__ 256 d esize m n sel1 sel2)
  | 512 => (execute_EORTB_Z_ZZ__ 512 d esize m n sel1 sel2)
  | 1024 => (execute_EORTB_Z_ZZ__ 1024 d esize m n sel1 sel2)
  | 2048 => (execute_EORTB_Z_ZZ__ 2048 d esize m n sel1 sel2)
  | _ => (pure ())

def decode_CDOT_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
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
  let sel_a := (BitVec.toNat (BitVec.join1 [(BitVec.access rot 0)]))
  let sel_b := (BitVec.toNat (Complement.complement (BitVec.join1 [(BitVec.access rot 0)])))
  let sub_i : Bool := ((BitVec.join1 [(BitVec.access rot 0)]) == (BitVec.join1 [(BitVec.access rot 1)]))
  match VL with
  | 128 => (execute_CDOT_Z_ZZZ__ 128 da esize m n sel_a sel_b sub_i)
  | 256 => (execute_CDOT_Z_ZZZ__ 256 da esize m n sel_a sel_b sub_i)
  | 512 => (execute_CDOT_Z_ZZZ__ 512 da esize m n sel_a sel_b sub_i)
  | 1024 => (execute_CDOT_Z_ZZZ__ 1024 da esize m n sel_a sel_b sub_i)
  | 2048 => (execute_CDOT_Z_ZZZ__ 2048 da esize m n sel_a sel_b sub_i)
  | _ => (pure ())

def decode_CDOT_Z_ZZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel_a := (BitVec.toNat (BitVec.join1 [(BitVec.access rot 0)]))
  let sel_b := (BitVec.toNat (Complement.complement (BitVec.join1 [(BitVec.access rot 0)])))
  let sub_i : Bool := ((BitVec.join1 [(BitVec.access rot 0)]) == (BitVec.join1 [(BitVec.access rot 1)]))
  match VL with
  | 128 => (execute_CDOT_Z_ZZZi_S 128 da esize index m n sel_a sel_b sub_i)
  | 256 => (execute_CDOT_Z_ZZZi_S 256 da esize index m n sel_a sel_b sub_i)
  | 512 => (execute_CDOT_Z_ZZZi_S 512 da esize index m n sel_a sel_b sub_i)
  | 1024 => (execute_CDOT_Z_ZZZi_S 1024 da esize index m n sel_a sel_b sub_i)
  | 2048 => (execute_CDOT_Z_ZZZi_S 2048 da esize index m n sel_a sel_b sub_i)
  | _ => (pure ())

def decode_CDOT_Z_ZZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let index := (BitVec.toNat i1)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let sel_a := (BitVec.toNat (BitVec.join1 [(BitVec.access rot 0)]))
  let sel_b := (BitVec.toNat (Complement.complement (BitVec.join1 [(BitVec.access rot 0)])))
  let sub_i : Bool := ((BitVec.join1 [(BitVec.access rot 0)]) == (BitVec.join1 [(BitVec.access rot 1)]))
  match VL with
  | 128 => (execute_CDOT_Z_ZZZi_D 128 da esize index m n sel_a sel_b sub_i)
  | 256 => (execute_CDOT_Z_ZZZi_D 256 da esize index m n sel_a sel_b sub_i)
  | 512 => (execute_CDOT_Z_ZZZi_D 512 da esize index m n sel_a sel_b sub_i)
  | 1024 => (execute_CDOT_Z_ZZZi_D 1024 da esize index m n sel_a sel_b sub_i)
  | 2048 => (execute_CDOT_Z_ZZZi_D 2048 da esize index m n sel_a sel_b sub_i)
  | _ => (pure ())

def decode_SMMLA_Z_ZZZ__ (uns : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveInt8MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_unsigned : Bool := false
  let op2_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMMLA_Z_ZZZ__ 128 da m n op1_unsigned op2_unsigned)
  | 256 => (execute_SMMLA_Z_ZZZ__ 256 da m n op1_unsigned op2_unsigned)
  | 512 => (execute_SMMLA_Z_ZZZ__ 512 da m n op1_unsigned op2_unsigned)
  | 1024 => (execute_SMMLA_Z_ZZZ__ 1024 da m n op1_unsigned op2_unsigned)
  | 2048 => (execute_SMMLA_Z_ZZZ__ 2048 da m n op1_unsigned op2_unsigned)
  | _ => (pure ())

def decode_UMMLA_Z_ZZZ__ (uns : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveInt8MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_unsigned : Bool := true
  let op2_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMMLA_Z_ZZZ__ 128 da m n op1_unsigned op2_unsigned)
  | 256 => (execute_UMMLA_Z_ZZZ__ 256 da m n op1_unsigned op2_unsigned)
  | 512 => (execute_UMMLA_Z_ZZZ__ 512 da m n op1_unsigned op2_unsigned)
  | 1024 => (execute_UMMLA_Z_ZZZ__ 1024 da m n op1_unsigned op2_unsigned)
  | 2048 => (execute_UMMLA_Z_ZZZ__ 2048 da m n op1_unsigned op2_unsigned)
  | _ => (pure ())

def decode_USMMLA_Z_ZZZ__ (uns : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveInt8MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  let op1_unsigned : Bool := true
  let op2_unsigned : Bool := false
  match VL with
  | 128 => (execute_USMMLA_Z_ZZZ__ 128 da m n op1_unsigned op2_unsigned)
  | 256 => (execute_USMMLA_Z_ZZZ__ 256 da m n op1_unsigned op2_unsigned)
  | 512 => (execute_USMMLA_Z_ZZZ__ 512 da m n op1_unsigned op2_unsigned)
  | 1024 => (execute_USMMLA_Z_ZZZ__ 1024 da m n op1_unsigned op2_unsigned)
  | 2048 => (execute_USMMLA_Z_ZZZ__ 2048 da m n op1_unsigned op2_unsigned)
  | _ => (pure ())

def decode_SQDMULH_Z_ZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (R : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let index := (BitVec.toNat (i3h +++ i3l))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQDMULH_Z_ZZi_H 128 d esize index m n)
  | 256 => (execute_SQDMULH_Z_ZZi_H 256 d esize index m n)
  | 512 => (execute_SQDMULH_Z_ZZi_H 512 d esize index m n)
  | 1024 => (execute_SQDMULH_Z_ZZi_H 1024 d esize index m n)
  | 2048 => (execute_SQDMULH_Z_ZZi_H 2048 d esize index m n)
  | _ => (pure ())

def decode_SQDMULH_Z_ZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (R : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let index := (BitVec.toNat i2)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQDMULH_Z_ZZi_S 128 d esize index m n)
  | 256 => (execute_SQDMULH_Z_ZZi_S 256 d esize index m n)
  | 512 => (execute_SQDMULH_Z_ZZi_S 512 d esize index m n)
  | 1024 => (execute_SQDMULH_Z_ZZi_S 1024 d esize index m n)
  | 2048 => (execute_SQDMULH_Z_ZZi_S 2048 d esize index m n)
  | _ => (pure ())

def decode_SQDMULH_Z_ZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (R : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let index := (BitVec.toNat i1)
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQDMULH_Z_ZZi_D 128 d esize index m n)
  | 256 => (execute_SQDMULH_Z_ZZi_D 256 d esize index m n)
  | 512 => (execute_SQDMULH_Z_ZZi_D 512 d esize index m n)
  | 1024 => (execute_SQDMULH_Z_ZZi_D 1024 d esize index m n)
  | 2048 => (execute_SQDMULH_Z_ZZi_D 2048 d esize index m n)
  | _ => (pure ())

def decode_SRSRA_Z_ZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (R : (BitVec 1)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  let n := (BitVec.toNat Zn)
  let da := (BitVec.toNat Zda)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_SRSRA_Z_ZI__ 128 da 8 n shift)
      | 256 => (execute_SRSRA_Z_ZI__ 256 da 8 n shift)
      | 512 => (execute_SRSRA_Z_ZI__ 512 da 8 n shift)
      | 1024 => (execute_SRSRA_Z_ZI__ 1024 da 8 n shift)
      | 2048 => (execute_SRSRA_Z_ZI__ 2048 da 8 n shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_SRSRA_Z_ZI__ 128 da 16 n shift)
      | 256 => (execute_SRSRA_Z_ZI__ 256 da 16 n shift)
      | 512 => (execute_SRSRA_Z_ZI__ 512 da 16 n shift)
      | 1024 => (execute_SRSRA_Z_ZI__ 1024 da 16 n shift)
      | 2048 => (execute_SRSRA_Z_ZI__ 2048 da 16 n shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_SRSRA_Z_ZI__ 128 da 32 n shift)
      | 256 => (execute_SRSRA_Z_ZI__ 256 da 32 n shift)
      | 512 => (execute_SRSRA_Z_ZI__ 512 da 32 n shift)
      | 1024 => (execute_SRSRA_Z_ZI__ 1024 da 32 n shift)
      | 2048 => (execute_SRSRA_Z_ZI__ 2048 da 32 n shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_SRSRA_Z_ZI__ 128 da 64 n shift)
      | 256 => (execute_SRSRA_Z_ZI__ 256 da 64 n shift)
      | 512 => (execute_SRSRA_Z_ZI__ 512 da 64 n shift)
      | 1024 => (execute_SRSRA_Z_ZI__ 1024 da 64 n shift)
      | 2048 => (execute_SRSRA_Z_ZI__ 2048 da 64 n shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:51742.22-51742.23"

def decode_SSRA_Z_ZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (R : (BitVec 1)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  let n := (BitVec.toNat Zn)
  let da := (BitVec.toNat Zda)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_SSRA_Z_ZI__ 128 da 8 n shift)
      | 256 => (execute_SSRA_Z_ZI__ 256 da 8 n shift)
      | 512 => (execute_SSRA_Z_ZI__ 512 da 8 n shift)
      | 1024 => (execute_SSRA_Z_ZI__ 1024 da 8 n shift)
      | 2048 => (execute_SSRA_Z_ZI__ 2048 da 8 n shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_SSRA_Z_ZI__ 128 da 16 n shift)
      | 256 => (execute_SSRA_Z_ZI__ 256 da 16 n shift)
      | 512 => (execute_SSRA_Z_ZI__ 512 da 16 n shift)
      | 1024 => (execute_SSRA_Z_ZI__ 1024 da 16 n shift)
      | 2048 => (execute_SSRA_Z_ZI__ 2048 da 16 n shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_SSRA_Z_ZI__ 128 da 32 n shift)
      | 256 => (execute_SSRA_Z_ZI__ 256 da 32 n shift)
      | 512 => (execute_SSRA_Z_ZI__ 512 da 32 n shift)
      | 1024 => (execute_SSRA_Z_ZI__ 1024 da 32 n shift)
      | 2048 => (execute_SSRA_Z_ZI__ 2048 da 32 n shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_SSRA_Z_ZI__ 128 da 64 n shift)
      | 256 => (execute_SSRA_Z_ZI__ 256 da 64 n shift)
      | 512 => (execute_SSRA_Z_ZI__ 512 da 64 n shift)
      | 1024 => (execute_SSRA_Z_ZI__ 1024 da 64 n shift)
      | 2048 => (execute_SSRA_Z_ZI__ 2048 da 64 n shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:51889.22-51889.23"

def decode_URSRA_Z_ZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (R : (BitVec 1)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  let n := (BitVec.toNat Zn)
  let da := (BitVec.toNat Zda)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_URSRA_Z_ZI__ 128 da 8 n shift)
      | 256 => (execute_URSRA_Z_ZI__ 256 da 8 n shift)
      | 512 => (execute_URSRA_Z_ZI__ 512 da 8 n shift)
      | 1024 => (execute_URSRA_Z_ZI__ 1024 da 8 n shift)
      | 2048 => (execute_URSRA_Z_ZI__ 2048 da 8 n shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_URSRA_Z_ZI__ 128 da 16 n shift)
      | 256 => (execute_URSRA_Z_ZI__ 256 da 16 n shift)
      | 512 => (execute_URSRA_Z_ZI__ 512 da 16 n shift)
      | 1024 => (execute_URSRA_Z_ZI__ 1024 da 16 n shift)
      | 2048 => (execute_URSRA_Z_ZI__ 2048 da 16 n shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_URSRA_Z_ZI__ 128 da 32 n shift)
      | 256 => (execute_URSRA_Z_ZI__ 256 da 32 n shift)
      | 512 => (execute_URSRA_Z_ZI__ 512 da 32 n shift)
      | 1024 => (execute_URSRA_Z_ZI__ 1024 da 32 n shift)
      | 2048 => (execute_URSRA_Z_ZI__ 2048 da 32 n shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_URSRA_Z_ZI__ 128 da 64 n shift)
      | 256 => (execute_URSRA_Z_ZI__ 256 da 64 n shift)
      | 512 => (execute_URSRA_Z_ZI__ 512 da 64 n shift)
      | 1024 => (execute_URSRA_Z_ZI__ 1024 da 64 n shift)
      | 2048 => (execute_URSRA_Z_ZI__ 2048 da 64 n shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:52036.22-52036.23"

def decode_USRA_Z_ZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (R : (BitVec 1)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  let n := (BitVec.toNat Zn)
  let da := (BitVec.toNat Zda)
  let shift := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_USRA_Z_ZI__ 128 da 8 n shift)
      | 256 => (execute_USRA_Z_ZI__ 256 da 8 n shift)
      | 512 => (execute_USRA_Z_ZI__ 512 da 8 n shift)
      | 1024 => (execute_USRA_Z_ZI__ 1024 da 8 n shift)
      | 2048 => (execute_USRA_Z_ZI__ 2048 da 8 n shift)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_USRA_Z_ZI__ 128 da 16 n shift)
      | 256 => (execute_USRA_Z_ZI__ 256 da 16 n shift)
      | 512 => (execute_USRA_Z_ZI__ 512 da 16 n shift)
      | 1024 => (execute_USRA_Z_ZI__ 1024 da 16 n shift)
      | 2048 => (execute_USRA_Z_ZI__ 2048 da 16 n shift)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_USRA_Z_ZI__ 128 da 32 n shift)
      | 256 => (execute_USRA_Z_ZI__ 256 da 32 n shift)
      | 512 => (execute_USRA_Z_ZI__ 512 da 32 n shift)
      | 1024 => (execute_USRA_Z_ZI__ 1024 da 32 n shift)
      | 2048 => (execute_USRA_Z_ZI__ 2048 da 32 n shift)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_USRA_Z_ZI__ 128 da 64 n shift)
      | 256 => (execute_USRA_Z_ZI__ 256 da 64 n shift)
      | 512 => (execute_USRA_Z_ZI__ 512 da 64 n shift)
      | 1024 => (execute_USRA_Z_ZI__ 1024 da 64 n shift)
      | 2048 => (execute_USRA_Z_ZI__ 2048 da 64 n shift)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:52183.22-52183.23"

def decode_AESD_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVE2AES ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let m := (BitVec.toNat Zm)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_AESD_Z_ZZ__ 128 dn m)
  | 256 => (execute_AESD_Z_ZZ__ 256 dn m)
  | 512 => (execute_AESD_Z_ZZ__ 512 dn m)
  | 1024 => (execute_AESD_Z_ZZ__ 1024 dn m)
  | 2048 => (execute_AESD_Z_ZZ__ 2048 dn m)
  | _ => (pure ())

def decode_AESE_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVE2AES ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let m := (BitVec.toNat Zm)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_AESE_Z_ZZ__ 128 dn m)
  | 256 => (execute_AESE_Z_ZZ__ 256 dn m)
  | 512 => (execute_AESE_Z_ZZ__ 512 dn m)
  | 1024 => (execute_AESE_Z_ZZ__ 1024 dn m)
  | 2048 => (execute_AESE_Z_ZZ__ 2048 dn m)
  | _ => (pure ())

def decode_AESIMC_Z_Z__ (size : (BitVec 2)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVE2AES ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_AESIMC_Z_Z__ 128 dn)
  | 256 => (execute_AESIMC_Z_Z__ 256 dn)
  | 512 => (execute_AESIMC_Z_Z__ 512 dn)
  | 1024 => (execute_AESIMC_Z_Z__ 1024 dn)
  | 2048 => (execute_AESIMC_Z_Z__ 2048 dn)
  | _ => (pure ())

def decode_AESMC_Z_Z__ (size : (BitVec 2)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVE2AES ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_AESMC_Z_Z__ 128 dn)
  | 256 => (execute_AESMC_Z_Z__ 256 dn)
  | 512 => (execute_AESMC_Z_Z__ 512 dn)
  | 1024 => (execute_AESMC_Z_Z__ 1024 dn)
  | 2048 => (execute_AESMC_Z_Z__ 2048 dn)
  | _ => (pure ())

def decode_RAX1_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2SHA3 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_RAX1_Z_ZZ__ 128 d m n)
  | 256 => (execute_RAX1_Z_ZZ__ 256 d m n)
  | 512 => (execute_RAX1_Z_ZZ__ 512 d m n)
  | 1024 => (execute_RAX1_Z_ZZ__ 1024 d m n)
  | 2048 => (execute_RAX1_Z_ZZ__ 2048 d m n)
  | _ => (pure ())

def decode_SM4E_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVE2SM4 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let m := (BitVec.toNat Zm)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_SM4E_Z_ZZ__ 128 dn m)
  | 256 => (execute_SM4E_Z_ZZ__ 256 dn m)
  | 512 => (execute_SM4E_Z_ZZ__ 512 dn m)
  | 1024 => (execute_SM4E_Z_ZZ__ 1024 dn m)
  | 2048 => (execute_SM4E_Z_ZZ__ 2048 dn m)
  | _ => (pure ())

def decode_SM4EKEY_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVE2SM4 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SM4EKEY_Z_ZZ__ 128 d m n)
  | 256 => (execute_SM4EKEY_Z_ZZ__ 256 d m n)
  | 512 => (execute_SM4EKEY_Z_ZZ__ 512 d m n)
  | 1024 => (execute_SM4EKEY_Z_ZZ__ 1024 d m n)
  | 2048 => (execute_SM4EKEY_Z_ZZ__ 2048 d m n)
  | _ => (pure ())

def decode_XAR_Z_ZZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let m := (BitVec.toNat Zm)
  let dn := (BitVec.toNat Zdn)
  let rot := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
  match esize with
  | 8 =>
    (do
      match VL with
      | 128 => (execute_XAR_Z_ZZI__ 128 dn 8 m rot)
      | 256 => (execute_XAR_Z_ZZI__ 256 dn 8 m rot)
      | 512 => (execute_XAR_Z_ZZI__ 512 dn 8 m rot)
      | 1024 => (execute_XAR_Z_ZZI__ 1024 dn 8 m rot)
      | 2048 => (execute_XAR_Z_ZZI__ 2048 dn 8 m rot)
      | _ => (pure ()))
  | 16 =>
    (do
      match VL with
      | 128 => (execute_XAR_Z_ZZI__ 128 dn 16 m rot)
      | 256 => (execute_XAR_Z_ZZI__ 256 dn 16 m rot)
      | 512 => (execute_XAR_Z_ZZI__ 512 dn 16 m rot)
      | 1024 => (execute_XAR_Z_ZZI__ 1024 dn 16 m rot)
      | 2048 => (execute_XAR_Z_ZZI__ 2048 dn 16 m rot)
      | _ => (pure ()))
  | 32 =>
    (do
      match VL with
      | 128 => (execute_XAR_Z_ZZI__ 128 dn 32 m rot)
      | 256 => (execute_XAR_Z_ZZI__ 256 dn 32 m rot)
      | 512 => (execute_XAR_Z_ZZI__ 512 dn 32 m rot)
      | 1024 => (execute_XAR_Z_ZZI__ 1024 dn 32 m rot)
      | 2048 => (execute_XAR_Z_ZZI__ 2048 dn 32 m rot)
      | _ => (pure ()))
  | 64 =>
    (do
      match VL with
      | 128 => (execute_XAR_Z_ZZI__ 128 dn 64 m rot)
      | 256 => (execute_XAR_Z_ZZI__ 256 dn 64 m rot)
      | 512 => (execute_XAR_Z_ZZI__ 512 dn 64 m rot)
      | 1024 => (execute_XAR_Z_ZZI__ 1024 dn 64 m rot)
      | 2048 => (execute_XAR_Z_ZZI__ 2048 dn 64 m rot)
      | _ => (pure ()))
  | _ => sail_assert false "src/instrs64_sve.sail:52750.22-52750.23"

def decode_BCAX_Z_ZZZ__ (Zm : (BitVec 5)) (Zk : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let m := (BitVec.toNat Zm)
  let k := (BitVec.toNat Zk)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_BCAX_Z_ZZZ__ 128 dn k m)
  | 256 => (execute_BCAX_Z_ZZZ__ 256 dn k m)
  | 512 => (execute_BCAX_Z_ZZZ__ 512 dn k m)
  | 1024 => (execute_BCAX_Z_ZZZ__ 1024 dn k m)
  | 2048 => (execute_BCAX_Z_ZZZ__ 2048 dn k m)
  | _ => (pure ())

def decode_EOR3_Z_ZZZ__ (Zm : (BitVec 5)) (Zk : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let m := (BitVec.toNat Zm)
  let k := (BitVec.toNat Zk)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_EOR3_Z_ZZZ__ 128 dn k m)
  | 256 => (execute_EOR3_Z_ZZZ__ 256 dn k m)
  | 512 => (execute_EOR3_Z_ZZZ__ 512 dn k m)
  | 1024 => (execute_EOR3_Z_ZZZ__ 1024 dn k m)
  | 2048 => (execute_EOR3_Z_ZZZ__ 2048 dn k m)
  | _ => (pure ())

def decode_BSL_Z_ZZZ__ (Zm : (BitVec 5)) (Zk : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let m := (BitVec.toNat Zm)
  let k := (BitVec.toNat Zk)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_BSL_Z_ZZZ__ 128 dn k m)
  | 256 => (execute_BSL_Z_ZZZ__ 256 dn k m)
  | 512 => (execute_BSL_Z_ZZZ__ 512 dn k m)
  | 1024 => (execute_BSL_Z_ZZZ__ 1024 dn k m)
  | 2048 => (execute_BSL_Z_ZZZ__ 2048 dn k m)
  | _ => (pure ())

def decode_BSL1N_Z_ZZZ__ (Zm : (BitVec 5)) (Zk : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let m := (BitVec.toNat Zm)
  let k := (BitVec.toNat Zk)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_BSL1N_Z_ZZZ__ 128 dn k m)
  | 256 => (execute_BSL1N_Z_ZZZ__ 256 dn k m)
  | 512 => (execute_BSL1N_Z_ZZZ__ 512 dn k m)
  | 1024 => (execute_BSL1N_Z_ZZZ__ 1024 dn k m)
  | 2048 => (execute_BSL1N_Z_ZZZ__ 2048 dn k m)
  | _ => (pure ())

def decode_BSL2N_Z_ZZZ__ (Zm : (BitVec 5)) (Zk : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let m := (BitVec.toNat Zm)
  let k := (BitVec.toNat Zk)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_BSL2N_Z_ZZZ__ 128 dn k m)
  | 256 => (execute_BSL2N_Z_ZZZ__ 256 dn k m)
  | 512 => (execute_BSL2N_Z_ZZZ__ 512 dn k m)
  | 1024 => (execute_BSL2N_Z_ZZZ__ 1024 dn k m)
  | 2048 => (execute_BSL2N_Z_ZZZ__ 2048 dn k m)
  | _ => (pure ())

def decode_NBSL_Z_ZZZ__ (Zm : (BitVec 5)) (Zk : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let m := (BitVec.toNat Zm)
  let k := (BitVec.toNat Zk)
  let dn := (BitVec.toNat Zdn)
  match VL with
  | 128 => (execute_NBSL_Z_ZZZ__ 128 dn k m)
  | 256 => (execute_NBSL_Z_ZZZ__ 256 dn k m)
  | 512 => (execute_NBSL_Z_ZZZ__ 512 dn k m)
  | 1024 => (execute_NBSL_Z_ZZZ__ 1024 dn k m)
  | 2048 => (execute_NBSL_Z_ZZZ__ 2048 dn k m)
  | _ => (pure ())

def decode_ADCLB_Z_ZZZ__ (sz : (BitVec 1)) (Zm : (BitVec 5)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_ADCLB_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_ADCLB_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_ADCLB_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_ADCLB_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_ADCLB_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_ADCLT_Z_ZZZ__ (sz : (BitVec 1)) (Zm : (BitVec 5)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_ADCLT_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_ADCLT_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_ADCLT_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_ADCLT_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_ADCLT_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_SBCLB_Z_ZZZ__ (sz : (BitVec 1)) (Zm : (BitVec 5)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SBCLB_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_SBCLB_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_SBCLB_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_SBCLB_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_SBCLB_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_SBCLT_Z_ZZZ__ (sz : (BitVec 1)) (Zm : (BitVec 5)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let da := (BitVec.toNat Zda)
  match VL with
  | 128 => (execute_SBCLT_Z_ZZZ__ 128 da esize m n)
  | 256 => (execute_SBCLT_Z_ZZZ__ 256 da esize m n)
  | 512 => (execute_SBCLT_Z_ZZZ__ 512 da esize m n)
  | 1024 => (execute_SBCLT_Z_ZZZ__ 1024 da esize m n)
  | 2048 => (execute_SBCLT_Z_ZZZ__ 2048 da esize m n)
  | _ => (pure ())

def decode_SMULH_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMULH_Z_ZZ__ 128 d esize m n is_unsigned)
  | 256 => (execute_SMULH_Z_ZZ__ 256 d esize m n is_unsigned)
  | 512 => (execute_SMULH_Z_ZZ__ 512 d esize m n is_unsigned)
  | 1024 => (execute_SMULH_Z_ZZ__ 1024 d esize m n is_unsigned)
  | 2048 => (execute_SMULH_Z_ZZ__ 2048 d esize m n is_unsigned)
  | _ => (pure ())

def decode_UMULH_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2 ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMULH_Z_ZZ__ 128 d esize m n is_unsigned)
  | 256 => (execute_UMULH_Z_ZZ__ 256 d esize m n is_unsigned)
  | 512 => (execute_UMULH_Z_ZZ__ 512 d esize m n is_unsigned)
  | 1024 => (execute_UMULH_Z_ZZ__ 1024 d esize m n is_unsigned)
  | 2048 => (execute_UMULH_Z_ZZ__ 2048 d esize m n is_unsigned)
  | _ => (pure ())

def decode_SCLAMP_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SCLAMP_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_SCLAMP_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_SCLAMP_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_SCLAMP_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_SCLAMP_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_UCLAMP_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_UCLAMP_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_UCLAMP_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_UCLAMP_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_UCLAMP_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_UCLAMP_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_REVD_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 128
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Zd)
  let swsize := 64
  match VL with
  | 128 => (execute_REVD_Z_P_Z__ 128 d esize g n swsize)
  | 256 => (execute_REVD_Z_P_Z__ 256 d esize g n swsize)
  | 512 => (execute_REVD_Z_P_Z__ 512 d esize g n swsize)
  | 1024 => (execute_REVD_Z_P_Z__ 1024 d esize g n swsize)
  | 2048 => (execute_REVD_Z_P_Z__ 2048 d esize g n swsize)
  | _ => (pure ())

def decode_PSEL_P_PPi__ (i1 : (BitVec 1)) (tszh : (BitVec 1)) (tszl : (BitVec 3)) (Rv : (BitVec 2)) (Pn : (BitVec 4)) (S : (BitVec 1)) (Pm : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let imm5 : (BitVec 5) := ((i1 +++ tszh) +++ tszl)
  let esize : Nat := 8
  let imm ← (( do (undefined_range 0 15) ) : SailM Nat )
  let (esize, imm) ← (( do
    let b__0 := (tszh +++ tszl)
    let (esize, imm) ← (( do
      if ((b__0 == (0x0#4 : (BitVec 4))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (let (esize, imm) : (Int × Nat) :=
          if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 64
            let imm : Nat := (BitVec.toNat (BitVec.join1 [(BitVec.access imm5 4)]))
            (esize, imm))
          else
            (let (esize, imm) : (Int × Nat) :=
              if (((Sail.BitVec.extractLsb b__0 2 0) == (0b100#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 32
                let imm : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 3))
                (esize, imm))
              else
                (let (esize, imm) : (Int × Nat) :=
                  if (((Sail.BitVec.extractLsb b__0 1 0) == (0b10#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 16
                    let imm : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 2))
                    (esize, imm))
                  else
                    (let esize : Nat := 8
                    let imm : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 1))
                    (esize, imm))
                (esize, imm))
            (esize, imm))
        (pure (esize, imm))) ) : SailM (Int × Nat) )
    (pure (esize, imm)) ) : SailM (Int × Nat) )
  let imm := imm
  let esize := esize
  let n := (BitVec.toNat Pn)
  let m := (BitVec.toNat Pm)
  let d := (BitVec.toNat Pd)
  let v := (BitVec.toNat (0b011#3 +++ Rv))
  match VL with
  | 128 => (execute_PSEL_P_PPi__ 128 d esize imm m n v)
  | 256 => (execute_PSEL_P_PPi__ 256 d esize imm m n v)
  | 512 => (execute_PSEL_P_PPi__ 512 d esize imm m n v)
  | 1024 => (execute_PSEL_P_PPi__ 1024 d esize imm m n v)
  | 2048 => (execute_PSEL_P_PPi__ 2048 d esize imm m n v)
  | _ => (pure ())

def decode_WHILELO_PP_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (Pd : (BitVec 3)) (eq : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d0 := (BitVec.toNat (Pd +++ 0#1))
  let d1 := (BitVec.toNat (Pd +++ 1#1))
  let is_unsigned : Bool := true
  let op : SVECmp := Cmp_LT
  match VL with
  | 128 => (execute_WHILELO_PP_RR__ 128 d0 d1 esize m n op rsize is_unsigned)
  | 256 => (execute_WHILELO_PP_RR__ 256 d0 d1 esize m n op rsize is_unsigned)
  | 512 => (execute_WHILELO_PP_RR__ 512 d0 d1 esize m n op rsize is_unsigned)
  | 1024 => (execute_WHILELO_PP_RR__ 1024 d0 d1 esize m n op rsize is_unsigned)
  | 2048 => (execute_WHILELO_PP_RR__ 2048 d0 d1 esize m n op rsize is_unsigned)
  | _ => (pure ())

def decode_WHILELS_PP_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (Pd : (BitVec 3)) (eq : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d0 := (BitVec.toNat (Pd +++ 0#1))
  let d1 := (BitVec.toNat (Pd +++ 1#1))
  let is_unsigned : Bool := true
  let op : SVECmp := Cmp_LE
  match VL with
  | 128 => (execute_WHILELS_PP_RR__ 128 d0 d1 esize m n op rsize is_unsigned)
  | 256 => (execute_WHILELS_PP_RR__ 256 d0 d1 esize m n op rsize is_unsigned)
  | 512 => (execute_WHILELS_PP_RR__ 512 d0 d1 esize m n op rsize is_unsigned)
  | 1024 => (execute_WHILELS_PP_RR__ 1024 d0 d1 esize m n op rsize is_unsigned)
  | 2048 => (execute_WHILELS_PP_RR__ 2048 d0 d1 esize m n op rsize is_unsigned)
  | _ => (pure ())

def decode_WHILELT_PP_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (Pd : (BitVec 3)) (eq : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d0 := (BitVec.toNat (Pd +++ 0#1))
  let d1 := (BitVec.toNat (Pd +++ 1#1))
  let is_unsigned : Bool := false
  let op : SVECmp := Cmp_LT
  match VL with
  | 128 => (execute_WHILELT_PP_RR__ 128 d0 d1 esize m n op rsize is_unsigned)
  | 256 => (execute_WHILELT_PP_RR__ 256 d0 d1 esize m n op rsize is_unsigned)
  | 512 => (execute_WHILELT_PP_RR__ 512 d0 d1 esize m n op rsize is_unsigned)
  | 1024 => (execute_WHILELT_PP_RR__ 1024 d0 d1 esize m n op rsize is_unsigned)
  | 2048 => (execute_WHILELT_PP_RR__ 2048 d0 d1 esize m n op rsize is_unsigned)
  | _ => (pure ())

def decode_WHILELE_PP_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (Pd : (BitVec 3)) (eq : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d0 := (BitVec.toNat (Pd +++ 0#1))
  let d1 := (BitVec.toNat (Pd +++ 1#1))
  let is_unsigned : Bool := false
  let op : SVECmp := Cmp_LE
  match VL with
  | 128 => (execute_WHILELE_PP_RR__ 128 d0 d1 esize m n op rsize is_unsigned)
  | 256 => (execute_WHILELE_PP_RR__ 256 d0 d1 esize m n op rsize is_unsigned)
  | 512 => (execute_WHILELE_PP_RR__ 512 d0 d1 esize m n op rsize is_unsigned)
  | 1024 => (execute_WHILELE_PP_RR__ 1024 d0 d1 esize m n op rsize is_unsigned)
  | 2048 => (execute_WHILELE_PP_RR__ 2048 d0 d1 esize m n op rsize is_unsigned)
  | _ => (pure ())

def decode_WHILEHI_PP_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (Pd : (BitVec 3)) (eq : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d0 := (BitVec.toNat (Pd +++ 0#1))
  let d1 := (BitVec.toNat (Pd +++ 1#1))
  let is_unsigned : Bool := true
  let op : SVECmp := Cmp_GT
  match VL with
  | 128 => (execute_WHILEHI_PP_RR__ 128 d0 d1 esize m n op rsize is_unsigned)
  | 256 => (execute_WHILEHI_PP_RR__ 256 d0 d1 esize m n op rsize is_unsigned)
  | 512 => (execute_WHILEHI_PP_RR__ 512 d0 d1 esize m n op rsize is_unsigned)
  | 1024 => (execute_WHILEHI_PP_RR__ 1024 d0 d1 esize m n op rsize is_unsigned)
  | 2048 => (execute_WHILEHI_PP_RR__ 2048 d0 d1 esize m n op rsize is_unsigned)
  | _ => (pure ())

def decode_WHILEHS_PP_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (Pd : (BitVec 3)) (eq : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d0 := (BitVec.toNat (Pd +++ 0#1))
  let d1 := (BitVec.toNat (Pd +++ 1#1))
  let is_unsigned : Bool := true
  let op : SVECmp := Cmp_GE
  match VL with
  | 128 => (execute_WHILEHS_PP_RR__ 128 d0 d1 esize m n op rsize is_unsigned)
  | 256 => (execute_WHILEHS_PP_RR__ 256 d0 d1 esize m n op rsize is_unsigned)
  | 512 => (execute_WHILEHS_PP_RR__ 512 d0 d1 esize m n op rsize is_unsigned)
  | 1024 => (execute_WHILEHS_PP_RR__ 1024 d0 d1 esize m n op rsize is_unsigned)
  | 2048 => (execute_WHILEHS_PP_RR__ 2048 d0 d1 esize m n op rsize is_unsigned)
  | _ => (pure ())

def decode_WHILEGT_PP_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (Pd : (BitVec 3)) (eq : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d0 := (BitVec.toNat (Pd +++ 0#1))
  let d1 := (BitVec.toNat (Pd +++ 1#1))
  let is_unsigned : Bool := false
  let op : SVECmp := Cmp_GT
  match VL with
  | 128 => (execute_WHILEGT_PP_RR__ 128 d0 d1 esize m n op rsize is_unsigned)
  | 256 => (execute_WHILEGT_PP_RR__ 256 d0 d1 esize m n op rsize is_unsigned)
  | 512 => (execute_WHILEGT_PP_RR__ 512 d0 d1 esize m n op rsize is_unsigned)
  | 1024 => (execute_WHILEGT_PP_RR__ 1024 d0 d1 esize m n op rsize is_unsigned)
  | 2048 => (execute_WHILEGT_PP_RR__ 2048 d0 d1 esize m n op rsize is_unsigned)
  | _ => (pure ())

def decode_WHILEGE_PP_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (Pd : (BitVec 3)) (eq : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d0 := (BitVec.toNat (Pd +++ 0#1))
  let d1 := (BitVec.toNat (Pd +++ 1#1))
  let is_unsigned : Bool := false
  let op : SVECmp := Cmp_GE
  match VL with
  | 128 => (execute_WHILEGE_PP_RR__ 128 d0 d1 esize m n op rsize is_unsigned)
  | 256 => (execute_WHILEGE_PP_RR__ 256 d0 d1 esize m n op rsize is_unsigned)
  | 512 => (execute_WHILEGE_PP_RR__ 512 d0 d1 esize m n op rsize is_unsigned)
  | 1024 => (execute_WHILEGE_PP_RR__ 1024 d0 d1 esize m n op rsize is_unsigned)
  | 2048 => (execute_WHILEGE_PP_RR__ 2048 d0 d1 esize m n op rsize is_unsigned)
  | _ => (pure ())

def decode_SQRSHRN_Z_MZ2__ (tszh : (BitVec 1)) (tszl : (BitVec 1)) (imm4 : (BitVec 4)) (U : (BitVec 1)) (R : (BitVec 1)) (Zn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat Zd)
  let shift := (esize -i (BitVec.toNat imm4))
  match VL with
  | 128 => (execute_SQRSHRN_Z_MZ2__ 128 d esize n shift)
  | 256 => (execute_SQRSHRN_Z_MZ2__ 256 d esize n shift)
  | 512 => (execute_SQRSHRN_Z_MZ2__ 512 d esize n shift)
  | 1024 => (execute_SQRSHRN_Z_MZ2__ 1024 d esize n shift)
  | 2048 => (execute_SQRSHRN_Z_MZ2__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQRSHRUN_Z_MZ2__ (tszh : (BitVec 1)) (tszl : (BitVec 1)) (imm4 : (BitVec 4)) (U : (BitVec 1)) (R : (BitVec 1)) (Zn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat Zd)
  let shift := (esize -i (BitVec.toNat imm4))
  match VL with
  | 128 => (execute_SQRSHRUN_Z_MZ2__ 128 d esize n shift)
  | 256 => (execute_SQRSHRUN_Z_MZ2__ 256 d esize n shift)
  | 512 => (execute_SQRSHRUN_Z_MZ2__ 512 d esize n shift)
  | 1024 => (execute_SQRSHRUN_Z_MZ2__ 1024 d esize n shift)
  | 2048 => (execute_SQRSHRUN_Z_MZ2__ 2048 d esize n shift)
  | _ => (pure ())

def decode_UQRSHRN_Z_MZ2__ (tszh : (BitVec 1)) (tszl : (BitVec 1)) (imm4 : (BitVec 4)) (U : (BitVec 1)) (R : (BitVec 1)) (Zn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat Zd)
  let shift := (esize -i (BitVec.toNat imm4))
  match VL with
  | 128 => (execute_UQRSHRN_Z_MZ2__ 128 d esize n shift)
  | 256 => (execute_UQRSHRN_Z_MZ2__ 256 d esize n shift)
  | 512 => (execute_UQRSHRN_Z_MZ2__ 512 d esize n shift)
  | 1024 => (execute_UQRSHRN_Z_MZ2__ 1024 d esize n shift)
  | 2048 => (execute_UQRSHRN_Z_MZ2__ 2048 d esize n shift)
  | _ => (pure ())

def decode_SQCVTN_Z_MZ2__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (U : (BitVec 1)) (Zn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQCVTN_Z_MZ2__ 128 d esize n)
  | 256 => (execute_SQCVTN_Z_MZ2__ 256 d esize n)
  | 512 => (execute_SQCVTN_Z_MZ2__ 512 d esize n)
  | 1024 => (execute_SQCVTN_Z_MZ2__ 1024 d esize n)
  | 2048 => (execute_SQCVTN_Z_MZ2__ 2048 d esize n)
  | _ => (pure ())

def decode_SQCVTUN_Z_MZ2__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (Zn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_SQCVTUN_Z_MZ2__ 128 d esize n)
  | 256 => (execute_SQCVTUN_Z_MZ2__ 256 d esize n)
  | 512 => (execute_SQCVTUN_Z_MZ2__ 512 d esize n)
  | 1024 => (execute_SQCVTUN_Z_MZ2__ 1024 d esize n)
  | 2048 => (execute_SQCVTUN_Z_MZ2__ 2048 d esize n)
  | _ => (pure ())

def decode_UQCVTN_Z_MZ2__ (tszh : (BitVec 1)) (tszl : (BitVec 2)) (U : (BitVec 1)) (Zn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let n := (BitVec.toNat (Zn +++ 0#1))
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_UQCVTN_Z_MZ2__ 128 d esize n)
  | 256 => (execute_UQCVTN_Z_MZ2__ 256 d esize n)
  | 512 => (execute_UQCVTN_Z_MZ2__ 512 d esize n)
  | 1024 => (execute_UQCVTN_Z_MZ2__ 1024 d esize n)
  | 2048 => (execute_UQCVTN_Z_MZ2__ 2048 d esize n)
  | _ => (pure ())

def decode_DUPQ_Z_Zi__ (i1 : (BitVec 1)) (tsz : (BitVec 4)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let imm : (BitVec 5) := (i1 +++ tsz)
  let esize : Nat := 8
  let index ← (( do (undefined_range 0 15) ) : SailM Nat )
  let (esize, index) ← (( do
    let b__0 := tsz
    let (esize, index) ← (( do
      if ((b__0 == (0x0#4 : (BitVec 4))) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (let (esize, index) : (Int × Nat) :=
          if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
          then
            (let esize : Nat := 64
            let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 4 4))
            (esize, index))
          else
            (let (esize, index) : (Int × Nat) :=
              if (((Sail.BitVec.extractLsb b__0 2 0) == (0b100#3 : (BitVec 3))) : Bool)
              then
                (let esize : Nat := 32
                let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 4 3))
                (esize, index))
              else
                (let (esize, index) : (Int × Nat) :=
                  if (((Sail.BitVec.extractLsb b__0 1 0) == (0b10#2 : (BitVec 2))) : Bool)
                  then
                    (let esize : Nat := 16
                    let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 4 2))
                    (esize, index))
                  else
                    (let esize : Nat := 8
                    let index : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm 4 1))
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
  | 128 => (execute_DUPQ_Z_Zi__ 128 d esize index n)
  | 256 => (execute_DUPQ_Z_Zi__ 256 d esize index n)
  | 512 => (execute_DUPQ_Z_Zi__ 512 d esize index n)
  | 1024 => (execute_DUPQ_Z_Zi__ 1024 d esize index n)
  | 2048 => (execute_DUPQ_Z_Zi__ 2048 d esize index n)
  | _ => (pure ())

def decode_EXTQ_Z_ZI_Des (imm4 : (BitVec 4)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let dn := (BitVec.toNat Zdn)
  let m := (BitVec.toNat Zm)
  let position := (Int.shiftl (BitVec.toNat imm4) 3)
  match VL with
  | 128 => (execute_EXTQ_Z_ZI_Des 128 dn m position)
  | 256 => (execute_EXTQ_Z_ZI_Des 256 dn m position)
  | 512 => (execute_EXTQ_Z_ZI_Des 512 dn m position)
  | 1024 => (execute_EXTQ_Z_ZI_Des 1024 dn m position)
  | 2048 => (execute_EXTQ_Z_ZI_Des 2048 dn m position)
  | _ => (pure ())

def decode_TBLQ_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_TBLQ_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_TBLQ_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_TBLQ_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_TBLQ_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_TBLQ_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_TBXQ_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  match VL with
  | 128 => (execute_TBXQ_Z_ZZ__ 128 d esize m n)
  | 256 => (execute_TBXQ_Z_ZZ__ 256 d esize m n)
  | 512 => (execute_TBXQ_Z_ZZ__ 512 d esize m n)
  | 1024 => (execute_TBXQ_Z_ZZ__ 1024 d esize m n)
  | 2048 => (execute_TBXQ_Z_ZZ__ 2048 d esize m n)
  | _ => (pure ())

def decode_UZPQ1_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let part := 0
  match VL with
  | 128 => (execute_UZPQ1_Z_ZZ__ 128 d esize m n part)
  | 256 => (execute_UZPQ1_Z_ZZ__ 256 d esize m n part)
  | 512 => (execute_UZPQ1_Z_ZZ__ 512 d esize m n part)
  | 1024 => (execute_UZPQ1_Z_ZZ__ 1024 d esize m n part)
  | 2048 => (execute_UZPQ1_Z_ZZ__ 2048 d esize m n part)
  | _ => (pure ())

def decode_UZPQ2_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let part := 1
  match VL with
  | 128 => (execute_UZPQ2_Z_ZZ__ 128 d esize m n part)
  | 256 => (execute_UZPQ2_Z_ZZ__ 256 d esize m n part)
  | 512 => (execute_UZPQ2_Z_ZZ__ 512 d esize m n part)
  | 1024 => (execute_UZPQ2_Z_ZZ__ 1024 d esize m n part)
  | 2048 => (execute_UZPQ2_Z_ZZ__ 2048 d esize m n part)
  | _ => (pure ())

def decode_ZIPQ1_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let part := 0
  match VL with
  | 128 => (execute_ZIPQ1_Z_ZZ__ 128 d esize m n part)
  | 256 => (execute_ZIPQ1_Z_ZZ__ 256 d esize m n part)
  | 512 => (execute_ZIPQ1_Z_ZZ__ 512 d esize m n part)
  | 1024 => (execute_ZIPQ1_Z_ZZ__ 1024 d esize m n part)
  | 2048 => (execute_ZIPQ1_Z_ZZ__ 2048 d esize m n part)
  | _ => (pure ())

def decode_ZIPQ2_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat Zn)
  let m := (BitVec.toNat Zm)
  let d := (BitVec.toNat Zd)
  let part := 1
  match VL with
  | 128 => (execute_ZIPQ2_Z_ZZ__ 128 d esize m n part)
  | 256 => (execute_ZIPQ2_Z_ZZ__ 256 d esize m n part)
  | 512 => (execute_ZIPQ2_Z_ZZ__ 512 d esize m n part)
  | 1024 => (execute_ZIPQ2_Z_ZZ__ 1024 d esize m n part)
  | 2048 => (execute_ZIPQ2_Z_ZZ__ 2048 d esize m n part)
  | _ => (pure ())

def decode_ANDQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_ANDQV_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_ANDQV_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_ANDQV_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_ANDQV_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_ANDQV_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_EORQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_EORQV_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_EORQV_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_EORQV_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_EORQV_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_EORQV_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_ORQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  match VL with
  | 128 => (execute_ORQV_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_ORQV_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_ORQV_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_ORQV_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_ORQV_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_ADDQV_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_ADDQV_Z_P_Z__ 128 d esize g n)
  | 256 => (execute_ADDQV_Z_P_Z__ 256 d esize g n)
  | 512 => (execute_ADDQV_Z_P_Z__ 512 d esize g n)
  | 1024 => (execute_ADDQV_Z_P_Z__ 1024 d esize g n)
  | 2048 => (execute_ADDQV_Z_P_Z__ 2048 d esize g n)
  | _ => (pure ())

def decode_SMAXQV_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMAXQV_Z_P_Z__ 128 d esize g n is_unsigned)
  | 256 => (execute_SMAXQV_Z_P_Z__ 256 d esize g n is_unsigned)
  | 512 => (execute_SMAXQV_Z_P_Z__ 512 d esize g n is_unsigned)
  | 1024 => (execute_SMAXQV_Z_P_Z__ 1024 d esize g n is_unsigned)
  | 2048 => (execute_SMAXQV_Z_P_Z__ 2048 d esize g n is_unsigned)
  | _ => (pure ())

def decode_UMAXQV_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMAXQV_Z_P_Z__ 128 d esize g n is_unsigned)
  | 256 => (execute_UMAXQV_Z_P_Z__ 256 d esize g n is_unsigned)
  | 512 => (execute_UMAXQV_Z_P_Z__ 512 d esize g n is_unsigned)
  | 1024 => (execute_UMAXQV_Z_P_Z__ 1024 d esize g n is_unsigned)
  | 2048 => (execute_UMAXQV_Z_P_Z__ 2048 d esize g n is_unsigned)
  | _ => (pure ())

def decode_SMINQV_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_SMINQV_Z_P_Z__ 128 d esize g n is_unsigned)
  | 256 => (execute_SMINQV_Z_P_Z__ 256 d esize g n is_unsigned)
  | 512 => (execute_SMINQV_Z_P_Z__ 512 d esize g n is_unsigned)
  | 1024 => (execute_SMINQV_Z_P_Z__ 1024 d esize g n is_unsigned)
  | 2048 => (execute_SMINQV_Z_P_Z__ 2048 d esize g n is_unsigned)
  | _ => (pure ())

def decode_UMINQV_Z_P_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Vd)
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_UMINQV_Z_P_Z__ 128 d esize g n is_unsigned)
  | 256 => (execute_UMINQV_Z_P_Z__ 256 d esize g n is_unsigned)
  | 512 => (execute_UMINQV_Z_P_Z__ 512 d esize g n is_unsigned)
  | 1024 => (execute_UMINQV_Z_P_Z__ 1024 d esize g n is_unsigned)
  | 2048 => (execute_UMINQV_Z_P_Z__ 2048 d esize g n is_unsigned)
  | _ => (pure ())

def decode_PMOV_Z_PI_B (Pn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Pn)
  let d := (BitVec.toNat Zd)
  let esize := 8
  let imm := 0
  match VL with
  | 128 => (execute_PMOV_Z_PI_B 128 d esize imm n)
  | 256 => (execute_PMOV_Z_PI_B 256 d esize imm n)
  | 512 => (execute_PMOV_Z_PI_B 512 d esize imm n)
  | 1024 => (execute_PMOV_Z_PI_B 1024 d esize imm n)
  | 2048 => (execute_PMOV_Z_PI_B 2048 d esize imm n)
  | _ => (pure ())

def decode_PMOV_Z_PI_H (i1 : (BitVec 1)) (Pn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Pn)
  let d := (BitVec.toNat Zd)
  let esize := 16
  let imm := (BitVec.toNat i1)
  match VL with
  | 128 => (execute_PMOV_Z_PI_H 128 d esize imm n)
  | 256 => (execute_PMOV_Z_PI_H 256 d esize imm n)
  | 512 => (execute_PMOV_Z_PI_H 512 d esize imm n)
  | 1024 => (execute_PMOV_Z_PI_H 1024 d esize imm n)
  | 2048 => (execute_PMOV_Z_PI_H 2048 d esize imm n)
  | _ => (pure ())

def decode_PMOV_Z_PI_S (i2 : (BitVec 2)) (Pn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Pn)
  let d := (BitVec.toNat Zd)
  let esize := 32
  let imm := (BitVec.toNat i2)
  match VL with
  | 128 => (execute_PMOV_Z_PI_S 128 d esize imm n)
  | 256 => (execute_PMOV_Z_PI_S 256 d esize imm n)
  | 512 => (execute_PMOV_Z_PI_S 512 d esize imm n)
  | 1024 => (execute_PMOV_Z_PI_S 1024 d esize imm n)
  | 2048 => (execute_PMOV_Z_PI_S 2048 d esize imm n)
  | _ => (pure ())

def decode_PMOV_Z_PI_D (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Pn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Pn)
  let d := (BitVec.toNat Zd)
  let esize := 64
  let imm := (BitVec.toNat (i3h +++ i3l))
  match VL with
  | 128 => (execute_PMOV_Z_PI_D 128 d esize imm n)
  | 256 => (execute_PMOV_Z_PI_D 256 d esize imm n)
  | 512 => (execute_PMOV_Z_PI_D 512 d esize imm n)
  | 1024 => (execute_PMOV_Z_PI_D 1024 d esize imm n)
  | 2048 => (execute_PMOV_Z_PI_D 2048 d esize imm n)
  | _ => (pure ())

def decode_PMOV_P_ZI_B (Zn : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let esize := 8
  let imm := 0
  match VL with
  | 128 => (execute_PMOV_P_ZI_B 128 d esize imm n)
  | 256 => (execute_PMOV_P_ZI_B 256 d esize imm n)
  | 512 => (execute_PMOV_P_ZI_B 512 d esize imm n)
  | 1024 => (execute_PMOV_P_ZI_B 1024 d esize imm n)
  | 2048 => (execute_PMOV_P_ZI_B 2048 d esize imm n)
  | _ => (pure ())

def decode_PMOV_P_ZI_H (i1 : (BitVec 1)) (Zn : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let esize := 16
  let imm := (BitVec.toNat i1)
  match VL with
  | 128 => (execute_PMOV_P_ZI_H 128 d esize imm n)
  | 256 => (execute_PMOV_P_ZI_H 256 d esize imm n)
  | 512 => (execute_PMOV_P_ZI_H 512 d esize imm n)
  | 1024 => (execute_PMOV_P_ZI_H 1024 d esize imm n)
  | 2048 => (execute_PMOV_P_ZI_H 2048 d esize imm n)
  | _ => (pure ())

def decode_PMOV_P_ZI_S (i2 : (BitVec 2)) (Zn : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let esize := 32
  let imm := (BitVec.toNat i2)
  match VL with
  | 128 => (execute_PMOV_P_ZI_S 128 d esize imm n)
  | 256 => (execute_PMOV_P_ZI_S 256 d esize imm n)
  | 512 => (execute_PMOV_P_ZI_S 512 d esize imm n)
  | 1024 => (execute_PMOV_P_ZI_S 1024 d esize imm n)
  | 2048 => (execute_PMOV_P_ZI_S 2048 d esize imm n)
  | _ => (pure ())

def decode_PMOV_P_ZI_D (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zn : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let n := (BitVec.toNat Zn)
  let d := (BitVec.toNat Pd)
  let esize := 64
  let imm := (BitVec.toNat (i3h +++ i3l))
  match VL with
  | 128 => (execute_PMOV_P_ZI_D 128 d esize imm n)
  | 256 => (execute_PMOV_P_ZI_D 256 d esize imm n)
  | 512 => (execute_PMOV_P_ZI_D 512 d esize imm n)
  | 1024 => (execute_PMOV_P_ZI_D 1024 d esize imm n)
  | 2048 => (execute_PMOV_P_ZI_D 2048 d esize imm n)
  | _ => (pure ())

def decode_PEXT_PN_RR__ (size : (BitVec 2)) (imm2 : (BitVec 2)) (PNn : (BitVec 3)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat (1#1 +++ PNn))
  let d := (BitVec.toNat Pd)
  let part := (BitVec.toNat imm2)
  match VL with
  | 128 => (execute_PEXT_PN_RR__ 128 d esize n part)
  | 256 => (execute_PEXT_PN_RR__ 256 d esize n part)
  | 512 => (execute_PEXT_PN_RR__ 512 d esize n part)
  | 1024 => (execute_PEXT_PN_RR__ 1024 d esize n part)
  | 2048 => (execute_PEXT_PN_RR__ 2048 d esize n part)
  | _ => (pure ())

def decode_PEXT_PP_RR__ (size : (BitVec 2)) (i1 : (BitVec 1)) (PNn : (BitVec 3)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat (1#1 +++ PNn))
  let d0 := (BitVec.toNat Pd)
  let d1 := (Nat.mod ((BitVec.toNat Pd) +i 1) 16)
  let part := (BitVec.toNat i1)
  match VL with
  | 128 => (execute_PEXT_PP_RR__ 128 d0 d1 esize n part)
  | 256 => (execute_PEXT_PP_RR__ 256 d0 d1 esize n part)
  | 512 => (execute_PEXT_PP_RR__ 512 d0 d1 esize n part)
  | 1024 => (execute_PEXT_PP_RR__ 1024 d0 d1 esize n part)
  | 2048 => (execute_PEXT_PP_RR__ 2048 d0 d1 esize n part)
  | _ => (pure ())

def decode_PTRUE_PN_I__ (size : (BitVec 2)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let d := (BitVec.toNat (1#1 +++ PNd))
  match VL with
  | 128 => (execute_PTRUE_PN_I__ 128 d esize)
  | 256 => (execute_PTRUE_PN_I__ 256 d esize)
  | 512 => (execute_PTRUE_PN_I__ 512 d esize)
  | 1024 => (execute_PTRUE_PN_I__ 1024 d esize)
  | 2048 => (execute_PTRUE_PN_I__ 2048 d esize)
  | _ => (pure ())

def decode_CNTP_R_PN__ (size : (BitVec 2)) (vl : (BitVec 1)) (PNn : (BitVec 4)) (Rd : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let n := (BitVec.toNat PNn)
  let d := (BitVec.toNat Rd)
  let width := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 15) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))) "src/instrs64_sve.sail:56606.130-56606.131"
      (execute_CNTP_R_PN__ 128 d esize n width))
  | 256 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 15) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))) "src/instrs64_sve.sail:56610.130-56610.131"
      (execute_CNTP_R_PN__ 256 d esize n width))
  | 512 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 15) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))) "src/instrs64_sve.sail:56614.130-56614.131"
      (execute_CNTP_R_PN__ 512 d esize n width))
  | 1024 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 15) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))) "src/instrs64_sve.sail:56618.131-56618.132"
      (execute_CNTP_R_PN__ 1024 d esize n width))
  | 2048 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 15) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))) "src/instrs64_sve.sail:56622.131-56622.132"
      (execute_CNTP_R_PN__ 2048 d esize n width))
  | _ => (pure ())

def decode_WHILELO_PN_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (vl : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat (1#1 +++ PNd))
  let is_unsigned : Bool := true
  let invert : Bool := false
  let op : SVECmp := Cmp_LT
  let width := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))))) "src/instrs64_sve.sail:56696.151-56696.152"
      (execute_WHILELO_PN_RR__ 128 d esize invert m n op rsize is_unsigned width))
  | 256 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))))) "src/instrs64_sve.sail:56700.151-56700.152"
      (execute_WHILELO_PN_RR__ 256 d esize invert m n op rsize is_unsigned width))
  | 512 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))))) "src/instrs64_sve.sail:56704.151-56704.152"
      (execute_WHILELO_PN_RR__ 512 d esize invert m n op rsize is_unsigned width))
  | 1024 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))))) "src/instrs64_sve.sail:56708.152-56708.153"
      (execute_WHILELO_PN_RR__ 1024 d esize invert m n op rsize is_unsigned width))
  | 2048 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))))) "src/instrs64_sve.sail:56712.152-56712.153"
      (execute_WHILELO_PN_RR__ 2048 d esize invert m n op rsize is_unsigned width))
  | _ => (pure ())

def decode_WHILELS_PN_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (vl : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat (1#1 +++ PNd))
  let is_unsigned : Bool := true
  let invert : Bool := false
  let op : SVECmp := Cmp_LE
  let width := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))))) "src/instrs64_sve.sail:56790.151-56790.152"
      (execute_WHILELS_PN_RR__ 128 d esize invert m n op rsize is_unsigned width))
  | 256 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))))) "src/instrs64_sve.sail:56794.151-56794.152"
      (execute_WHILELS_PN_RR__ 256 d esize invert m n op rsize is_unsigned width))
  | 512 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))))) "src/instrs64_sve.sail:56798.151-56798.152"
      (execute_WHILELS_PN_RR__ 512 d esize invert m n op rsize is_unsigned width))
  | 1024 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))))) "src/instrs64_sve.sail:56802.152-56802.153"
      (execute_WHILELS_PN_RR__ 1024 d esize invert m n op rsize is_unsigned width))
  | 2048 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))))) "src/instrs64_sve.sail:56806.152-56806.153"
      (execute_WHILELS_PN_RR__ 2048 d esize invert m n op rsize is_unsigned width))
  | _ => (pure ())

def decode_WHILELT_PN_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (vl : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat (1#1 +++ PNd))
  let is_unsigned : Bool := false
  let invert : Bool := false
  let op : SVECmp := Cmp_LT
  let width := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))))) "src/instrs64_sve.sail:56884.151-56884.152"
      (execute_WHILELT_PN_RR__ 128 d esize invert m n op rsize is_unsigned width))
  | 256 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))))) "src/instrs64_sve.sail:56888.151-56888.152"
      (execute_WHILELT_PN_RR__ 256 d esize invert m n op rsize is_unsigned width))
  | 512 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))))) "src/instrs64_sve.sail:56892.151-56892.152"
      (execute_WHILELT_PN_RR__ 512 d esize invert m n op rsize is_unsigned width))
  | 1024 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))))) "src/instrs64_sve.sail:56896.152-56896.153"
      (execute_WHILELT_PN_RR__ 1024 d esize invert m n op rsize is_unsigned width))
  | 2048 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))))) "src/instrs64_sve.sail:56900.152-56900.153"
      (execute_WHILELT_PN_RR__ 2048 d esize invert m n op rsize is_unsigned width))
  | _ => (pure ())

def decode_WHILELE_PN_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (vl : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat (1#1 +++ PNd))
  let is_unsigned : Bool := false
  let invert : Bool := false
  let op : SVECmp := Cmp_LE
  let width := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))))) "src/instrs64_sve.sail:56978.151-56978.152"
      (execute_WHILELE_PN_RR__ 128 d esize invert m n op rsize is_unsigned width))
  | 256 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))))) "src/instrs64_sve.sail:56982.151-56982.152"
      (execute_WHILELE_PN_RR__ 256 d esize invert m n op rsize is_unsigned width))
  | 512 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))))) "src/instrs64_sve.sail:56986.151-56986.152"
      (execute_WHILELE_PN_RR__ 512 d esize invert m n op rsize is_unsigned width))
  | 1024 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))))) "src/instrs64_sve.sail:56990.152-56990.153"
      (execute_WHILELE_PN_RR__ 1024 d esize invert m n op rsize is_unsigned width))
  | 2048 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))))) "src/instrs64_sve.sail:56994.152-56994.153"
      (execute_WHILELE_PN_RR__ 2048 d esize invert m n op rsize is_unsigned width))
  | _ => (pure ())

def decode_WHILEHI_PN_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (vl : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat (1#1 +++ PNd))
  let is_unsigned : Bool := true
  let invert : Bool := true
  let op : SVECmp := Cmp_GT
  let width := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))))) "src/instrs64_sve.sail:57072.151-57072.152"
      (execute_WHILEHI_PN_RR__ 128 d esize invert m n op rsize is_unsigned width))
  | 256 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))))) "src/instrs64_sve.sail:57076.151-57076.152"
      (execute_WHILEHI_PN_RR__ 256 d esize invert m n op rsize is_unsigned width))
  | 512 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))))) "src/instrs64_sve.sail:57080.151-57080.152"
      (execute_WHILEHI_PN_RR__ 512 d esize invert m n op rsize is_unsigned width))
  | 1024 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))))) "src/instrs64_sve.sail:57084.152-57084.153"
      (execute_WHILEHI_PN_RR__ 1024 d esize invert m n op rsize is_unsigned width))
  | 2048 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))))) "src/instrs64_sve.sail:57088.152-57088.153"
      (execute_WHILEHI_PN_RR__ 2048 d esize invert m n op rsize is_unsigned width))
  | _ => (pure ())

def decode_WHILEHS_PN_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (vl : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat (1#1 +++ PNd))
  let is_unsigned : Bool := true
  let invert : Bool := true
  let op : SVECmp := Cmp_GE
  let width := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))))) "src/instrs64_sve.sail:57166.151-57166.152"
      (execute_WHILEHS_PN_RR__ 128 d esize invert m n op rsize is_unsigned width))
  | 256 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))))) "src/instrs64_sve.sail:57170.151-57170.152"
      (execute_WHILEHS_PN_RR__ 256 d esize invert m n op rsize is_unsigned width))
  | 512 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))))) "src/instrs64_sve.sail:57174.151-57174.152"
      (execute_WHILEHS_PN_RR__ 512 d esize invert m n op rsize is_unsigned width))
  | 1024 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))))) "src/instrs64_sve.sail:57178.152-57178.153"
      (execute_WHILEHS_PN_RR__ 1024 d esize invert m n op rsize is_unsigned width))
  | 2048 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))))) "src/instrs64_sve.sail:57182.152-57182.153"
      (execute_WHILEHS_PN_RR__ 2048 d esize invert m n op rsize is_unsigned width))
  | _ => (pure ())

def decode_WHILEGT_PN_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (vl : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat (1#1 +++ PNd))
  let is_unsigned : Bool := false
  let invert : Bool := true
  let op : SVECmp := Cmp_GT
  let width := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))))) "src/instrs64_sve.sail:57260.151-57260.152"
      (execute_WHILEGT_PN_RR__ 128 d esize invert m n op rsize is_unsigned width))
  | 256 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))))) "src/instrs64_sve.sail:57264.151-57264.152"
      (execute_WHILEGT_PN_RR__ 256 d esize invert m n op rsize is_unsigned width))
  | 512 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))))) "src/instrs64_sve.sail:57268.151-57268.152"
      (execute_WHILEGT_PN_RR__ 512 d esize invert m n op rsize is_unsigned width))
  | 1024 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))))) "src/instrs64_sve.sail:57272.152-57272.153"
      (execute_WHILEGT_PN_RR__ 1024 d esize invert m n op rsize is_unsigned width))
  | 2048 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))))) "src/instrs64_sve.sail:57276.152-57276.153"
      (execute_WHILEGT_PN_RR__ 2048 d esize invert m n op rsize is_unsigned width))
  | _ => (pure ())

def decode_WHILEGE_PN_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (vl : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSME2 ())))) <&&> (do
       (pure (! (← (HaveSVE2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let rsize := 64
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let d := (BitVec.toNat (1#1 +++ PNd))
  let is_unsigned : Bool := false
  let invert : Bool := true
  let op : SVECmp := Cmp_GE
  let width := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))))) "src/instrs64_sve.sail:57354.151-57354.152"
      (execute_WHILEGE_PN_RR__ 128 d esize invert m n op rsize is_unsigned width))
  | 256 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))))) "src/instrs64_sve.sail:57358.151-57358.152"
      (execute_WHILEGE_PN_RR__ 256 d esize invert m n op rsize is_unsigned width))
  | 512 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))))) "src/instrs64_sve.sail:57362.151-57362.152"
      (execute_WHILEGE_PN_RR__ 512 d esize invert m n op rsize is_unsigned width))
  | 1024 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))))) "src/instrs64_sve.sail:57366.152-57366.153"
      (execute_WHILEGE_PN_RR__ 1024 d esize invert m n op rsize is_unsigned width))
  | 2048 =>
    (do
      sail_assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))))) "src/instrs64_sve.sail:57370.152-57370.153"
      (execute_WHILEGE_PN_RR__ 2048 d esize invert m n op rsize is_unsigned width))
  | _ => (pure ())

def decode_LD1B_Z_P_BZ_S_x32_unscaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LD1B_Z_P_BZ_S_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1B_Z_P_BZ_S_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1B_Z_P_BZ_S_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1B_Z_P_BZ_S_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1B_Z_P_BZ_S_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1SB_Z_P_BZ_S_x32_unscaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let offs_size := 32
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LD1SB_Z_P_BZ_S_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1SB_Z_P_BZ_S_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1SB_Z_P_BZ_S_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1SB_Z_P_BZ_S_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1SB_Z_P_BZ_S_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1B_Z_P_BZ_S_x32_unscaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1B_Z_P_BZ_S_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1B_Z_P_BZ_S_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1B_Z_P_BZ_S_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1B_Z_P_BZ_S_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1B_Z_P_BZ_S_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SB_Z_P_BZ_S_x32_unscaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let offs_size := 32
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1SB_Z_P_BZ_S_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1SB_Z_P_BZ_S_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1SB_Z_P_BZ_S_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1SB_Z_P_BZ_S_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1SB_Z_P_BZ_S_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1H_Z_P_BZ_S_x32_unscaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LD1H_Z_P_BZ_S_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1H_Z_P_BZ_S_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1H_Z_P_BZ_S_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1H_Z_P_BZ_S_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1H_Z_P_BZ_S_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1SH_Z_P_BZ_S_x32_unscaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let offs_size := 32
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LD1SH_Z_P_BZ_S_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1SH_Z_P_BZ_S_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1SH_Z_P_BZ_S_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1SH_Z_P_BZ_S_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1SH_Z_P_BZ_S_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1H_Z_P_BZ_S_x32_unscaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1H_Z_P_BZ_S_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1H_Z_P_BZ_S_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1H_Z_P_BZ_S_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1H_Z_P_BZ_S_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1H_Z_P_BZ_S_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SH_Z_P_BZ_S_x32_unscaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let offs_size := 32
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1SH_Z_P_BZ_S_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1SH_Z_P_BZ_S_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1SH_Z_P_BZ_S_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1SH_Z_P_BZ_S_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1SH_Z_P_BZ_S_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1W_Z_P_BZ_S_x32_unscaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 32
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LD1W_Z_P_BZ_S_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1W_Z_P_BZ_S_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1W_Z_P_BZ_S_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1W_Z_P_BZ_S_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1W_Z_P_BZ_S_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1W_Z_P_BZ_S_x32_unscaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 32
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1W_Z_P_BZ_S_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1W_Z_P_BZ_S_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1W_Z_P_BZ_S_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1W_Z_P_BZ_S_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1W_Z_P_BZ_S_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_PRFB_I_P_BZ_S_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_PRFB_I_P_BZ_S_x32_scaled 128 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 256 => (execute_PRFB_I_P_BZ_S_x32_scaled 256 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 512 => (execute_PRFB_I_P_BZ_S_x32_scaled 512 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 1024 => (execute_PRFB_I_P_BZ_S_x32_scaled 1024 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 2048 => (execute_PRFB_I_P_BZ_S_x32_scaled 2048 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | _ => (pure ())

def decode_PRFH_I_P_BZ_S_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 1
  match VL with
  | 128 => (execute_PRFH_I_P_BZ_S_x32_scaled 128 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 256 => (execute_PRFH_I_P_BZ_S_x32_scaled 256 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 512 => (execute_PRFH_I_P_BZ_S_x32_scaled 512 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 1024 => (execute_PRFH_I_P_BZ_S_x32_scaled 1024 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 2048 => (execute_PRFH_I_P_BZ_S_x32_scaled 2048 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | _ => (pure ())

def decode_PRFW_I_P_BZ_S_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 2
  match VL with
  | 128 => (execute_PRFW_I_P_BZ_S_x32_scaled 128 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 256 => (execute_PRFW_I_P_BZ_S_x32_scaled 256 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 512 => (execute_PRFW_I_P_BZ_S_x32_scaled 512 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 1024 => (execute_PRFW_I_P_BZ_S_x32_scaled 1024 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 2048 => (execute_PRFW_I_P_BZ_S_x32_scaled 2048 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | _ => (pure ())

def decode_PRFD_I_P_BZ_S_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 3
  match VL with
  | 128 => (execute_PRFD_I_P_BZ_S_x32_scaled 128 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 256 => (execute_PRFD_I_P_BZ_S_x32_scaled 256 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 512 => (execute_PRFD_I_P_BZ_S_x32_scaled 512 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 1024 => (execute_PRFD_I_P_BZ_S_x32_scaled 1024 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 2048 => (execute_PRFD_I_P_BZ_S_x32_scaled 2048 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | _ => (pure ())

def decode_LD1H_Z_P_BZ_S_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 1
  match VL with
  | 128 => (execute_LD1H_Z_P_BZ_S_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1H_Z_P_BZ_S_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1H_Z_P_BZ_S_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1H_Z_P_BZ_S_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1H_Z_P_BZ_S_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1SH_Z_P_BZ_S_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let offs_size := 32
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 1
  match VL with
  | 128 => (execute_LD1SH_Z_P_BZ_S_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1SH_Z_P_BZ_S_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1SH_Z_P_BZ_S_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1SH_Z_P_BZ_S_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1SH_Z_P_BZ_S_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1H_Z_P_BZ_S_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 1
  match VL with
  | 128 => (execute_LDFF1H_Z_P_BZ_S_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1H_Z_P_BZ_S_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1H_Z_P_BZ_S_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1H_Z_P_BZ_S_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1H_Z_P_BZ_S_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SH_Z_P_BZ_S_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let offs_size := 32
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 1
  match VL with
  | 128 => (execute_LDFF1SH_Z_P_BZ_S_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1SH_Z_P_BZ_S_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1SH_Z_P_BZ_S_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1SH_Z_P_BZ_S_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1SH_Z_P_BZ_S_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1W_Z_P_BZ_S_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 32
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 2
  match VL with
  | 128 => (execute_LD1W_Z_P_BZ_S_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1W_Z_P_BZ_S_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1W_Z_P_BZ_S_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1W_Z_P_BZ_S_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1W_Z_P_BZ_S_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1W_Z_P_BZ_S_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 32
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 2
  match VL with
  | 128 => (execute_LDFF1W_Z_P_BZ_S_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1W_Z_P_BZ_S_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1W_Z_P_BZ_S_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1W_Z_P_BZ_S_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1W_Z_P_BZ_S_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDR_P_BI__ (imm9h : (BitVec 6)) (imm9l : (BitVec 3)) (Rn : (BitVec 5)) (Pt : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Pt)
  let n := (BitVec.toNat Rn)
  let imm := (BitVec.toInt (imm9h +++ imm9l))
  match VL with
  | 128 => (execute_LDR_P_BI__ 128 imm n t)
  | 256 => (execute_LDR_P_BI__ 256 imm n t)
  | 512 => (execute_LDR_P_BI__ 512 imm n t)
  | 1024 => (execute_LDR_P_BI__ 1024 imm n t)
  | 2048 => (execute_LDR_P_BI__ 2048 imm n t)
  | _ => (pure ())

def decode_LDR_Z_BI__ (imm9h : (BitVec 6)) (imm9l : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let imm := (BitVec.toInt (imm9h +++ imm9l))
  match VL with
  | 128 => (execute_LDR_Z_BI__ 128 imm n t)
  | 256 => (execute_LDR_Z_BI__ 256 imm n t)
  | 512 => (execute_LDR_Z_BI__ 512 imm n t)
  | 1024 => (execute_LDR_Z_BI__ 1024 imm n t)
  | 2048 => (execute_LDR_Z_BI__ 2048 imm n t)
  | _ => (pure ())

def decode_PRFB_I_P_BI_S (imm6 : (BitVec 6)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale := 0
  let offset := (BitVec.toInt imm6)
  match VL with
  | 128 => (execute_PRFB_I_P_BI_S 128 esize g level n offset pref_hint scale stream)
  | 256 => (execute_PRFB_I_P_BI_S 256 esize g level n offset pref_hint scale stream)
  | 512 => (execute_PRFB_I_P_BI_S 512 esize g level n offset pref_hint scale stream)
  | 1024 => (execute_PRFB_I_P_BI_S 1024 esize g level n offset pref_hint scale stream)
  | 2048 => (execute_PRFB_I_P_BI_S 2048 esize g level n offset pref_hint scale stream)
  | _ => (pure ())

def decode_PRFH_I_P_BI_S (imm6 : (BitVec 6)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale := 1
  let offset := (BitVec.toInt imm6)
  match VL with
  | 128 => (execute_PRFH_I_P_BI_S 128 esize g level n offset pref_hint scale stream)
  | 256 => (execute_PRFH_I_P_BI_S 256 esize g level n offset pref_hint scale stream)
  | 512 => (execute_PRFH_I_P_BI_S 512 esize g level n offset pref_hint scale stream)
  | 1024 => (execute_PRFH_I_P_BI_S 1024 esize g level n offset pref_hint scale stream)
  | 2048 => (execute_PRFH_I_P_BI_S 2048 esize g level n offset pref_hint scale stream)
  | _ => (pure ())

def decode_PRFW_I_P_BI_S (imm6 : (BitVec 6)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale := 2
  let offset := (BitVec.toInt imm6)
  match VL with
  | 128 => (execute_PRFW_I_P_BI_S 128 esize g level n offset pref_hint scale stream)
  | 256 => (execute_PRFW_I_P_BI_S 256 esize g level n offset pref_hint scale stream)
  | 512 => (execute_PRFW_I_P_BI_S 512 esize g level n offset pref_hint scale stream)
  | 1024 => (execute_PRFW_I_P_BI_S 1024 esize g level n offset pref_hint scale stream)
  | 2048 => (execute_PRFW_I_P_BI_S 2048 esize g level n offset pref_hint scale stream)
  | _ => (pure ())

def decode_PRFD_I_P_BI_S (imm6 : (BitVec 6)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale := 3
  let offset := (BitVec.toInt imm6)
  match VL with
  | 128 => (execute_PRFD_I_P_BI_S 128 esize g level n offset pref_hint scale stream)
  | 256 => (execute_PRFD_I_P_BI_S 256 esize g level n offset pref_hint scale stream)
  | 512 => (execute_PRFD_I_P_BI_S 512 esize g level n offset pref_hint scale stream)
  | 1024 => (execute_PRFD_I_P_BI_S 1024 esize g level n offset pref_hint scale stream)
  | 2048 => (execute_PRFD_I_P_BI_S 2048 esize g level n offset pref_hint scale stream)
  | _ => (pure ())

def decode_PRFB_I_P_BR_S (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 8
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale := 0
  match VL with
  | 128 => (execute_PRFB_I_P_BR_S 128 esize g level m n pref_hint scale stream)
  | 256 => (execute_PRFB_I_P_BR_S 256 esize g level m n pref_hint scale stream)
  | 512 => (execute_PRFB_I_P_BR_S 512 esize g level m n pref_hint scale stream)
  | 1024 => (execute_PRFB_I_P_BR_S 1024 esize g level m n pref_hint scale stream)
  | 2048 => (execute_PRFB_I_P_BR_S 2048 esize g level m n pref_hint scale stream)
  | _ => (pure ())

def decode_PRFH_I_P_BR_S (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 16
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale := 1
  match VL with
  | 128 => (execute_PRFH_I_P_BR_S 128 esize g level m n pref_hint scale stream)
  | 256 => (execute_PRFH_I_P_BR_S 256 esize g level m n pref_hint scale stream)
  | 512 => (execute_PRFH_I_P_BR_S 512 esize g level m n pref_hint scale stream)
  | 1024 => (execute_PRFH_I_P_BR_S 1024 esize g level m n pref_hint scale stream)
  | 2048 => (execute_PRFH_I_P_BR_S 2048 esize g level m n pref_hint scale stream)
  | _ => (pure ())

def decode_PRFW_I_P_BR_S (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale := 2
  match VL with
  | 128 => (execute_PRFW_I_P_BR_S 128 esize g level m n pref_hint scale stream)
  | 256 => (execute_PRFW_I_P_BR_S 256 esize g level m n pref_hint scale stream)
  | 512 => (execute_PRFW_I_P_BR_S 512 esize g level m n pref_hint scale stream)
  | 1024 => (execute_PRFW_I_P_BR_S 1024 esize g level m n pref_hint scale stream)
  | 2048 => (execute_PRFW_I_P_BR_S 2048 esize g level m n pref_hint scale stream)
  | _ => (pure ())

def decode_PRFD_I_P_BR_S (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale := 3
  match VL with
  | 128 => (execute_PRFD_I_P_BR_S 128 esize g level m n pref_hint scale stream)
  | 256 => (execute_PRFD_I_P_BR_S 256 esize g level m n pref_hint scale stream)
  | 512 => (execute_PRFD_I_P_BR_S 512 esize g level m n pref_hint scale stream)
  | 1024 => (execute_PRFD_I_P_BR_S 1024 esize g level m n pref_hint scale stream)
  | 2048 => (execute_PRFD_I_P_BR_S 2048 esize g level m n pref_hint scale stream)
  | _ => (pure ())

def decode_PRFB_I_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale := 0
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_PRFB_I_P_AI_S 128 esize g level n offset pref_hint scale stream)
  | 256 => (execute_PRFB_I_P_AI_S 256 esize g level n offset pref_hint scale stream)
  | 512 => (execute_PRFB_I_P_AI_S 512 esize g level n offset pref_hint scale stream)
  | 1024 => (execute_PRFB_I_P_AI_S 1024 esize g level n offset pref_hint scale stream)
  | 2048 => (execute_PRFB_I_P_AI_S 2048 esize g level n offset pref_hint scale stream)
  | _ => (pure ())

def decode_PRFH_I_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale := 1
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_PRFH_I_P_AI_S 128 esize g level n offset pref_hint scale stream)
  | 256 => (execute_PRFH_I_P_AI_S 256 esize g level n offset pref_hint scale stream)
  | 512 => (execute_PRFH_I_P_AI_S 512 esize g level n offset pref_hint scale stream)
  | 1024 => (execute_PRFH_I_P_AI_S 1024 esize g level n offset pref_hint scale stream)
  | 2048 => (execute_PRFH_I_P_AI_S 2048 esize g level n offset pref_hint scale stream)
  | _ => (pure ())

def decode_PRFW_I_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale := 2
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_PRFW_I_P_AI_S 128 esize g level n offset pref_hint scale stream)
  | 256 => (execute_PRFW_I_P_AI_S 256 esize g level n offset pref_hint scale stream)
  | 512 => (execute_PRFW_I_P_AI_S 512 esize g level n offset pref_hint scale stream)
  | 1024 => (execute_PRFW_I_P_AI_S 1024 esize g level n offset pref_hint scale stream)
  | 2048 => (execute_PRFW_I_P_AI_S 2048 esize g level n offset pref_hint scale stream)
  | _ => (pure ())

def decode_PRFD_I_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 32
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale := 3
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_PRFD_I_P_AI_S 128 esize g level n offset pref_hint scale stream)
  | 256 => (execute_PRFD_I_P_AI_S 256 esize g level n offset pref_hint scale stream)
  | 512 => (execute_PRFD_I_P_AI_S 512 esize g level n offset pref_hint scale stream)
  | 1024 => (execute_PRFD_I_P_AI_S 1024 esize g level n offset pref_hint scale stream)
  | 2048 => (execute_PRFD_I_P_AI_S 2048 esize g level n offset pref_hint scale stream)
  | _ => (pure ())

def decode_LD1B_Z_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LD1B_Z_P_AI_S 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1B_Z_P_AI_S 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1B_Z_P_AI_S 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1B_Z_P_AI_S 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1B_Z_P_AI_S 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1SB_Z_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let is_unsigned : Bool := false
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LD1SB_Z_P_AI_S 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1SB_Z_P_AI_S 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1SB_Z_P_AI_S 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1SB_Z_P_AI_S 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1SB_Z_P_AI_S 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDFF1B_Z_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LDFF1B_Z_P_AI_S 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDFF1B_Z_P_AI_S 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDFF1B_Z_P_AI_S 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDFF1B_Z_P_AI_S 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDFF1B_Z_P_AI_S 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SB_Z_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let is_unsigned : Bool := false
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LDFF1SB_Z_P_AI_S 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDFF1SB_Z_P_AI_S 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDFF1SB_Z_P_AI_S 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDFF1SB_Z_P_AI_S 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDFF1SB_Z_P_AI_S 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1H_Z_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LD1H_Z_P_AI_S 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1H_Z_P_AI_S 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1H_Z_P_AI_S 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1H_Z_P_AI_S 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1H_Z_P_AI_S 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1SH_Z_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let is_unsigned : Bool := false
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LD1SH_Z_P_AI_S 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1SH_Z_P_AI_S 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1SH_Z_P_AI_S 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1SH_Z_P_AI_S 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1SH_Z_P_AI_S 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDFF1H_Z_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LDFF1H_Z_P_AI_S 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDFF1H_Z_P_AI_S 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDFF1H_Z_P_AI_S 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDFF1H_Z_P_AI_S 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDFF1H_Z_P_AI_S 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SH_Z_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let is_unsigned : Bool := false
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LDFF1SH_Z_P_AI_S 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDFF1SH_Z_P_AI_S 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDFF1SH_Z_P_AI_S 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDFF1SH_Z_P_AI_S 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDFF1SH_Z_P_AI_S 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1W_Z_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 32
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LD1W_Z_P_AI_S 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1W_Z_P_AI_S 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1W_Z_P_AI_S 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1W_Z_P_AI_S 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1W_Z_P_AI_S 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDFF1W_Z_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 32
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LDFF1W_Z_P_AI_S 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDFF1W_Z_P_AI_S 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDFF1W_Z_P_AI_S 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDFF1W_Z_P_AI_S 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDFF1W_Z_P_AI_S 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1RB_Z_P_BI_U8 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 8
  let msize := 8
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm6)
  match VL with
  | 128 => (execute_LD1RB_Z_P_BI_U8 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1RB_Z_P_BI_U8 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1RB_Z_P_BI_U8 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1RB_Z_P_BI_U8 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1RB_Z_P_BI_U8 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1RB_Z_P_BI_U16 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let msize := 8
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm6)
  match VL with
  | 128 => (execute_LD1RB_Z_P_BI_U16 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1RB_Z_P_BI_U16 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1RB_Z_P_BI_U16 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1RB_Z_P_BI_U16 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1RB_Z_P_BI_U16 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1RB_Z_P_BI_U32 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm6)
  match VL with
  | 128 => (execute_LD1RB_Z_P_BI_U32 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1RB_Z_P_BI_U32 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1RB_Z_P_BI_U32 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1RB_Z_P_BI_U32 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1RB_Z_P_BI_U32 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1RB_Z_P_BI_U64 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm6)
  match VL with
  | 128 => (execute_LD1RB_Z_P_BI_U64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1RB_Z_P_BI_U64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1RB_Z_P_BI_U64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1RB_Z_P_BI_U64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1RB_Z_P_BI_U64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1RSW_Z_P_BI_S64 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let is_unsigned : Bool := false
  let offset := (BitVec.toNat imm6)
  match VL with
  | 128 => (execute_LD1RSW_Z_P_BI_S64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1RSW_Z_P_BI_S64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1RSW_Z_P_BI_S64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1RSW_Z_P_BI_S64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1RSW_Z_P_BI_S64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1RH_Z_P_BI_U16 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let msize := 16
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm6)
  match VL with
  | 128 => (execute_LD1RH_Z_P_BI_U16 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1RH_Z_P_BI_U16 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1RH_Z_P_BI_U16 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1RH_Z_P_BI_U16 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1RH_Z_P_BI_U16 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1RH_Z_P_BI_U32 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm6)
  match VL with
  | 128 => (execute_LD1RH_Z_P_BI_U32 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1RH_Z_P_BI_U32 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1RH_Z_P_BI_U32 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1RH_Z_P_BI_U32 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1RH_Z_P_BI_U32 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1RH_Z_P_BI_U64 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm6)
  match VL with
  | 128 => (execute_LD1RH_Z_P_BI_U64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1RH_Z_P_BI_U64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1RH_Z_P_BI_U64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1RH_Z_P_BI_U64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1RH_Z_P_BI_U64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1RSH_Z_P_BI_S64 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let is_unsigned : Bool := false
  let offset := (BitVec.toNat imm6)
  match VL with
  | 128 => (execute_LD1RSH_Z_P_BI_S64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1RSH_Z_P_BI_S64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1RSH_Z_P_BI_S64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1RSH_Z_P_BI_S64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1RSH_Z_P_BI_S64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1RSH_Z_P_BI_S32 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let is_unsigned : Bool := false
  let offset := (BitVec.toNat imm6)
  match VL with
  | 128 => (execute_LD1RSH_Z_P_BI_S32 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1RSH_Z_P_BI_S32 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1RSH_Z_P_BI_S32 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1RSH_Z_P_BI_S32 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1RSH_Z_P_BI_S32 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1RW_Z_P_BI_U32 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 32
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm6)
  match VL with
  | 128 => (execute_LD1RW_Z_P_BI_U32 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1RW_Z_P_BI_U32 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1RW_Z_P_BI_U32 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1RW_Z_P_BI_U32 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1RW_Z_P_BI_U32 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1RW_Z_P_BI_U64 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm6)
  match VL with
  | 128 => (execute_LD1RW_Z_P_BI_U64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1RW_Z_P_BI_U64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1RW_Z_P_BI_U64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1RW_Z_P_BI_U64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1RW_Z_P_BI_U64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1RSB_Z_P_BI_S64 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let is_unsigned : Bool := false
  let offset := (BitVec.toNat imm6)
  match VL with
  | 128 => (execute_LD1RSB_Z_P_BI_S64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1RSB_Z_P_BI_S64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1RSB_Z_P_BI_S64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1RSB_Z_P_BI_S64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1RSB_Z_P_BI_S64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1RSB_Z_P_BI_S32 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let is_unsigned : Bool := false
  let offset := (BitVec.toNat imm6)
  match VL with
  | 128 => (execute_LD1RSB_Z_P_BI_S32 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1RSB_Z_P_BI_S32 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1RSB_Z_P_BI_S32 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1RSB_Z_P_BI_S32 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1RSB_Z_P_BI_S32 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1RSB_Z_P_BI_S16 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let msize := 8
  let is_unsigned : Bool := false
  let offset := (BitVec.toNat imm6)
  match VL with
  | 128 => (execute_LD1RSB_Z_P_BI_S16 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1RSB_Z_P_BI_S16 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1RSB_Z_P_BI_S16 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1RSB_Z_P_BI_S16 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1RSB_Z_P_BI_S16 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1RD_Z_P_BI_U64 (dtypeh : (BitVec 2)) (imm6 : (BitVec 6)) (dtypel : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm6)
  match VL with
  | 128 => (execute_LD1RD_Z_P_BI_U64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1RD_Z_P_BI_U64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1RD_Z_P_BI_U64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1RD_Z_P_BI_U64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1RD_Z_P_BI_U64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1B_Z_P_BR_U8 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 8
  let msize := 8
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LD1B_Z_P_BR_U8 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1B_Z_P_BR_U8 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1B_Z_P_BR_U8 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1B_Z_P_BR_U8 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1B_Z_P_BR_U8 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1B_Z_P_BR_U16 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let msize := 8
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LD1B_Z_P_BR_U16 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1B_Z_P_BR_U16 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1B_Z_P_BR_U16 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1B_Z_P_BR_U16 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1B_Z_P_BR_U16 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1B_Z_P_BR_U32 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LD1B_Z_P_BR_U32 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1B_Z_P_BR_U32 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1B_Z_P_BR_U32 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1B_Z_P_BR_U32 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1B_Z_P_BR_U32 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1B_Z_P_BR_U64 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LD1B_Z_P_BR_U64 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1B_Z_P_BR_U64 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1B_Z_P_BR_U64 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1B_Z_P_BR_U64 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1B_Z_P_BR_U64 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1SW_Z_P_BR_S64 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LD1SW_Z_P_BR_S64 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1SW_Z_P_BR_S64 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1SW_Z_P_BR_S64 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1SW_Z_P_BR_S64 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1SW_Z_P_BR_S64 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1H_Z_P_BR_U16 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let msize := 16
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LD1H_Z_P_BR_U16 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1H_Z_P_BR_U16 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1H_Z_P_BR_U16 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1H_Z_P_BR_U16 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1H_Z_P_BR_U16 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1H_Z_P_BR_U32 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LD1H_Z_P_BR_U32 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1H_Z_P_BR_U32 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1H_Z_P_BR_U32 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1H_Z_P_BR_U32 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1H_Z_P_BR_U32 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1H_Z_P_BR_U64 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LD1H_Z_P_BR_U64 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1H_Z_P_BR_U64 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1H_Z_P_BR_U64 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1H_Z_P_BR_U64 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1H_Z_P_BR_U64 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1SH_Z_P_BR_S64 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LD1SH_Z_P_BR_S64 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1SH_Z_P_BR_S64 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1SH_Z_P_BR_S64 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1SH_Z_P_BR_S64 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1SH_Z_P_BR_S64 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1SH_Z_P_BR_S32 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LD1SH_Z_P_BR_S32 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1SH_Z_P_BR_S32 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1SH_Z_P_BR_S32 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1SH_Z_P_BR_S32 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1SH_Z_P_BR_S32 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1W_Z_P_BR_U32 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 32
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LD1W_Z_P_BR_U32 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1W_Z_P_BR_U32 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1W_Z_P_BR_U32 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1W_Z_P_BR_U32 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1W_Z_P_BR_U32 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1W_Z_P_BR_U64 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LD1W_Z_P_BR_U64 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1W_Z_P_BR_U64 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1W_Z_P_BR_U64 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1W_Z_P_BR_U64 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1W_Z_P_BR_U64 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1SB_Z_P_BR_S64 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LD1SB_Z_P_BR_S64 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1SB_Z_P_BR_S64 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1SB_Z_P_BR_S64 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1SB_Z_P_BR_S64 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1SB_Z_P_BR_S64 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1SB_Z_P_BR_S32 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LD1SB_Z_P_BR_S32 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1SB_Z_P_BR_S32 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1SB_Z_P_BR_S32 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1SB_Z_P_BR_S32 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1SB_Z_P_BR_S32 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1SB_Z_P_BR_S16 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let msize := 8
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LD1SB_Z_P_BR_S16 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1SB_Z_P_BR_S16 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1SB_Z_P_BR_S16 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1SB_Z_P_BR_S16 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1SB_Z_P_BR_S16 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1D_Z_P_BR_U64 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 64
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LD1D_Z_P_BR_U64 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1D_Z_P_BR_U64 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1D_Z_P_BR_U64 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1D_Z_P_BR_U64 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1D_Z_P_BR_U64 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1W_Z_P_BR_U128 (dtype : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let msize := 32
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LD1W_Z_P_BR_U128 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1W_Z_P_BR_U128 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1W_Z_P_BR_U128 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1W_Z_P_BR_U128 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1W_Z_P_BR_U128 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LD1D_Z_P_BR_U128 (dtype : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let msize := 64
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LD1D_Z_P_BR_U128 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LD1D_Z_P_BR_U128 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LD1D_Z_P_BR_U128 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LD1D_Z_P_BR_U128 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LD1D_Z_P_BR_U128 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDFF1B_Z_P_BR_U8 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 8
  let msize := 8
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDFF1B_Z_P_BR_U8 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDFF1B_Z_P_BR_U8 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDFF1B_Z_P_BR_U8 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDFF1B_Z_P_BR_U8 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDFF1B_Z_P_BR_U8 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDFF1B_Z_P_BR_U16 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let msize := 8
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDFF1B_Z_P_BR_U16 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDFF1B_Z_P_BR_U16 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDFF1B_Z_P_BR_U16 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDFF1B_Z_P_BR_U16 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDFF1B_Z_P_BR_U16 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDFF1B_Z_P_BR_U32 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDFF1B_Z_P_BR_U32 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDFF1B_Z_P_BR_U32 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDFF1B_Z_P_BR_U32 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDFF1B_Z_P_BR_U32 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDFF1B_Z_P_BR_U32 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDFF1B_Z_P_BR_U64 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDFF1B_Z_P_BR_U64 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDFF1B_Z_P_BR_U64 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDFF1B_Z_P_BR_U64 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDFF1B_Z_P_BR_U64 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDFF1B_Z_P_BR_U64 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SW_Z_P_BR_S64 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LDFF1SW_Z_P_BR_S64 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDFF1SW_Z_P_BR_S64 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDFF1SW_Z_P_BR_S64 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDFF1SW_Z_P_BR_S64 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDFF1SW_Z_P_BR_S64 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDFF1H_Z_P_BR_U16 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let msize := 16
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDFF1H_Z_P_BR_U16 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDFF1H_Z_P_BR_U16 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDFF1H_Z_P_BR_U16 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDFF1H_Z_P_BR_U16 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDFF1H_Z_P_BR_U16 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDFF1H_Z_P_BR_U32 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDFF1H_Z_P_BR_U32 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDFF1H_Z_P_BR_U32 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDFF1H_Z_P_BR_U32 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDFF1H_Z_P_BR_U32 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDFF1H_Z_P_BR_U32 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDFF1H_Z_P_BR_U64 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDFF1H_Z_P_BR_U64 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDFF1H_Z_P_BR_U64 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDFF1H_Z_P_BR_U64 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDFF1H_Z_P_BR_U64 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDFF1H_Z_P_BR_U64 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SH_Z_P_BR_S64 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LDFF1SH_Z_P_BR_S64 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDFF1SH_Z_P_BR_S64 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDFF1SH_Z_P_BR_S64 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDFF1SH_Z_P_BR_S64 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDFF1SH_Z_P_BR_S64 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SH_Z_P_BR_S32 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LDFF1SH_Z_P_BR_S32 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDFF1SH_Z_P_BR_S32 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDFF1SH_Z_P_BR_S32 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDFF1SH_Z_P_BR_S32 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDFF1SH_Z_P_BR_S32 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDFF1W_Z_P_BR_U32 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 32
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDFF1W_Z_P_BR_U32 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDFF1W_Z_P_BR_U32 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDFF1W_Z_P_BR_U32 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDFF1W_Z_P_BR_U32 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDFF1W_Z_P_BR_U32 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDFF1W_Z_P_BR_U64 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDFF1W_Z_P_BR_U64 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDFF1W_Z_P_BR_U64 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDFF1W_Z_P_BR_U64 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDFF1W_Z_P_BR_U64 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDFF1W_Z_P_BR_U64 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SB_Z_P_BR_S64 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LDFF1SB_Z_P_BR_S64 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDFF1SB_Z_P_BR_S64 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDFF1SB_Z_P_BR_S64 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDFF1SB_Z_P_BR_S64 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDFF1SB_Z_P_BR_S64 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SB_Z_P_BR_S32 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LDFF1SB_Z_P_BR_S32 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDFF1SB_Z_P_BR_S32 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDFF1SB_Z_P_BR_S32 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDFF1SB_Z_P_BR_S32 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDFF1SB_Z_P_BR_S32 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SB_Z_P_BR_S16 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let msize := 8
  let is_unsigned : Bool := false
  match VL with
  | 128 => (execute_LDFF1SB_Z_P_BR_S16 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDFF1SB_Z_P_BR_S16 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDFF1SB_Z_P_BR_S16 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDFF1SB_Z_P_BR_S16 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDFF1SB_Z_P_BR_S16 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDFF1D_Z_P_BR_U64 (dtype : (BitVec 4)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 64
  let is_unsigned : Bool := true
  match VL with
  | 128 => (execute_LDFF1D_Z_P_BR_U64 128 esize g m msize n t is_unsigned)
  | 256 => (execute_LDFF1D_Z_P_BR_U64 256 esize g m msize n t is_unsigned)
  | 512 => (execute_LDFF1D_Z_P_BR_U64 512 esize g m msize n t is_unsigned)
  | 1024 => (execute_LDFF1D_Z_P_BR_U64 1024 esize g m msize n t is_unsigned)
  | 2048 => (execute_LDFF1D_Z_P_BR_U64 2048 esize g m msize n t is_unsigned)
  | _ => (pure ())

def decode_LDNT1B_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 8
  match VL with
  | 128 => (execute_LDNT1B_Z_P_BR_Contiguous 128 esize g m n t)
  | 256 => (execute_LDNT1B_Z_P_BR_Contiguous 256 esize g m n t)
  | 512 => (execute_LDNT1B_Z_P_BR_Contiguous 512 esize g m n t)
  | 1024 => (execute_LDNT1B_Z_P_BR_Contiguous 1024 esize g m n t)
  | 2048 => (execute_LDNT1B_Z_P_BR_Contiguous 2048 esize g m n t)
  | _ => (pure ())

def decode_LDNT1H_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 16
  match VL with
  | 128 => (execute_LDNT1H_Z_P_BR_Contiguous 128 esize g m n t)
  | 256 => (execute_LDNT1H_Z_P_BR_Contiguous 256 esize g m n t)
  | 512 => (execute_LDNT1H_Z_P_BR_Contiguous 512 esize g m n t)
  | 1024 => (execute_LDNT1H_Z_P_BR_Contiguous 1024 esize g m n t)
  | 2048 => (execute_LDNT1H_Z_P_BR_Contiguous 2048 esize g m n t)
  | _ => (pure ())

def decode_LDNT1W_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  match VL with
  | 128 => (execute_LDNT1W_Z_P_BR_Contiguous 128 esize g m n t)
  | 256 => (execute_LDNT1W_Z_P_BR_Contiguous 256 esize g m n t)
  | 512 => (execute_LDNT1W_Z_P_BR_Contiguous 512 esize g m n t)
  | 1024 => (execute_LDNT1W_Z_P_BR_Contiguous 1024 esize g m n t)
  | 2048 => (execute_LDNT1W_Z_P_BR_Contiguous 2048 esize g m n t)
  | _ => (pure ())

def decode_LDNT1D_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  match VL with
  | 128 => (execute_LDNT1D_Z_P_BR_Contiguous 128 esize g m n t)
  | 256 => (execute_LDNT1D_Z_P_BR_Contiguous 256 esize g m n t)
  | 512 => (execute_LDNT1D_Z_P_BR_Contiguous 512 esize g m n t)
  | 1024 => (execute_LDNT1D_Z_P_BR_Contiguous 1024 esize g m n t)
  | 2048 => (execute_LDNT1D_Z_P_BR_Contiguous 2048 esize g m n t)
  | _ => (pure ())

def decode_LD2B_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 8
  let nreg := 2
  match VL with
  | 128 => (execute_LD2B_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_LD2B_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_LD2B_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_LD2B_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_LD2B_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD2H_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let nreg := 2
  match VL with
  | 128 => (execute_LD2H_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_LD2H_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_LD2H_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_LD2H_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_LD2H_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD2W_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let nreg := 2
  match VL with
  | 128 => (execute_LD2W_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_LD2W_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_LD2W_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_LD2W_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_LD2W_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD2D_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let nreg := 2
  match VL with
  | 128 => (execute_LD2D_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_LD2D_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_LD2D_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_LD2D_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_LD2D_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD3B_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 8
  let nreg := 3
  match VL with
  | 128 => (execute_LD3B_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_LD3B_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_LD3B_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_LD3B_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_LD3B_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD3H_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let nreg := 3
  match VL with
  | 128 => (execute_LD3H_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_LD3H_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_LD3H_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_LD3H_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_LD3H_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD3W_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let nreg := 3
  match VL with
  | 128 => (execute_LD3W_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_LD3W_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_LD3W_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_LD3W_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_LD3W_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD3D_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let nreg := 3
  match VL with
  | 128 => (execute_LD3D_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_LD3D_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_LD3D_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_LD3D_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_LD3D_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD4B_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 8
  let nreg := 4
  match VL with
  | 128 => (execute_LD4B_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_LD4B_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_LD4B_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_LD4B_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_LD4B_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD4H_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let nreg := 4
  match VL with
  | 128 => (execute_LD4H_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_LD4H_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_LD4H_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_LD4H_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_LD4H_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD4W_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let nreg := 4
  match VL with
  | 128 => (execute_LD4W_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_LD4W_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_LD4W_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_LD4W_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_LD4W_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD4D_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let nreg := 4
  match VL with
  | 128 => (execute_LD4D_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_LD4D_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_LD4D_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_LD4D_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_LD4D_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD2Q_Z_P_BR_Contiguous (num : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let nreg := 2
  match VL with
  | 128 => (execute_LD2Q_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_LD2Q_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_LD2Q_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_LD2Q_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_LD2Q_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD3Q_Z_P_BR_Contiguous (num : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let nreg := 3
  match VL with
  | 128 => (execute_LD3Q_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_LD3Q_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_LD3Q_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_LD3Q_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_LD3Q_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD4Q_Z_P_BR_Contiguous (num : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let nreg := 4
  match VL with
  | 128 => (execute_LD4Q_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_LD4Q_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_LD4Q_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_LD4Q_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_LD4Q_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_LD1RQB_Z_P_BR_Contiguous (msz : (BitVec 2)) (ssz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 8
  match VL with
  | 128 => (execute_LD1RQB_Z_P_BR_Contiguous 128 esize g m n t)
  | 256 => (execute_LD1RQB_Z_P_BR_Contiguous 256 esize g m n t)
  | 512 => (execute_LD1RQB_Z_P_BR_Contiguous 512 esize g m n t)
  | 1024 => (execute_LD1RQB_Z_P_BR_Contiguous 1024 esize g m n t)
  | 2048 => (execute_LD1RQB_Z_P_BR_Contiguous 2048 esize g m n t)
  | _ => (pure ())

def decode_LD1RQH_Z_P_BR_Contiguous (msz : (BitVec 2)) (ssz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 16
  match VL with
  | 128 => (execute_LD1RQH_Z_P_BR_Contiguous 128 esize g m n t)
  | 256 => (execute_LD1RQH_Z_P_BR_Contiguous 256 esize g m n t)
  | 512 => (execute_LD1RQH_Z_P_BR_Contiguous 512 esize g m n t)
  | 1024 => (execute_LD1RQH_Z_P_BR_Contiguous 1024 esize g m n t)
  | 2048 => (execute_LD1RQH_Z_P_BR_Contiguous 2048 esize g m n t)
  | _ => (pure ())

def decode_LD1RQW_Z_P_BR_Contiguous (msz : (BitVec 2)) (ssz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  match VL with
  | 128 => (execute_LD1RQW_Z_P_BR_Contiguous 128 esize g m n t)
  | 256 => (execute_LD1RQW_Z_P_BR_Contiguous 256 esize g m n t)
  | 512 => (execute_LD1RQW_Z_P_BR_Contiguous 512 esize g m n t)
  | 1024 => (execute_LD1RQW_Z_P_BR_Contiguous 1024 esize g m n t)
  | 2048 => (execute_LD1RQW_Z_P_BR_Contiguous 2048 esize g m n t)
  | _ => (pure ())

def decode_LD1RQD_Z_P_BR_Contiguous (msz : (BitVec 2)) (ssz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  match VL with
  | 128 => (execute_LD1RQD_Z_P_BR_Contiguous 128 esize g m n t)
  | 256 => (execute_LD1RQD_Z_P_BR_Contiguous 256 esize g m n t)
  | 512 => (execute_LD1RQD_Z_P_BR_Contiguous 512 esize g m n t)
  | 1024 => (execute_LD1RQD_Z_P_BR_Contiguous 1024 esize g m n t)
  | 2048 => (execute_LD1RQD_Z_P_BR_Contiguous 2048 esize g m n t)
  | _ => (pure ())

def decode_LD1ROB_Z_P_BR_Contiguous (msz : (BitVec 2)) (ssz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVEFP64MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 8
  match VL with
  | 128 => (execute_LD1ROB_Z_P_BR_Contiguous 128 esize g m n t)
  | 256 => (execute_LD1ROB_Z_P_BR_Contiguous 256 esize g m n t)
  | 512 => (execute_LD1ROB_Z_P_BR_Contiguous 512 esize g m n t)
  | 1024 => (execute_LD1ROB_Z_P_BR_Contiguous 1024 esize g m n t)
  | 2048 => (execute_LD1ROB_Z_P_BR_Contiguous 2048 esize g m n t)
  | _ => (pure ())

def decode_LD1ROH_Z_P_BR_Contiguous (msz : (BitVec 2)) (ssz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVEFP64MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 16
  match VL with
  | 128 => (execute_LD1ROH_Z_P_BR_Contiguous 128 esize g m n t)
  | 256 => (execute_LD1ROH_Z_P_BR_Contiguous 256 esize g m n t)
  | 512 => (execute_LD1ROH_Z_P_BR_Contiguous 512 esize g m n t)
  | 1024 => (execute_LD1ROH_Z_P_BR_Contiguous 1024 esize g m n t)
  | 2048 => (execute_LD1ROH_Z_P_BR_Contiguous 2048 esize g m n t)
  | _ => (pure ())

def decode_LD1ROW_Z_P_BR_Contiguous (msz : (BitVec 2)) (ssz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVEFP64MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  match VL with
  | 128 => (execute_LD1ROW_Z_P_BR_Contiguous 128 esize g m n t)
  | 256 => (execute_LD1ROW_Z_P_BR_Contiguous 256 esize g m n t)
  | 512 => (execute_LD1ROW_Z_P_BR_Contiguous 512 esize g m n t)
  | 1024 => (execute_LD1ROW_Z_P_BR_Contiguous 1024 esize g m n t)
  | 2048 => (execute_LD1ROW_Z_P_BR_Contiguous 2048 esize g m n t)
  | _ => (pure ())

def decode_LD1ROD_Z_P_BR_Contiguous (msz : (BitVec 2)) (ssz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVEFP64MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  match VL with
  | 128 => (execute_LD1ROD_Z_P_BR_Contiguous 128 esize g m n t)
  | 256 => (execute_LD1ROD_Z_P_BR_Contiguous 256 esize g m n t)
  | 512 => (execute_LD1ROD_Z_P_BR_Contiguous 512 esize g m n t)
  | 1024 => (execute_LD1ROD_Z_P_BR_Contiguous 1024 esize g m n t)
  | 2048 => (execute_LD1ROD_Z_P_BR_Contiguous 2048 esize g m n t)
  | _ => (pure ())

def decode_LD1B_Z_P_BI_U8 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 8
  let msize := 8
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1B_Z_P_BI_U8 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1B_Z_P_BI_U8 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1B_Z_P_BI_U8 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1B_Z_P_BI_U8 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1B_Z_P_BI_U8 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1B_Z_P_BI_U16 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let msize := 8
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1B_Z_P_BI_U16 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1B_Z_P_BI_U16 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1B_Z_P_BI_U16 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1B_Z_P_BI_U16 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1B_Z_P_BI_U16 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1B_Z_P_BI_U32 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1B_Z_P_BI_U32 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1B_Z_P_BI_U32 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1B_Z_P_BI_U32 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1B_Z_P_BI_U32 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1B_Z_P_BI_U32 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1B_Z_P_BI_U64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1B_Z_P_BI_U64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1B_Z_P_BI_U64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1B_Z_P_BI_U64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1B_Z_P_BI_U64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1B_Z_P_BI_U64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1SW_Z_P_BI_S64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let is_unsigned : Bool := false
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1SW_Z_P_BI_S64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1SW_Z_P_BI_S64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1SW_Z_P_BI_S64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1SW_Z_P_BI_S64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1SW_Z_P_BI_S64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1H_Z_P_BI_U16 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let msize := 16
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1H_Z_P_BI_U16 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1H_Z_P_BI_U16 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1H_Z_P_BI_U16 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1H_Z_P_BI_U16 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1H_Z_P_BI_U16 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1H_Z_P_BI_U32 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1H_Z_P_BI_U32 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1H_Z_P_BI_U32 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1H_Z_P_BI_U32 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1H_Z_P_BI_U32 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1H_Z_P_BI_U32 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1H_Z_P_BI_U64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1H_Z_P_BI_U64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1H_Z_P_BI_U64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1H_Z_P_BI_U64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1H_Z_P_BI_U64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1H_Z_P_BI_U64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1SH_Z_P_BI_S64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let is_unsigned : Bool := false
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1SH_Z_P_BI_S64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1SH_Z_P_BI_S64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1SH_Z_P_BI_S64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1SH_Z_P_BI_S64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1SH_Z_P_BI_S64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1SH_Z_P_BI_S32 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let is_unsigned : Bool := false
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1SH_Z_P_BI_S32 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1SH_Z_P_BI_S32 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1SH_Z_P_BI_S32 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1SH_Z_P_BI_S32 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1SH_Z_P_BI_S32 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1W_Z_P_BI_U32 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 32
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1W_Z_P_BI_U32 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1W_Z_P_BI_U32 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1W_Z_P_BI_U32 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1W_Z_P_BI_U32 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1W_Z_P_BI_U32 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1W_Z_P_BI_U64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1W_Z_P_BI_U64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1W_Z_P_BI_U64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1W_Z_P_BI_U64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1W_Z_P_BI_U64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1W_Z_P_BI_U64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1SB_Z_P_BI_S64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let is_unsigned : Bool := false
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1SB_Z_P_BI_S64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1SB_Z_P_BI_S64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1SB_Z_P_BI_S64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1SB_Z_P_BI_S64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1SB_Z_P_BI_S64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1SB_Z_P_BI_S32 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let is_unsigned : Bool := false
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1SB_Z_P_BI_S32 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1SB_Z_P_BI_S32 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1SB_Z_P_BI_S32 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1SB_Z_P_BI_S32 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1SB_Z_P_BI_S32 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1SB_Z_P_BI_S16 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let msize := 8
  let is_unsigned : Bool := false
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1SB_Z_P_BI_S16 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1SB_Z_P_BI_S16 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1SB_Z_P_BI_S16 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1SB_Z_P_BI_S16 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1SB_Z_P_BI_S16 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1D_Z_P_BI_U64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1D_Z_P_BI_U64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1D_Z_P_BI_U64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1D_Z_P_BI_U64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1D_Z_P_BI_U64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1D_Z_P_BI_U64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNF1B_Z_P_BI_U8 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 8
  let msize := 8
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNF1B_Z_P_BI_U8 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDNF1B_Z_P_BI_U8 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDNF1B_Z_P_BI_U8 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDNF1B_Z_P_BI_U8 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDNF1B_Z_P_BI_U8 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNF1B_Z_P_BI_U16 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let msize := 8
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNF1B_Z_P_BI_U16 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDNF1B_Z_P_BI_U16 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDNF1B_Z_P_BI_U16 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDNF1B_Z_P_BI_U16 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDNF1B_Z_P_BI_U16 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNF1B_Z_P_BI_U32 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNF1B_Z_P_BI_U32 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDNF1B_Z_P_BI_U32 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDNF1B_Z_P_BI_U32 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDNF1B_Z_P_BI_U32 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDNF1B_Z_P_BI_U32 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNF1B_Z_P_BI_U64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNF1B_Z_P_BI_U64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDNF1B_Z_P_BI_U64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDNF1B_Z_P_BI_U64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDNF1B_Z_P_BI_U64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDNF1B_Z_P_BI_U64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNF1SW_Z_P_BI_S64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let is_unsigned : Bool := false
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNF1SW_Z_P_BI_S64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDNF1SW_Z_P_BI_S64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDNF1SW_Z_P_BI_S64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDNF1SW_Z_P_BI_S64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDNF1SW_Z_P_BI_S64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNF1H_Z_P_BI_U16 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let msize := 16
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNF1H_Z_P_BI_U16 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDNF1H_Z_P_BI_U16 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDNF1H_Z_P_BI_U16 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDNF1H_Z_P_BI_U16 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDNF1H_Z_P_BI_U16 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNF1H_Z_P_BI_U32 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNF1H_Z_P_BI_U32 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDNF1H_Z_P_BI_U32 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDNF1H_Z_P_BI_U32 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDNF1H_Z_P_BI_U32 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDNF1H_Z_P_BI_U32 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNF1H_Z_P_BI_U64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNF1H_Z_P_BI_U64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDNF1H_Z_P_BI_U64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDNF1H_Z_P_BI_U64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDNF1H_Z_P_BI_U64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDNF1H_Z_P_BI_U64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNF1SH_Z_P_BI_S64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let is_unsigned : Bool := false
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNF1SH_Z_P_BI_S64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDNF1SH_Z_P_BI_S64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDNF1SH_Z_P_BI_S64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDNF1SH_Z_P_BI_S64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDNF1SH_Z_P_BI_S64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNF1SH_Z_P_BI_S32 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let is_unsigned : Bool := false
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNF1SH_Z_P_BI_S32 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDNF1SH_Z_P_BI_S32 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDNF1SH_Z_P_BI_S32 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDNF1SH_Z_P_BI_S32 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDNF1SH_Z_P_BI_S32 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNF1W_Z_P_BI_U32 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 32
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNF1W_Z_P_BI_U32 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDNF1W_Z_P_BI_U32 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDNF1W_Z_P_BI_U32 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDNF1W_Z_P_BI_U32 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDNF1W_Z_P_BI_U32 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNF1W_Z_P_BI_U64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNF1W_Z_P_BI_U64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDNF1W_Z_P_BI_U64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDNF1W_Z_P_BI_U64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDNF1W_Z_P_BI_U64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDNF1W_Z_P_BI_U64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNF1SB_Z_P_BI_S64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let is_unsigned : Bool := false
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNF1SB_Z_P_BI_S64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDNF1SB_Z_P_BI_S64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDNF1SB_Z_P_BI_S64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDNF1SB_Z_P_BI_S64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDNF1SB_Z_P_BI_S64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNF1SB_Z_P_BI_S32 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let is_unsigned : Bool := false
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNF1SB_Z_P_BI_S32 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDNF1SB_Z_P_BI_S32 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDNF1SB_Z_P_BI_S32 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDNF1SB_Z_P_BI_S32 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDNF1SB_Z_P_BI_S32 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNF1SB_Z_P_BI_S16 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let msize := 8
  let is_unsigned : Bool := false
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNF1SB_Z_P_BI_S16 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDNF1SB_Z_P_BI_S16 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDNF1SB_Z_P_BI_S16 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDNF1SB_Z_P_BI_S16 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDNF1SB_Z_P_BI_S16 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNF1D_Z_P_BI_U64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 64
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LDNF1D_Z_P_BI_U64 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDNF1D_Z_P_BI_U64 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDNF1D_Z_P_BI_U64 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDNF1D_Z_P_BI_U64 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDNF1D_Z_P_BI_U64 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1W_Z_P_BI_U128 (dtype : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let msize := 32
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1W_Z_P_BI_U128 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1W_Z_P_BI_U128 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1W_Z_P_BI_U128 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1W_Z_P_BI_U128 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1W_Z_P_BI_U128 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1D_Z_P_BI_U128 (dtype : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let msize := 64
  let is_unsigned : Bool := true
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1D_Z_P_BI_U128 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1D_Z_P_BI_U128 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1D_Z_P_BI_U128 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1D_Z_P_BI_U128 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1D_Z_P_BI_U128 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDNT1B_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LDNT1B_Z_P_BI_Contiguous 128 esize g n offset t)
  | 256 => (execute_LDNT1B_Z_P_BI_Contiguous 256 esize g n offset t)
  | 512 => (execute_LDNT1B_Z_P_BI_Contiguous 512 esize g n offset t)
  | 1024 => (execute_LDNT1B_Z_P_BI_Contiguous 1024 esize g n offset t)
  | 2048 => (execute_LDNT1B_Z_P_BI_Contiguous 2048 esize g n offset t)
  | _ => (pure ())

def decode_LDNT1H_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LDNT1H_Z_P_BI_Contiguous 128 esize g n offset t)
  | 256 => (execute_LDNT1H_Z_P_BI_Contiguous 256 esize g n offset t)
  | 512 => (execute_LDNT1H_Z_P_BI_Contiguous 512 esize g n offset t)
  | 1024 => (execute_LDNT1H_Z_P_BI_Contiguous 1024 esize g n offset t)
  | 2048 => (execute_LDNT1H_Z_P_BI_Contiguous 2048 esize g n offset t)
  | _ => (pure ())

def decode_LDNT1W_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LDNT1W_Z_P_BI_Contiguous 128 esize g n offset t)
  | 256 => (execute_LDNT1W_Z_P_BI_Contiguous 256 esize g n offset t)
  | 512 => (execute_LDNT1W_Z_P_BI_Contiguous 512 esize g n offset t)
  | 1024 => (execute_LDNT1W_Z_P_BI_Contiguous 1024 esize g n offset t)
  | 2048 => (execute_LDNT1W_Z_P_BI_Contiguous 2048 esize g n offset t)
  | _ => (pure ())

def decode_LDNT1D_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LDNT1D_Z_P_BI_Contiguous 128 esize g n offset t)
  | 256 => (execute_LDNT1D_Z_P_BI_Contiguous 256 esize g n offset t)
  | 512 => (execute_LDNT1D_Z_P_BI_Contiguous 512 esize g n offset t)
  | 1024 => (execute_LDNT1D_Z_P_BI_Contiguous 1024 esize g n offset t)
  | 2048 => (execute_LDNT1D_Z_P_BI_Contiguous 2048 esize g n offset t)
  | _ => (pure ())

def decode_LD2B_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD2B_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_LD2B_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_LD2B_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_LD2B_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_LD2B_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD2H_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD2H_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_LD2H_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_LD2H_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_LD2H_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_LD2H_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD2W_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD2W_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_LD2W_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_LD2W_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_LD2W_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_LD2W_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD2D_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD2D_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_LD2D_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_LD2D_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_LD2D_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_LD2D_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD3B_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD3B_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_LD3B_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_LD3B_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_LD3B_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_LD3B_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD3H_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD3H_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_LD3H_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_LD3H_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_LD3H_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_LD3H_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD3W_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD3W_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_LD3W_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_LD3W_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_LD3W_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_LD3W_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD3D_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD3D_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_LD3D_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_LD3D_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_LD3D_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_LD3D_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD4B_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD4B_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_LD4B_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_LD4B_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_LD4B_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_LD4B_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD4H_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD4H_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_LD4H_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_LD4H_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_LD4H_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_LD4H_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD4W_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD4W_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_LD4W_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_LD4W_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_LD4W_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_LD4W_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD4D_Z_P_BI_Contiguous (msz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD4D_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_LD4D_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_LD4D_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_LD4D_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_LD4D_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD2Q_Z_P_BI_Contiguous (num : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD2Q_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_LD2Q_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_LD2Q_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_LD2Q_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_LD2Q_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD3Q_Z_P_BI_Contiguous (num : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD3Q_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_LD3Q_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_LD3Q_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_LD3Q_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_LD3Q_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD4Q_Z_P_BI_Contiguous (num : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD4Q_Z_P_BI_Contiguous 128 esize g n nreg offset t)
  | 256 => (execute_LD4Q_Z_P_BI_Contiguous 256 esize g n nreg offset t)
  | 512 => (execute_LD4Q_Z_P_BI_Contiguous 512 esize g n nreg offset t)
  | 1024 => (execute_LD4Q_Z_P_BI_Contiguous 1024 esize g n nreg offset t)
  | 2048 => (execute_LD4Q_Z_P_BI_Contiguous 2048 esize g n nreg offset t)
  | _ => (pure ())

def decode_LD1RQB_Z_P_BI_U8 (msz : (BitVec 2)) (ssz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD1RQB_Z_P_BI_U8 128 esize g n offset t)
  | 256 => (execute_LD1RQB_Z_P_BI_U8 256 esize g n offset t)
  | 512 => (execute_LD1RQB_Z_P_BI_U8 512 esize g n offset t)
  | 1024 => (execute_LD1RQB_Z_P_BI_U8 1024 esize g n offset t)
  | 2048 => (execute_LD1RQB_Z_P_BI_U8 2048 esize g n offset t)
  | _ => (pure ())

def decode_LD1RQH_Z_P_BI_U16 (msz : (BitVec 2)) (ssz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD1RQH_Z_P_BI_U16 128 esize g n offset t)
  | 256 => (execute_LD1RQH_Z_P_BI_U16 256 esize g n offset t)
  | 512 => (execute_LD1RQH_Z_P_BI_U16 512 esize g n offset t)
  | 1024 => (execute_LD1RQH_Z_P_BI_U16 1024 esize g n offset t)
  | 2048 => (execute_LD1RQH_Z_P_BI_U16 2048 esize g n offset t)
  | _ => (pure ())

def decode_LD1RQW_Z_P_BI_U32 (msz : (BitVec 2)) (ssz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD1RQW_Z_P_BI_U32 128 esize g n offset t)
  | 256 => (execute_LD1RQW_Z_P_BI_U32 256 esize g n offset t)
  | 512 => (execute_LD1RQW_Z_P_BI_U32 512 esize g n offset t)
  | 1024 => (execute_LD1RQW_Z_P_BI_U32 1024 esize g n offset t)
  | 2048 => (execute_LD1RQW_Z_P_BI_U32 2048 esize g n offset t)
  | _ => (pure ())

def decode_LD1RQD_Z_P_BI_U64 (msz : (BitVec 2)) (ssz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  | 128 => (execute_LD1RQD_Z_P_BI_U64 128 esize g n offset t)
  | 256 => (execute_LD1RQD_Z_P_BI_U64 256 esize g n offset t)
  | 512 => (execute_LD1RQD_Z_P_BI_U64 512 esize g n offset t)
  | 1024 => (execute_LD1RQD_Z_P_BI_U64 1024 esize g n offset t)
  | 2048 => (execute_LD1RQD_Z_P_BI_U64 2048 esize g n offset t)
  | _ => (pure ())

def decode_LD1ROB_Z_P_BI_U8 (msz : (BitVec 2)) (ssz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVEFP64MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 8
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1ROB_Z_P_BI_U8 128 esize g n offset t)
  | 256 => (execute_LD1ROB_Z_P_BI_U8 256 esize g n offset t)
  | 512 => (execute_LD1ROB_Z_P_BI_U8 512 esize g n offset t)
  | 1024 => (execute_LD1ROB_Z_P_BI_U8 1024 esize g n offset t)
  | 2048 => (execute_LD1ROB_Z_P_BI_U8 2048 esize g n offset t)
  | _ => (pure ())

def decode_LD1ROH_Z_P_BI_U16 (msz : (BitVec 2)) (ssz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVEFP64MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1ROH_Z_P_BI_U16 128 esize g n offset t)
  | 256 => (execute_LD1ROH_Z_P_BI_U16 256 esize g n offset t)
  | 512 => (execute_LD1ROH_Z_P_BI_U16 512 esize g n offset t)
  | 1024 => (execute_LD1ROH_Z_P_BI_U16 1024 esize g n offset t)
  | 2048 => (execute_LD1ROH_Z_P_BI_U16 2048 esize g n offset t)
  | _ => (pure ())

def decode_LD1ROW_Z_P_BI_U32 (msz : (BitVec 2)) (ssz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVEFP64MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1ROW_Z_P_BI_U32 128 esize g n offset t)
  | 256 => (execute_LD1ROW_Z_P_BI_U32 256 esize g n offset t)
  | 512 => (execute_LD1ROW_Z_P_BI_U32 512 esize g n offset t)
  | 1024 => (execute_LD1ROW_Z_P_BI_U32 1024 esize g n offset t)
  | 2048 => (execute_LD1ROW_Z_P_BI_U32 2048 esize g n offset t)
  | _ => (pure ())

def decode_LD1ROD_Z_P_BI_U64 (msz : (BitVec 2)) (ssz : (BitVec 2)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <||> (do
       (pure (! (← (HaveSVEFP64MatMulExt ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let offset := (BitVec.toInt imm4)
  match VL with
  | 128 => (execute_LD1ROD_Z_P_BI_U64 128 esize g n offset t)
  | 256 => (execute_LD1ROD_Z_P_BI_U64 256 esize g n offset t)
  | 512 => (execute_LD1ROD_Z_P_BI_U64 512 esize g n offset t)
  | 1024 => (execute_LD1ROD_Z_P_BI_U64 1024 esize g n offset t)
  | 2048 => (execute_LD1ROD_Z_P_BI_U64 2048 esize g n offset t)
  | _ => (pure ())

def decode_LD1B_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LD1B_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1B_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1B_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1B_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1B_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1SB_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let offs_size := 32
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LD1SB_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1SB_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1SB_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1SB_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1SB_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1B_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1B_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1B_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1B_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1B_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1B_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SB_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let offs_size := 32
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1SB_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1SB_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1SB_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1SB_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1SB_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1H_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LD1H_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1H_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1H_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1H_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1H_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1SH_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 32
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LD1SH_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1SH_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1SH_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1SH_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1SH_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1H_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1H_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1H_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1H_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1H_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1H_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SH_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 32
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1SH_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1SH_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1SH_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1SH_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1SH_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1W_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LD1W_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1W_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1W_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1W_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1W_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1SW_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 32
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LD1SW_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1SW_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1SW_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1SW_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1SW_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1W_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1W_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1W_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1W_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1W_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1W_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SW_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 32
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1SW_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1SW_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1SW_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1SW_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1SW_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1D_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LD1D_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1D_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1D_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1D_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1D_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1D_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1D_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1D_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1D_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1D_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1D_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_PRFB_I_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_PRFB_I_P_BZ_D_x32_scaled 128 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 256 => (execute_PRFB_I_P_BZ_D_x32_scaled 256 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 512 => (execute_PRFB_I_P_BZ_D_x32_scaled 512 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 1024 => (execute_PRFB_I_P_BZ_D_x32_scaled 1024 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 2048 => (execute_PRFB_I_P_BZ_D_x32_scaled 2048 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | _ => (pure ())

def decode_PRFH_I_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 1
  match VL with
  | 128 => (execute_PRFH_I_P_BZ_D_x32_scaled 128 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 256 => (execute_PRFH_I_P_BZ_D_x32_scaled 256 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 512 => (execute_PRFH_I_P_BZ_D_x32_scaled 512 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 1024 => (execute_PRFH_I_P_BZ_D_x32_scaled 1024 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 2048 => (execute_PRFH_I_P_BZ_D_x32_scaled 2048 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | _ => (pure ())

def decode_PRFW_I_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 2
  match VL with
  | 128 => (execute_PRFW_I_P_BZ_D_x32_scaled 128 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 256 => (execute_PRFW_I_P_BZ_D_x32_scaled 256 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 512 => (execute_PRFW_I_P_BZ_D_x32_scaled 512 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 1024 => (execute_PRFW_I_P_BZ_D_x32_scaled 1024 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 2048 => (execute_PRFW_I_P_BZ_D_x32_scaled 2048 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | _ => (pure ())

def decode_PRFD_I_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 3
  match VL with
  | 128 => (execute_PRFD_I_P_BZ_D_x32_scaled 128 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 256 => (execute_PRFD_I_P_BZ_D_x32_scaled 256 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 512 => (execute_PRFD_I_P_BZ_D_x32_scaled 512 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 1024 => (execute_PRFD_I_P_BZ_D_x32_scaled 1024 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 2048 => (execute_PRFD_I_P_BZ_D_x32_scaled 2048 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | _ => (pure ())

def decode_LD1H_Z_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 1
  match VL with
  | 128 => (execute_LD1H_Z_P_BZ_D_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1H_Z_P_BZ_D_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1H_Z_P_BZ_D_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1H_Z_P_BZ_D_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1H_Z_P_BZ_D_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1SH_Z_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 32
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 1
  match VL with
  | 128 => (execute_LD1SH_Z_P_BZ_D_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1SH_Z_P_BZ_D_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1SH_Z_P_BZ_D_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1SH_Z_P_BZ_D_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1SH_Z_P_BZ_D_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1H_Z_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 1
  match VL with
  | 128 => (execute_LDFF1H_Z_P_BZ_D_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1H_Z_P_BZ_D_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1H_Z_P_BZ_D_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1H_Z_P_BZ_D_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1H_Z_P_BZ_D_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SH_Z_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 32
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 1
  match VL with
  | 128 => (execute_LDFF1SH_Z_P_BZ_D_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1SH_Z_P_BZ_D_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1SH_Z_P_BZ_D_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1SH_Z_P_BZ_D_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1SH_Z_P_BZ_D_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1W_Z_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 2
  match VL with
  | 128 => (execute_LD1W_Z_P_BZ_D_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1W_Z_P_BZ_D_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1W_Z_P_BZ_D_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1W_Z_P_BZ_D_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1W_Z_P_BZ_D_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1SW_Z_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 32
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 2
  match VL with
  | 128 => (execute_LD1SW_Z_P_BZ_D_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1SW_Z_P_BZ_D_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1SW_Z_P_BZ_D_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1SW_Z_P_BZ_D_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1SW_Z_P_BZ_D_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1W_Z_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 2
  match VL with
  | 128 => (execute_LDFF1W_Z_P_BZ_D_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1W_Z_P_BZ_D_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1W_Z_P_BZ_D_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1W_Z_P_BZ_D_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1W_Z_P_BZ_D_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SW_Z_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 32
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 2
  match VL with
  | 128 => (execute_LDFF1SW_Z_P_BZ_D_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1SW_Z_P_BZ_D_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1SW_Z_P_BZ_D_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1SW_Z_P_BZ_D_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1SW_Z_P_BZ_D_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1D_Z_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 3
  match VL with
  | 128 => (execute_LD1D_Z_P_BZ_D_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1D_Z_P_BZ_D_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1D_Z_P_BZ_D_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1D_Z_P_BZ_D_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1D_Z_P_BZ_D_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1D_Z_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let offs_size := 32
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 3
  match VL with
  | 128 => (execute_LDFF1D_Z_P_BZ_D_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1D_Z_P_BZ_D_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1D_Z_P_BZ_D_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1D_Z_P_BZ_D_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1D_Z_P_BZ_D_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_PRFB_I_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale := 0
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_PRFB_I_P_AI_D 128 esize g level n offset pref_hint scale stream)
  | 256 => (execute_PRFB_I_P_AI_D 256 esize g level n offset pref_hint scale stream)
  | 512 => (execute_PRFB_I_P_AI_D 512 esize g level n offset pref_hint scale stream)
  | 1024 => (execute_PRFB_I_P_AI_D 1024 esize g level n offset pref_hint scale stream)
  | 2048 => (execute_PRFB_I_P_AI_D 2048 esize g level n offset pref_hint scale stream)
  | _ => (pure ())

def decode_PRFH_I_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale := 1
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_PRFH_I_P_AI_D 128 esize g level n offset pref_hint scale stream)
  | 256 => (execute_PRFH_I_P_AI_D 256 esize g level n offset pref_hint scale stream)
  | 512 => (execute_PRFH_I_P_AI_D 512 esize g level n offset pref_hint scale stream)
  | 1024 => (execute_PRFH_I_P_AI_D 1024 esize g level n offset pref_hint scale stream)
  | 2048 => (execute_PRFH_I_P_AI_D 2048 esize g level n offset pref_hint scale stream)
  | _ => (pure ())

def decode_PRFW_I_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale := 2
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_PRFW_I_P_AI_D 128 esize g level n offset pref_hint scale stream)
  | 256 => (execute_PRFW_I_P_AI_D 256 esize g level n offset pref_hint scale stream)
  | 512 => (execute_PRFW_I_P_AI_D 512 esize g level n offset pref_hint scale stream)
  | 1024 => (execute_PRFW_I_P_AI_D 1024 esize g level n offset pref_hint scale stream)
  | 2048 => (execute_PRFW_I_P_AI_D 2048 esize g level n offset pref_hint scale stream)
  | _ => (pure ())

def decode_PRFD_I_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Zn)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale := 3
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_PRFD_I_P_AI_D 128 esize g level n offset pref_hint scale stream)
  | 256 => (execute_PRFD_I_P_AI_D 256 esize g level n offset pref_hint scale stream)
  | 512 => (execute_PRFD_I_P_AI_D 512 esize g level n offset pref_hint scale stream)
  | 1024 => (execute_PRFD_I_P_AI_D 1024 esize g level n offset pref_hint scale stream)
  | 2048 => (execute_PRFD_I_P_AI_D 2048 esize g level n offset pref_hint scale stream)
  | _ => (pure ())

def decode_LD1B_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LD1B_Z_P_AI_D 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1B_Z_P_AI_D 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1B_Z_P_AI_D 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1B_Z_P_AI_D 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1B_Z_P_AI_D 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1SB_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let is_unsigned : Bool := false
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LD1SB_Z_P_AI_D 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1SB_Z_P_AI_D 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1SB_Z_P_AI_D 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1SB_Z_P_AI_D 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1SB_Z_P_AI_D 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDFF1B_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LDFF1B_Z_P_AI_D 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDFF1B_Z_P_AI_D 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDFF1B_Z_P_AI_D 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDFF1B_Z_P_AI_D 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDFF1B_Z_P_AI_D 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SB_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let is_unsigned : Bool := false
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LDFF1SB_Z_P_AI_D 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDFF1SB_Z_P_AI_D 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDFF1SB_Z_P_AI_D 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDFF1SB_Z_P_AI_D 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDFF1SB_Z_P_AI_D 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1H_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LD1H_Z_P_AI_D 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1H_Z_P_AI_D 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1H_Z_P_AI_D 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1H_Z_P_AI_D 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1H_Z_P_AI_D 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1SH_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let is_unsigned : Bool := false
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LD1SH_Z_P_AI_D 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1SH_Z_P_AI_D 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1SH_Z_P_AI_D 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1SH_Z_P_AI_D 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1SH_Z_P_AI_D 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDFF1H_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LDFF1H_Z_P_AI_D 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDFF1H_Z_P_AI_D 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDFF1H_Z_P_AI_D 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDFF1H_Z_P_AI_D 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDFF1H_Z_P_AI_D 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SH_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let is_unsigned : Bool := false
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LDFF1SH_Z_P_AI_D 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDFF1SH_Z_P_AI_D 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDFF1SH_Z_P_AI_D 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDFF1SH_Z_P_AI_D 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDFF1SH_Z_P_AI_D 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1W_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LD1W_Z_P_AI_D 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1W_Z_P_AI_D 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1W_Z_P_AI_D 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1W_Z_P_AI_D 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1W_Z_P_AI_D 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1SW_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let is_unsigned : Bool := false
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LD1SW_Z_P_AI_D 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1SW_Z_P_AI_D 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1SW_Z_P_AI_D 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1SW_Z_P_AI_D 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1SW_Z_P_AI_D 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDFF1W_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LDFF1W_Z_P_AI_D 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDFF1W_Z_P_AI_D 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDFF1W_Z_P_AI_D 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDFF1W_Z_P_AI_D 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDFF1W_Z_P_AI_D 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SW_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let is_unsigned : Bool := false
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LDFF1SW_Z_P_AI_D 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDFF1SW_Z_P_AI_D 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDFF1SW_Z_P_AI_D 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDFF1SW_Z_P_AI_D 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDFF1SW_Z_P_AI_D 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1D_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 64
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LD1D_Z_P_AI_D 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LD1D_Z_P_AI_D 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LD1D_Z_P_AI_D 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LD1D_Z_P_AI_D 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LD1D_Z_P_AI_D 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LDFF1D_Z_P_AI_D (msz : (BitVec 2)) (imm5 : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Zn)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 64
  let is_unsigned : Bool := true
  let offset := (BitVec.toNat imm5)
  match VL with
  | 128 => (execute_LDFF1D_Z_P_AI_D 128 esize g msize n offset t is_unsigned)
  | 256 => (execute_LDFF1D_Z_P_AI_D 256 esize g msize n offset t is_unsigned)
  | 512 => (execute_LDFF1D_Z_P_AI_D 512 esize g msize n offset t is_unsigned)
  | 1024 => (execute_LDFF1D_Z_P_AI_D 1024 esize g msize n offset t is_unsigned)
  | 2048 => (execute_LDFF1D_Z_P_AI_D 2048 esize g msize n offset t is_unsigned)
  | _ => (pure ())

def decode_LD1B_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let offs_size := 64
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_LD1B_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1B_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1B_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1B_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1B_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1SB_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let offs_size := 64
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_LD1SB_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1SB_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1SB_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1SB_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1SB_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1B_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let offs_size := 64
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1B_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1B_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1B_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1B_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1B_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SB_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let offs_size := 64
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1SB_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1SB_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1SB_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1SB_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1SB_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1H_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 64
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_LD1H_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1H_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1H_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1H_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1H_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1SH_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 64
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_LD1SH_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1SH_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1SH_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1SH_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1SH_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1H_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 64
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1H_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1H_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1H_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1H_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1H_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SH_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 64
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1SH_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1SH_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1SH_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1SH_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1SH_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1W_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 64
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_LD1W_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1W_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1W_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1W_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1W_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1SW_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 64
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_LD1SW_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1SW_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1SW_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1SW_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1SW_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1W_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 64
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1W_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1W_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1W_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1W_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1W_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SW_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 64
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1SW_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1SW_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1SW_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1SW_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1SW_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1D_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_LD1D_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1D_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1D_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1D_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1D_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1D_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_LDFF1D_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1D_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1D_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1D_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1D_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_PRFB_I_P_BZ_D_64_scaled (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size := 64
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_PRFB_I_P_BZ_D_64_scaled 128 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 256 => (execute_PRFB_I_P_BZ_D_64_scaled 256 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 512 => (execute_PRFB_I_P_BZ_D_64_scaled 512 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 1024 => (execute_PRFB_I_P_BZ_D_64_scaled 1024 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 2048 => (execute_PRFB_I_P_BZ_D_64_scaled 2048 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | _ => (pure ())

def decode_PRFH_I_P_BZ_D_64_scaled (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size := 64
  let offs_unsigned : Bool := true
  let scale := 1
  match VL with
  | 128 => (execute_PRFH_I_P_BZ_D_64_scaled 128 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 256 => (execute_PRFH_I_P_BZ_D_64_scaled 256 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 512 => (execute_PRFH_I_P_BZ_D_64_scaled 512 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 1024 => (execute_PRFH_I_P_BZ_D_64_scaled 1024 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 2048 => (execute_PRFH_I_P_BZ_D_64_scaled 2048 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | _ => (pure ())

def decode_PRFW_I_P_BZ_D_64_scaled (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size := 64
  let offs_unsigned : Bool := true
  let scale := 2
  match VL with
  | 128 => (execute_PRFW_I_P_BZ_D_64_scaled 128 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 256 => (execute_PRFW_I_P_BZ_D_64_scaled 256 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 512 => (execute_PRFW_I_P_BZ_D_64_scaled 512 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 1024 => (execute_PRFW_I_P_BZ_D_64_scaled 1024 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 2048 => (execute_PRFW_I_P_BZ_D_64_scaled 2048 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | _ => (pure ())

def decode_PRFD_I_P_BZ_D_64_scaled (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let esize := 64
  let g := (BitVec.toNat Pg)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let level := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.join1 [(BitVec.access prfop 0)]) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.join1 [(BitVec.access prfop 3)]) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size := 64
  let offs_unsigned : Bool := true
  let scale := 3
  match VL with
  | 128 => (execute_PRFD_I_P_BZ_D_64_scaled 128 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 256 => (execute_PRFD_I_P_BZ_D_64_scaled 256 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 512 => (execute_PRFD_I_P_BZ_D_64_scaled 512 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 1024 => (execute_PRFD_I_P_BZ_D_64_scaled 1024 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | 2048 => (execute_PRFD_I_P_BZ_D_64_scaled 2048 esize g level m n offs_size offs_unsigned pref_hint scale stream)
  | _ => (pure ())

def decode_LD1H_Z_P_BZ_D_64_scaled (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 64
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := true
  let scale := 1
  match VL with
  | 128 => (execute_LD1H_Z_P_BZ_D_64_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1H_Z_P_BZ_D_64_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1H_Z_P_BZ_D_64_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1H_Z_P_BZ_D_64_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1H_Z_P_BZ_D_64_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1SH_Z_P_BZ_D_64_scaled (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 64
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := true
  let scale := 1
  match VL with
  | 128 => (execute_LD1SH_Z_P_BZ_D_64_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1SH_Z_P_BZ_D_64_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1SH_Z_P_BZ_D_64_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1SH_Z_P_BZ_D_64_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1SH_Z_P_BZ_D_64_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1H_Z_P_BZ_D_64_scaled (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 64
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := true
  let scale := 1
  match VL with
  | 128 => (execute_LDFF1H_Z_P_BZ_D_64_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1H_Z_P_BZ_D_64_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1H_Z_P_BZ_D_64_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1H_Z_P_BZ_D_64_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1H_Z_P_BZ_D_64_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SH_Z_P_BZ_D_64_scaled (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 64
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := true
  let scale := 1
  match VL with
  | 128 => (execute_LDFF1SH_Z_P_BZ_D_64_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1SH_Z_P_BZ_D_64_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1SH_Z_P_BZ_D_64_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1SH_Z_P_BZ_D_64_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1SH_Z_P_BZ_D_64_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1W_Z_P_BZ_D_64_scaled (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 64
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := true
  let scale := 2
  match VL with
  | 128 => (execute_LD1W_Z_P_BZ_D_64_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1W_Z_P_BZ_D_64_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1W_Z_P_BZ_D_64_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1W_Z_P_BZ_D_64_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1W_Z_P_BZ_D_64_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1SW_Z_P_BZ_D_64_scaled (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 64
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := true
  let scale := 2
  match VL with
  | 128 => (execute_LD1SW_Z_P_BZ_D_64_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1SW_Z_P_BZ_D_64_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1SW_Z_P_BZ_D_64_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1SW_Z_P_BZ_D_64_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1SW_Z_P_BZ_D_64_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1W_Z_P_BZ_D_64_scaled (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 64
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := true
  let scale := 2
  match VL with
  | 128 => (execute_LDFF1W_Z_P_BZ_D_64_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1W_Z_P_BZ_D_64_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1W_Z_P_BZ_D_64_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1W_Z_P_BZ_D_64_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1W_Z_P_BZ_D_64_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1SW_Z_P_BZ_D_64_scaled (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 64
  let is_unsigned : Bool := false
  let offs_unsigned : Bool := true
  let scale := 2
  match VL with
  | 128 => (execute_LDFF1SW_Z_P_BZ_D_64_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1SW_Z_P_BZ_D_64_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1SW_Z_P_BZ_D_64_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1SW_Z_P_BZ_D_64_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1SW_Z_P_BZ_D_64_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LD1D_Z_P_BZ_D_64_scaled (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := true
  let scale := 3
  match VL with
  | 128 => (execute_LD1D_Z_P_BZ_D_64_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LD1D_Z_P_BZ_D_64_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LD1D_Z_P_BZ_D_64_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LD1D_Z_P_BZ_D_64_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LD1D_Z_P_BZ_D_64_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_LDFF1D_Z_P_BZ_D_64_scaled (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let is_unsigned : Bool := true
  let offs_unsigned : Bool := true
  let scale := 3
  match VL with
  | 128 => (execute_LDFF1D_Z_P_BZ_D_64_scaled 128 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 256 => (execute_LDFF1D_Z_P_BZ_D_64_scaled 256 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 512 => (execute_LDFF1D_Z_P_BZ_D_64_scaled 512 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 1024 => (execute_LDFF1D_Z_P_BZ_D_64_scaled 1024 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | 2048 => (execute_LDFF1D_Z_P_BZ_D_64_scaled 2048 esize g m msize n offs_size offs_unsigned scale t is_unsigned)
  | _ => (pure ())

def decode_ST1B_Z_P_BR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let msize := 8
  match VL with
  | 128 => (execute_ST1B_Z_P_BR__ 128 esize g m msize n t)
  | 256 => (execute_ST1B_Z_P_BR__ 256 esize g m msize n t)
  | 512 => (execute_ST1B_Z_P_BR__ 512 esize g m msize n t)
  | 1024 => (execute_ST1B_Z_P_BR__ 1024 esize g m msize n t)
  | 2048 => (execute_ST1B_Z_P_BR__ 2048 esize g m msize n t)
  | _ => (pure ())

def decode_ST1H_Z_P_BR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((size == 0b00#2) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := (Int.shiftl 8 (BitVec.toNat size))
  let msize := 16
  match VL with
  | 128 => (execute_ST1H_Z_P_BR__ 128 esize g m msize n t)
  | 256 => (execute_ST1H_Z_P_BR__ 256 esize g m msize n t)
  | 512 => (execute_ST1H_Z_P_BR__ 512 esize g m msize n t)
  | 1024 => (execute_ST1H_Z_P_BR__ 1024 esize g m msize n t)
  | 2048 => (execute_ST1H_Z_P_BR__ 2048 esize g m msize n t)
  | _ => (pure ())

def decode_ST1W_Z_P_BR__ (sz : (BitVec 1)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := (Int.shiftl 32 (BitVec.toNat sz))
  let msize := 32
  match VL with
  | 128 => (execute_ST1W_Z_P_BR__ 128 esize g m msize n t)
  | 256 => (execute_ST1W_Z_P_BR__ 256 esize g m msize n t)
  | 512 => (execute_ST1W_Z_P_BR__ 512 esize g m msize n t)
  | 1024 => (execute_ST1W_Z_P_BR__ 1024 esize g m msize n t)
  | 2048 => (execute_ST1W_Z_P_BR__ 2048 esize g m msize n t)
  | _ => (pure ())

def decode_ST1D_Z_P_BR__ (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 64
  match VL with
  | 128 => (execute_ST1D_Z_P_BR__ 128 esize g m msize n t)
  | 256 => (execute_ST1D_Z_P_BR__ 256 esize g m msize n t)
  | 512 => (execute_ST1D_Z_P_BR__ 512 esize g m msize n t)
  | 1024 => (execute_ST1D_Z_P_BR__ 1024 esize g m msize n t)
  | 2048 => (execute_ST1D_Z_P_BR__ 2048 esize g m msize n t)
  | _ => (pure ())

def decode_ST1W_Z_P_BR_U128 (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let msize := 32
  match VL with
  | 128 => (execute_ST1W_Z_P_BR_U128 128 esize g m msize n t)
  | 256 => (execute_ST1W_Z_P_BR_U128 256 esize g m msize n t)
  | 512 => (execute_ST1W_Z_P_BR_U128 512 esize g m msize n t)
  | 1024 => (execute_ST1W_Z_P_BR_U128 1024 esize g m msize n t)
  | 2048 => (execute_ST1W_Z_P_BR_U128 2048 esize g m msize n t)
  | _ => (pure ())

def decode_ST1D_Z_P_BR_U128 (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE2p1 ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let msize := 64
  match VL with
  | 128 => (execute_ST1D_Z_P_BR_U128 128 esize g m msize n t)
  | 256 => (execute_ST1D_Z_P_BR_U128 256 esize g m msize n t)
  | 512 => (execute_ST1D_Z_P_BR_U128 512 esize g m msize n t)
  | 1024 => (execute_ST1D_Z_P_BR_U128 1024 esize g m msize n t)
  | 2048 => (execute_ST1D_Z_P_BR_U128 2048 esize g m msize n t)
  | _ => (pure ())

def decode_STR_P_BI__ (imm9h : (BitVec 6)) (imm9l : (BitVec 3)) (Rn : (BitVec 5)) (Pt : (BitVec 4)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Pt)
  let n := (BitVec.toNat Rn)
  let imm := (BitVec.toInt (imm9h +++ imm9l))
  match VL with
  | 128 => (execute_STR_P_BI__ 128 imm n t)
  | 256 => (execute_STR_P_BI__ 256 imm n t)
  | 512 => (execute_STR_P_BI__ 512 imm n t)
  | 1024 => (execute_STR_P_BI__ 1024 imm n t)
  | 2048 => (execute_STR_P_BI__ 2048 imm n t)
  | _ => (pure ())

def decode_STR_Z_BI__ (imm9h : (BitVec 6)) (imm9l : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let imm := (BitVec.toInt (imm9h +++ imm9l))
  match VL with
  | 128 => (execute_STR_Z_BI__ 128 imm n t)
  | 256 => (execute_STR_Z_BI__ 256 imm n t)
  | 512 => (execute_STR_Z_BI__ 512 imm n t)
  | 1024 => (execute_STR_Z_BI__ 1024 imm n t)
  | 2048 => (execute_STR_Z_BI__ 2048 imm n t)
  | _ => (pure ())

def decode_STNT1B_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 8
  match VL with
  | 128 => (execute_STNT1B_Z_P_BR_Contiguous 128 esize g m n t)
  | 256 => (execute_STNT1B_Z_P_BR_Contiguous 256 esize g m n t)
  | 512 => (execute_STNT1B_Z_P_BR_Contiguous 512 esize g m n t)
  | 1024 => (execute_STNT1B_Z_P_BR_Contiguous 1024 esize g m n t)
  | 2048 => (execute_STNT1B_Z_P_BR_Contiguous 2048 esize g m n t)
  | _ => (pure ())

def decode_STNT1H_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 16
  match VL with
  | 128 => (execute_STNT1H_Z_P_BR_Contiguous 128 esize g m n t)
  | 256 => (execute_STNT1H_Z_P_BR_Contiguous 256 esize g m n t)
  | 512 => (execute_STNT1H_Z_P_BR_Contiguous 512 esize g m n t)
  | 1024 => (execute_STNT1H_Z_P_BR_Contiguous 1024 esize g m n t)
  | 2048 => (execute_STNT1H_Z_P_BR_Contiguous 2048 esize g m n t)
  | _ => (pure ())

def decode_STNT1W_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  match VL with
  | 128 => (execute_STNT1W_Z_P_BR_Contiguous 128 esize g m n t)
  | 256 => (execute_STNT1W_Z_P_BR_Contiguous 256 esize g m n t)
  | 512 => (execute_STNT1W_Z_P_BR_Contiguous 512 esize g m n t)
  | 1024 => (execute_STNT1W_Z_P_BR_Contiguous 1024 esize g m n t)
  | 2048 => (execute_STNT1W_Z_P_BR_Contiguous 2048 esize g m n t)
  | _ => (pure ())

def decode_STNT1D_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  match VL with
  | 128 => (execute_STNT1D_Z_P_BR_Contiguous 128 esize g m n t)
  | 256 => (execute_STNT1D_Z_P_BR_Contiguous 256 esize g m n t)
  | 512 => (execute_STNT1D_Z_P_BR_Contiguous 512 esize g m n t)
  | 1024 => (execute_STNT1D_Z_P_BR_Contiguous 1024 esize g m n t)
  | 2048 => (execute_STNT1D_Z_P_BR_Contiguous 2048 esize g m n t)
  | _ => (pure ())

def decode_ST2B_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 8
  let nreg := 2
  match VL with
  | 128 => (execute_ST2B_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_ST2B_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_ST2B_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_ST2B_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_ST2B_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST2H_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let nreg := 2
  match VL with
  | 128 => (execute_ST2H_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_ST2H_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_ST2H_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_ST2H_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_ST2H_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST2W_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let nreg := 2
  match VL with
  | 128 => (execute_ST2W_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_ST2W_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_ST2W_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_ST2W_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_ST2W_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST2D_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let nreg := 2
  match VL with
  | 128 => (execute_ST2D_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_ST2D_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_ST2D_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_ST2D_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_ST2D_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST3B_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 8
  let nreg := 3
  match VL with
  | 128 => (execute_ST3B_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_ST3B_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_ST3B_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_ST3B_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_ST3B_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST3H_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let nreg := 3
  match VL with
  | 128 => (execute_ST3H_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_ST3H_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_ST3H_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_ST3H_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_ST3H_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST3W_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let nreg := 3
  match VL with
  | 128 => (execute_ST3W_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_ST3W_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_ST3W_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_ST3W_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_ST3W_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST3D_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let nreg := 3
  match VL with
  | 128 => (execute_ST3D_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_ST3D_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_ST3D_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_ST3D_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_ST3D_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST4B_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 8
  let nreg := 4
  match VL with
  | 128 => (execute_ST4B_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_ST4B_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_ST4B_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_ST4B_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_ST4B_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST4H_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 16
  let nreg := 4
  match VL with
  | 128 => (execute_ST4H_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_ST4H_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_ST4H_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_ST4H_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_ST4H_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST4W_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let nreg := 4
  match VL with
  | 128 => (execute_ST4W_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_ST4W_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_ST4W_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_ST4W_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_ST4W_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST4D_Z_P_BR_Contiguous (msz : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE ())))) <&&> (do
       (pure (! (← (HaveSME ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let nreg := 4
  match VL with
  | 128 => (execute_ST4D_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_ST4D_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_ST4D_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_ST4D_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_ST4D_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST2Q_Z_P_BR_Contiguous (num : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let nreg := 2
  match VL with
  | 128 => (execute_ST2Q_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_ST2Q_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_ST2Q_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_ST2Q_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_ST2Q_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST3Q_Z_P_BR_Contiguous (num : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let nreg := 3
  match VL with
  | 128 => (execute_ST3Q_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_ST3Q_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_ST3Q_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_ST3Q_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_ST3Q_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST4Q_Z_P_BR_Contiguous (num : (BitVec 2)) (Rm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((←((pure (! (← (HaveSVE2p1 ())))) <&&> (do
       (pure (! (← (HaveSME2p1 ()))))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((Rm == 0b11111#5) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Rm)
  let g := (BitVec.toNat Pg)
  let esize := 128
  let nreg := 4
  match VL with
  | 128 => (execute_ST4Q_Z_P_BR_Contiguous 128 esize g m n nreg t)
  | 256 => (execute_ST4Q_Z_P_BR_Contiguous 256 esize g m n nreg t)
  | 512 => (execute_ST4Q_Z_P_BR_Contiguous 512 esize g m n nreg t)
  | 1024 => (execute_ST4Q_Z_P_BR_Contiguous 1024 esize g m n nreg t)
  | 2048 => (execute_ST4Q_Z_P_BR_Contiguous 2048 esize g m n nreg t)
  | _ => (pure ())

def decode_ST1B_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (xs : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_ST1B_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1B_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1B_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1B_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1B_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1H_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (xs : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_ST1H_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1H_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1H_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1H_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1H_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1W_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (xs : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_ST1W_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1W_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1W_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1W_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1W_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1D_Z_P_BZ_D_x32_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (xs : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_ST1D_Z_P_BZ_D_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1D_Z_P_BZ_D_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1D_Z_P_BZ_D_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1D_Z_P_BZ_D_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1D_Z_P_BZ_D_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1B_Z_P_BZ_S_x32_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (xs : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 8
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_ST1B_Z_P_BZ_S_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1B_Z_P_BZ_S_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1B_Z_P_BZ_S_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1B_Z_P_BZ_S_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1B_Z_P_BZ_S_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1H_Z_P_BZ_S_x32_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (xs : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_ST1H_Z_P_BZ_S_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1H_Z_P_BZ_S_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1H_Z_P_BZ_S_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1H_Z_P_BZ_S_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1H_Z_P_BZ_S_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1W_Z_P_BZ_S_x32_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (xs : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 32
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 0
  match VL with
  | 128 => (execute_ST1W_Z_P_BZ_S_x32_unscaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1W_Z_P_BZ_S_x32_unscaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1W_Z_P_BZ_S_x32_unscaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1W_Z_P_BZ_S_x32_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1W_Z_P_BZ_S_x32_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1H_Z_P_BZ_D_x32_scaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (xs : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 1
  match VL with
  | 128 => (execute_ST1H_Z_P_BZ_D_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1H_Z_P_BZ_D_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1H_Z_P_BZ_D_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1H_Z_P_BZ_D_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1H_Z_P_BZ_D_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1W_Z_P_BZ_D_x32_scaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (xs : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 2
  match VL with
  | 128 => (execute_ST1W_Z_P_BZ_D_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1W_Z_P_BZ_D_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1W_Z_P_BZ_D_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1W_Z_P_BZ_D_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1W_Z_P_BZ_D_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1D_Z_P_BZ_D_x32_scaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (xs : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 3
  match VL with
  | 128 => (execute_ST1D_Z_P_BZ_D_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1D_Z_P_BZ_D_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1D_Z_P_BZ_D_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1D_Z_P_BZ_D_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1D_Z_P_BZ_D_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1H_Z_P_BZ_S_x32_scaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (xs : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 16
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 1
  match VL with
  | 128 => (execute_ST1H_Z_P_BZ_S_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1H_Z_P_BZ_S_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1H_Z_P_BZ_S_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1H_Z_P_BZ_S_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1H_Z_P_BZ_S_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1W_Z_P_BZ_S_x32_scaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (xs : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 32
  let msize := 32
  let offs_size := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale := 2
  match VL with
  | 128 => (execute_ST1W_Z_P_BZ_S_x32_scaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1W_Z_P_BZ_S_x32_scaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1W_Z_P_BZ_S_x32_scaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1W_Z_P_BZ_S_x32_scaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1W_Z_P_BZ_S_x32_scaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1B_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 8
  let offs_size := 64
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_ST1B_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1B_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1B_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1B_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1B_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1H_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 64
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_ST1H_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1H_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1H_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1H_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1H_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1W_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 64
  let offs_unsigned : Bool := true
  let scale := 0
  match VL with
  | 128 => (execute_ST1W_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1W_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1W_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1W_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1W_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1D_Z_P_BZ_D_64_unscaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
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
  let scale := 0
  match VL with
  | 128 => (execute_ST1D_Z_P_BZ_D_64_unscaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1D_Z_P_BZ_D_64_unscaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1D_Z_P_BZ_D_64_unscaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1D_Z_P_BZ_D_64_unscaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1D_Z_P_BZ_D_64_unscaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1H_Z_P_BZ_D_64_scaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 16
  let offs_size := 64
  let offs_unsigned : Bool := true
  let scale := 1
  match VL with
  | 128 => (execute_ST1H_Z_P_BZ_D_64_scaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1H_Z_P_BZ_D_64_scaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1H_Z_P_BZ_D_64_scaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1H_Z_P_BZ_D_64_scaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1H_Z_P_BZ_D_64_scaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())

def decode_ST1W_Z_P_BZ_D_64_scaled (msz : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  if ((! (← (HaveSVE ()))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let t := (BitVec.toNat Zt)
  let n := (BitVec.toNat Rn)
  let m := (BitVec.toNat Zm)
  let g := (BitVec.toNat Pg)
  let esize := 64
  let msize := 32
  let offs_size := 64
  let offs_unsigned : Bool := true
  let scale := 2
  match VL with
  | 128 => (execute_ST1W_Z_P_BZ_D_64_scaled 128 esize g m msize n offs_size offs_unsigned scale t)
  | 256 => (execute_ST1W_Z_P_BZ_D_64_scaled 256 esize g m msize n offs_size offs_unsigned scale t)
  | 512 => (execute_ST1W_Z_P_BZ_D_64_scaled 512 esize g m msize n offs_size offs_unsigned scale t)
  | 1024 => (execute_ST1W_Z_P_BZ_D_64_scaled 1024 esize g m msize n offs_size offs_unsigned scale t)
  | 2048 => (execute_ST1W_Z_P_BZ_D_64_scaled 2048 esize g m msize n offs_size offs_unsigned scale t)
  | _ => (pure ())


