import Armv9.Armv9
import Armv9.Flow
import Armv9.Arith
import Armv9.Vector
import Armv9.ReverseEndianness
import Armv9.Option
import Armv9.MonoRewrites
import Armv9.Common
import Armv9.Prelude
import Armv9.Builtins
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

def _get_SCTLR2_EL1_Type_EnIDCP128 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_SCTLR2_EL2_Type_EnIDCP128 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_SCR_EL3_Type_EnTP2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _update_SCTLR_EL1_Type_EnTP2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _update_SCTLR_EL2_Type_EnTP2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _get_SCTLR_EL1_Type_EnTP2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _get_SCTLR_EL2_Type_EnTP2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _update_SCR_EL3_Type_FGTEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_SCR_EL3_Type_FGTEn2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_SCR_EL3_Type_GCSEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)

def _update_HCRX_EL2_Type_GCSEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_SCR_EL3_Type_HXEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _update_SCR_EL3_Type_MECEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def _update_SCR_EL3_Type_NMEA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_SCTLR2_EL1_Type_NMEA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_SCTLR2_EL2_Type_NMEA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_SCTLR2_EL1_Type_NMEA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_SCTLR2_EL2_Type_NMEA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_SCR_EL3_Type_NSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_EDSCR_Type_NSE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_MFAR_EL3_Type_NSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_PAR_EL1_Type_NSE (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PFAR_EL1_Type_NSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_PFAR_EL2_Type_NSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_PMPCSR_Type_NSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _get_MFAR_EL3_Type_NSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _get_PAR_EL1_Type_NSE (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PFAR_EL1_Type_NSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _get_PFAR_EL2_Type_NSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _get_PMPCSR_Type_NSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _update_SCR_EL3_Type_PFAREn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _update_SCR_EL3_Type_PIEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _update_SCR_EL3_Type_RCWMASKEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _update_SCR_EL3_Type_SCTLR2En (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_HCRX_EL2_Type_SCTLR2En (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_SCR_EL3_Type_TCR2En (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _update_HCRX_EL2_Type_TCR2En (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_SCR_EL3_Type_TMEA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)

def _update_HCRX_EL2_Type_TMEA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_SCR_EL3_Type_TRNDR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _update_SCR_EL3_Type_TWERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def undefined_SCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_SCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def __get_FPCR (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : FPCR_Type := value_name
  let tmp : FPCR_Type := (Mk_FPCR_Type (tmp &&& (Complement.complement 0xFFFFFFFFF80040F8#64)))
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Invalid Operation floating-point exceptions"))) : Bool)
    then (pure (Mk_FPCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x100#12 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Divide by Zero floating-point exceptions"))) : Bool)
    then (pure (Mk_FPCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x200#12 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Overflow floating-point exceptions"))) : Bool)
    then (pure (Mk_FPCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x400#12 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Underflow floating-point exceptions"))) : Bool)
    then (pure (Mk_FPCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x800#12 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Inexact floating-point exceptions"))) : Bool)
    then (pure (Mk_FPCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x1000#16 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  let tmp ← (( do
    if ((! (← (__IMPDEF_boolean "IMPLEMENTED_trapping of Input Denormal floating-point exceptions"))) : Bool)
    then (pure (Mk_FPCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x8000#16 64)))))
    else (pure tmp) ) : SailM (BitVec 64) )
  if ((← (__IMPDEF_boolean "IMPLEMENTED_FPSCR.LEN,STRIDE as RAZ")) : Bool)
  then (pure (Mk_FPCR_Type (tmp &&& (Complement.complement (Sail.BitVec.zeroExtend 0x370000#24 64)))))
  else (pure tmp)

def undefined_FPSCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_FPSCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def FPSCR_read__1 (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _FPSCR ) : SailM FPSCR_Type )
  let r ← (pure (Sail.BitVec.updateSubrange r 31 27 (BitVec.slice (← readReg FPSR) 27 5)))
  let r ← (pure (BitVec.update r 7 (Bit (BitVec.slice (← readReg FPSR) 7 1))))
  let r ← (pure (Sail.BitVec.updateSubrange r 4 0 (BitVec.slice (← readReg FPSR) 0 5)))
  let r ← (pure (Sail.BitVec.updateSubrange r 26 15 (BitVec.slice (← readReg FPCR) 15 12)))
  (pure (Sail.BitVec.updateSubrange r 12 8 (BitVec.slice (← readReg FPCR) 8 5)))

def undefined_ERRnFR_ElemType (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ERRnFR_ElemType (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ERRnFR_ElemType_CE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 54 53)

def _update_ERRnFR_ElemType_CE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 53 x)

def _get_ERRnFR_ElemType_CEC (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 14 12)

def _update_ERRnFR_ElemType_CEC (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 12 x)

def _get_ERRnFR_ElemType_CEO (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 19 18)

def _update_ERRnFR_ElemType_CEO (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 18 x)

def _get_ERRnFR_ElemType_CFI (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _update_ERRnFR_ElemType_CFI (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _get_ERRnFR_ElemType_CI (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)

def _update_ERRnFR_ElemType_CI (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 22 x)

def _get_ERRnFR_ElemType_DE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)

def _update_ERRnFR_ElemType_DE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _get_ERRnFR_ElemType_DUI (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 17 16)

def _update_ERRnFR_ElemType_DUI (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 16 x)

def _get_ERRnFR_ElemType_ED (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _update_ERRnFR_ElemType_ED (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _get_ERRnFR_ElemType_FI (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def _update_ERRnFR_ElemType_FI (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _get_ERRnFR_ElemType_FRX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_ERRnFR_ElemType_FRX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_ERRnFR_ElemType_INJ (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)

def _update_ERRnFR_ElemType_INJ (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 20 x)

def _get_ERRnFR_ElemType_RP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_ERRnFR_ElemType_RP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_ERRnFR_ElemType_TS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)

def _update_ERRnFR_ElemType_TS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)

def _update_BRBCR_EL1_Type_TS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 5 x)

def _update_BRBCR_EL2_Type_TS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 5 x)

def _update_BRBTS_EL1_Type_TS (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_HTRFCR_Type_TS (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 5 x)

def _update_ID_AA64ISAR0_EL1_Type_TS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_PMSCR_EL1_Type_TS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMSCR_EL2_Type_TS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_TRFCR_EL1_Type_TS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 5 x)

def _update_TRFCR_EL2_Type_TS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 5 x)

def _update_TRFCR_Type_TS (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 5 x)

def _get_BRBTS_EL1_Type_TS (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_HTRFCR_Type_TS (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 6 5)

def _get_ID_AA64ISAR0_EL1_Type_TS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _get_PMSCR_EL1_Type_TS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMSCR_EL2_Type_TS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_TRFCR_EL1_Type_TS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 6 5)

def _get_TRFCR_EL2_Type_TS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 6 5)

def _get_TRFCR_Type_TS (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 6 5)

def _get_ERRnFR_ElemType_UC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _update_ERRnFR_ElemType_UC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _get_ERRnFR_ElemType_UE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)

def _update_ERRnFR_ElemType_UE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def _get_ERRnFR_ElemType_UEO (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 51 51)

def _update_ERRnFR_ElemType_UEO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)

def _get_ERRnFR_ElemType_UER (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)

def _update_ERRnFR_ElemType_UER (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _get_ERRnFR_ElemType_UEU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)

def _update_ERRnFR_ElemType_UEU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def _get_ERRnFR_ElemType_UI (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _update_ERRnFR_ElemType_UI (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def undefined_CTR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CTR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_CTR_EL0_Type_CWG (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_CTR_EL0_Type_CWG (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_CTR_Type_CWG (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_CTR_Type_CWG (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_CTR_EL0_Type_DIC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_CTR_EL0_Type_DIC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_CTR_Type_DIC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_CTR_Type_DIC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_CTR_EL0_Type_DminLine (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_CTR_Type_DminLine (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_CTR_Type_DminLine (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_CTR_EL0_Type_ERG (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_CTR_EL0_Type_ERG (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_CTR_Type_ERG (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_CTR_Type_ERG (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_CTR_EL0_Type_IminLine (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_CTR_EL0_Type_IminLine (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_CTR_Type_IminLine (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_CTR_Type_IminLine (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_CTR_EL0_Type_L1Ip (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)

def _update_CTR_EL0_Type_L1Ip (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_CTR_Type_L1Ip (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _get_CTR_Type_L1Ip (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)

def _get_CTR_EL0_Type_TminLine (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 37 32)

def _update_CTR_EL0_Type_TminLine (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 32 x)

def undefined_HDCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_HDCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _update_HDCR_Type_HCCD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_MDCR_EL2_Type_HCCD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_HDCR_Type_HLP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_HDCR_Type_HLP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_MDCR_EL2_Type_HLP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_HDCR_Type_HPMD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_MDCR_EL2_Type_HPMD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_HDCR_Type_HPME (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_MDCR_EL2_Type_HPME (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_HDCR_Type_HPMFZO (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_MDCR_EL2_Type_HPMFZO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_HDCR_Type_HPMN (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _update_MDCR_EL2_Type_HPMN (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _get_HDCR_Type_MTPME (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_HDCR_Type_MTPME (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_MDCR_EL2_Type_MTPME (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_MDCR_EL3_Type_MTPME (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_SDCR_Type_MTPME (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_SDCR_Type_MTPME (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_HDCR_Type_TDA (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_HDCR_Type_TDA (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_DBGDSCRext_Type_TDA (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_EDSCR_Type_TDA (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_MDCR_EL2_Type_TDA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_MDCR_EL3_Type_TDA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_MDSCR_EL1_Type_TDA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_DBGDSCRext_Type_TDA (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_HDCR_Type_TDCC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_HDCR_Type_TDCC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_MDCR_EL2_Type_TDCC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_MDCR_EL3_Type_TDCC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_MDSCR_EL1_Type_TDCC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_SDCR_Type_TDCC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_SDCR_Type_TDCC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_HDCR_Type_TDE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_MDCR_EL2_Type_TDE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_HDCR_Type_TDOSA (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_HDCR_Type_TDOSA (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_MDCR_EL2_Type_TDOSA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_MDCR_EL3_Type_TDOSA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_HDCR_Type_TDRA (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_HDCR_Type_TDRA (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_MDCR_EL2_Type_TDRA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_HDCR_Type_TPM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_HDCR_Type_TPM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_MDCR_EL2_Type_TPM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_MDCR_EL3_Type_TPM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_HDCR_Type_TPMCR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_HDCR_Type_TPMCR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_MDCR_EL2_Type_TPMCR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_HDCR_Type_TTRF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_HDCR_Type_TTRF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_MDCR_EL2_Type_TTRF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_MDCR_EL3_Type_TTRF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_SDCR_Type_TTRF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_SDCR_Type_TTRF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def undefined_MDCR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MDCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_MDCR_EL2_Type_E2PB (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _update_MDCR_EL2_Type_EBWE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _update_MDCR_EL3_Type_EBWE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _update_MDCR_EL2_Type_EnSPM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_MDSCR_EL1_Type_EnSPM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _update_MDCR_EL2_Type_HPMFZS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _update_MDCR_EL2_Type_PMEE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 40 x)

def _update_MDCR_EL3_Type_PMEE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 40 x)

def _update_PMECR_EL1_Type_PMEE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _get_PMECR_EL1_Type_PMEE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _update_MDCR_EL2_Type_PMSSE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 30 x)

def _update_MDCR_EL3_Type_PMSSE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 30 x)

def _update_MDCR_EL2_Type_TPMS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def AArch32_GetNumEventCountersAccessible (_ : Unit) : SailM Int := do
  let n ← (( do (undefined_int ()) ) : SailM Int )
  let total_counters ← do (GetNumEventCounters ())
  let n ← (( do
    if ((←((pure ((← readReg PSTATE).EL == EL1)) <||> (do
         (pure ((← readReg PSTATE).EL == EL0))) <&&> (do
         (EL2Enabled ())))) : Bool)
    then
      (do
        let n ←
          (pure (BitVec.toNat
              (← (do
                if ((! (← (ELUsingAArch32 EL2))) : Bool)
                then (pure (_get_MDCR_EL2_Type_HPMN (← readReg MDCR_EL2)))
                else (pure (_get_HDCR_Type_HPMN (← (HDCR_read ()))))))))
        if ((←((pure (n >b total_counters)) <||> (do
             (pure ((! (← (HaveFeatHPMN0 ()))) && (n == 0)))))) : Bool)
        then
          (do
            let (_, __tup_1) ← do (ConstrainUnpredictableInteger 0 total_counters Unpredictable_PMUEVENTCOUNTER)
            (pure __tup_1))
        else (pure n))
    else (pure total_counters) ) : SailM Int )
  let n := n
  (pure n)

def AArch64_GetNumEventCountersAccessible (_ : Unit) : SailM Int := do
  let n ← (( do (undefined_int ()) ) : SailM Int )
  let total_counters ← do (GetNumEventCounters ())
  let n ← (( do
    if ((←((pure ((← readReg PSTATE).EL == EL1)) <||> (do
         (pure ((← readReg PSTATE).EL == EL0))) <&&> (do
         (EL2Enabled ())))) : Bool)
    then
      (do
        let n ← (pure (BitVec.toNat (_get_MDCR_EL2_Type_HPMN (← readReg MDCR_EL2))))
        if ((←((pure (n >b total_counters)) <||> (do
             (pure ((! (← (HaveFeatHPMN0 ()))) && (n == 0)))))) : Bool)
        then
          (do
            let (_, __tup_1) ← do (ConstrainUnpredictableInteger 0 total_counters Unpredictable_PMUEVENTCOUNTER)
            (pure __tup_1))
        else (pure n))
    else (pure total_counters) ) : SailM Int )
  let n := n
  (pure n)

def undefined_EDSCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDSCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _update_DBGDSCRext_Type_ERR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_MDSCR_EL1_Type_ERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _set_EDSCR_Type_ERR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_ERR r v)

def _get_DBGDSCRext_Type_ERR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_EDSCR_Type_HDE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_DBGDSCRext_Type_HDE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_MDSCR_EL1_Type_HDE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_DBGDSCRext_Type_HDE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_EDSCR_Type_INTdis (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 22 x)

def _update_DBGDSCRext_Type_INTdis (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 22 x)

def _update_MDSCR_EL1_Type_INTdis (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 22 x)

def _get_DBGDSCRext_Type_INTdis (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)

def _update_EDDFR1_Type_ITE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_ID_AA64DFR1_EL1_Type_ITE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _set_EDSCR_Type_ITE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_ITE r v)

def _get_EDDFR1_Type_ITE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_ID_AA64DFR1_EL1_Type_ITE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _set_EDSCR_Type_ITO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_ITO r v)

def _set_EDSCR_Type_MA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_MA r v)

def _update_EDSCR_Type_PipeAdv (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_EDSCR_Type_RXO (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_DBGDSCRext_Type_RXO (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_MDSCR_EL1_Type_RXO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_DBGDSCRext_Type_RXO (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_EDSCR_Type_RXfull (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_DBGDSCRext_Type_RXfull (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_DBGDSCRint_Type_RXfull (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_MDCCSR_EL0_Type_RXfull (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_MDSCR_EL1_Type_RXfull (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_DBGDSCRext_Type_RXfull (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_DBGDSCRint_Type_RXfull (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_MDCCSR_EL0_Type_RXfull (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_EDSCR_Type_SC2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_DBGDSCRext_Type_SC2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_MDSCR_EL1_Type_SC2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_DBGDSCRext_Type_SC2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_MDCR_EL3_Type_SDD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _set_EDSCR_Type_SDD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_SDD r v)

def _update_DFSR_Type_STATUS (v : (BitVec 32)) (x : (BitVec 6)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 0 x)

def _update_DISR_Type_STATUS (v : (BitVec 32)) (x : (BitVec 6)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 0 x)

def _update_IFSR32_EL2_Type_STATUS (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 0 x)

def _update_IFSR_Type_STATUS (v : (BitVec 32)) (x : (BitVec 6)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 0 x)

def _update_VDISR_EL2_Type_STATUS (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 0 x)

def _update_VDISR_Type_STATUS (v : (BitVec 32)) (x : (BitVec 6)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 0 x)

def _set_EDSCR_Type_STATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 6)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_STATUS r v)

def _get_DFSR_Type_STATUS (v : (BitVec 32)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 5 0)

def _get_DISR_Type_STATUS (v : (BitVec 32)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 5 0)

def _get_IFSR32_EL2_Type_STATUS (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 5 0)

def _get_IFSR_Type_STATUS (v : (BitVec 32)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 5 0)

def _get_VDISR_EL2_Type_STATUS (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 5 0)

def _get_VDISR_Type_STATUS (v : (BitVec 32)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 5 0)

def _update_EDSCR_Type_TFO (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_DBGDSCRext_Type_TFO (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_MDSCR_EL1_Type_TFO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_DBGDSCRext_Type_TFO (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_EDSCR_Type_TXU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_DBGDSCRext_Type_TXU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_MDSCR_EL1_Type_TXU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_DBGDSCRext_Type_TXU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_EDSCR_Type_TXfull (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_DBGDSCRext_Type_TXfull (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_DBGDSCRint_Type_TXfull (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_MDCCSR_EL0_Type_TXfull (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_MDSCR_EL1_Type_TXfull (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_DBGDSCRext_Type_TXfull (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_DBGDSCRint_Type_TXfull (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_MDCCSR_EL0_Type_TXfull (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def undefined_MDCCSR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MDCCSR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PMCNTENCLR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMCNTENCLR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMCNTENCLR_EL0_Type_F0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _update_PMCNTENCLR_EL0_Type_F0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_PMCNTENSET_EL0_Type_F0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_PMCNTEN_Type_F0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_PMINTENCLR_EL1_Type_F0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_PMINTENSET_EL1_Type_F0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_PMINTEN_Type_F0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_PMOVSCLR_EL0_Type_F0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_PMOVSSET_EL0_Type_F0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_PMOVS_Type_F0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_PMUACR_EL1_Type_F0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_PMZR_EL0_Type_F0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _get_PMCNTEN_Type_F0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _get_PMINTENCLR_EL1_Type_F0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _get_PMINTENSET_EL1_Type_F0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _get_PMINTEN_Type_F0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _get_PMOVSCLR_EL0_Type_F0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _get_PMOVSSET_EL0_Type_F0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _get_PMOVS_Type_F0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _get_PMUACR_EL1_Type_F0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _get_PMZR_EL0_Type_F0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _get_PMCNTENCLR_EL0_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_PMCNTENCLR_EL0_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_AMCNTENCLR0_EL0_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_AMCNTENCLR0_Type_P0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_AMCNTENCLR1_EL0_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_AMCNTENCLR1_Type_P0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_AMCNTENSET0_EL0_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_AMCNTENSET0_Type_P0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_AMCNTENSET1_EL0_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_AMCNTENSET1_Type_P0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICH_AP0R_EL2_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICH_AP0R_Type_P0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICH_AP1R_EL2_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICH_AP1R_Type_P0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMCNTENCLR_Type_P0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMCNTENSET_EL0_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMCNTENSET_Type_P0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMCNTEN_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMINTENCLR_EL1_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMINTENCLR_Type_P0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMINTENSET_EL1_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMINTENSET_Type_P0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMINTEN_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMOVSCLR_EL0_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMOVSR_Type_P0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMOVSSET_EL0_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMOVSSET_Type_P0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMOVS_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMSWINC_EL0_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMSWINC_Type_P0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMUACR_EL1_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMZR_EL0_Type_P0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_SMPRIMAP_EL2_Type_P0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_SPMACCESSR_EL1_Type_P0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _update_SPMACCESSR_EL2_Type_P0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _update_SPMACCESSR_EL3_Type_P0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _get_AMCNTENCLR0_EL0_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_AMCNTENCLR0_Type_P0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_AMCNTENCLR1_EL0_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_AMCNTENCLR1_Type_P0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_AMCNTENSET0_EL0_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_AMCNTENSET0_Type_P0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_AMCNTENSET1_EL0_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_AMCNTENSET1_Type_P0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICH_AP0R_EL2_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICH_AP0R_Type_P0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICH_AP1R_EL2_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_ICH_AP1R_Type_P0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMCNTENCLR_Type_P0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMCNTENSET_EL0_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMCNTENSET_Type_P0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMCNTEN_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMINTENCLR_EL1_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMINTENCLR_Type_P0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMINTENSET_EL1_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMINTENSET_Type_P0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMINTEN_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMOVSCLR_EL0_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMOVSR_Type_P0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMOVSSET_EL0_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMOVSSET_Type_P0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMOVS_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMSWINC_EL0_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMSWINC_Type_P0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMUACR_EL1_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMZR_EL0_Type_P0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_SMPRIMAP_EL2_Type_P0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_SPMACCESSR_EL1_Type_P0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _get_SPMACCESSR_EL2_Type_P0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _get_SPMACCESSR_EL3_Type_P0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _get_PMCNTENCLR_EL0_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_PMCNTENCLR_EL0_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_AMCNTENCLR0_EL0_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_AMCNTENCLR0_Type_P1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_AMCNTENCLR1_EL0_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_AMCNTENCLR1_Type_P1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_AMCNTENSET0_EL0_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_AMCNTENSET0_Type_P1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_AMCNTENSET1_EL0_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_AMCNTENSET1_Type_P1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICH_AP0R_EL2_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICH_AP0R_Type_P1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICH_AP1R_EL2_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICH_AP1R_Type_P1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMCNTENCLR_Type_P1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMCNTENSET_EL0_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMCNTENSET_Type_P1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMCNTEN_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMINTENCLR_EL1_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMINTENCLR_Type_P1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMINTENSET_EL1_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMINTENSET_Type_P1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMINTEN_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMOVSCLR_EL0_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMOVSR_Type_P1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMOVSSET_EL0_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMOVSSET_Type_P1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMOVS_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMSWINC_EL0_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMSWINC_Type_P1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMUACR_EL1_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMZR_EL0_Type_P1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_SMPRIMAP_EL2_Type_P1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_SPMACCESSR_EL1_Type_P1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 2 x)

def _update_SPMACCESSR_EL2_Type_P1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 2 x)

def _update_SPMACCESSR_EL3_Type_P1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 2 x)

def _get_AMCNTENCLR0_EL0_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_AMCNTENCLR0_Type_P1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_AMCNTENCLR1_EL0_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_AMCNTENCLR1_Type_P1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_AMCNTENSET0_EL0_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_AMCNTENSET0_Type_P1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_AMCNTENSET1_EL0_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_AMCNTENSET1_Type_P1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICH_AP0R_EL2_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICH_AP0R_Type_P1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICH_AP1R_EL2_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICH_AP1R_Type_P1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMCNTENCLR_Type_P1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMCNTENSET_EL0_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMCNTENSET_Type_P1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMCNTEN_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMINTENCLR_EL1_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMINTENCLR_Type_P1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMINTENSET_EL1_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMINTENSET_Type_P1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMINTEN_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMOVSCLR_EL0_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMOVSR_Type_P1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMOVSSET_EL0_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMOVSSET_Type_P1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMOVS_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMSWINC_EL0_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMSWINC_Type_P1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMUACR_EL1_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMZR_EL0_Type_P1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_SMPRIMAP_EL2_Type_P1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_SPMACCESSR_EL1_Type_P1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)

def _get_SPMACCESSR_EL2_Type_P1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)

def _get_SPMACCESSR_EL3_Type_P1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)

def _get_PMCNTENCLR_EL0_Type_P10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_PMCNTENCLR_EL0_Type_P10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_AMCNTENCLR1_EL0_Type_P10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_AMCNTENCLR1_Type_P10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_AMCNTENSET1_EL0_Type_P10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_AMCNTENSET1_Type_P10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_ICH_AP0R_EL2_Type_P10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_ICH_AP0R_Type_P10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_ICH_AP1R_EL2_Type_P10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_ICH_AP1R_Type_P10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMCNTENCLR_Type_P10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMCNTENSET_EL0_Type_P10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMCNTENSET_Type_P10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMCNTEN_Type_P10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMINTENCLR_EL1_Type_P10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMINTENCLR_Type_P10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMINTENSET_EL1_Type_P10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMINTENSET_Type_P10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMINTEN_Type_P10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMOVSCLR_EL0_Type_P10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMOVSR_Type_P10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMOVSSET_EL0_Type_P10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMOVSSET_Type_P10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMOVS_Type_P10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMSWINC_EL0_Type_P10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMSWINC_Type_P10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMUACR_EL1_Type_P10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMZR_EL0_Type_P10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_SMPRIMAP_EL2_Type_P10 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_SPMACCESSR_EL1_Type_P10 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 20 x)

def _update_SPMACCESSR_EL2_Type_P10 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 20 x)

def _update_SPMACCESSR_EL3_Type_P10 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 20 x)

def _get_AMCNTENCLR1_EL0_Type_P10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_AMCNTENCLR1_Type_P10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_AMCNTENSET1_EL0_Type_P10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_AMCNTENSET1_Type_P10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_ICH_AP0R_EL2_Type_P10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_ICH_AP0R_Type_P10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_ICH_AP1R_EL2_Type_P10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_ICH_AP1R_Type_P10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMCNTENCLR_Type_P10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMCNTENSET_EL0_Type_P10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMCNTENSET_Type_P10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMCNTEN_Type_P10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMINTENCLR_EL1_Type_P10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMINTENCLR_Type_P10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMINTENSET_EL1_Type_P10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMINTENSET_Type_P10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMINTEN_Type_P10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMOVSCLR_EL0_Type_P10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMOVSR_Type_P10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMOVSSET_EL0_Type_P10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMOVSSET_Type_P10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMOVS_Type_P10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMSWINC_EL0_Type_P10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMSWINC_Type_P10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMUACR_EL1_Type_P10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMZR_EL0_Type_P10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_SMPRIMAP_EL2_Type_P10 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_SPMACCESSR_EL1_Type_P10 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)

def _get_SPMACCESSR_EL2_Type_P10 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)

def _get_SPMACCESSR_EL3_Type_P10 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)

def _get_PMCNTENCLR_EL0_Type_P11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_PMCNTENCLR_EL0_Type_P11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_AMCNTENCLR1_EL0_Type_P11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_AMCNTENCLR1_Type_P11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_AMCNTENSET1_EL0_Type_P11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_AMCNTENSET1_Type_P11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_ICH_AP0R_EL2_Type_P11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_ICH_AP0R_Type_P11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_ICH_AP1R_EL2_Type_P11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_ICH_AP1R_Type_P11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMCNTENCLR_Type_P11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMCNTENSET_EL0_Type_P11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMCNTENSET_Type_P11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMCNTEN_Type_P11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMINTENCLR_EL1_Type_P11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMINTENCLR_Type_P11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMINTENSET_EL1_Type_P11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMINTENSET_Type_P11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMINTEN_Type_P11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMOVSCLR_EL0_Type_P11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMOVSR_Type_P11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMOVSSET_EL0_Type_P11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMOVSSET_Type_P11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMOVS_Type_P11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMSWINC_EL0_Type_P11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMSWINC_Type_P11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMUACR_EL1_Type_P11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMZR_EL0_Type_P11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_SMPRIMAP_EL2_Type_P11 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_SPMACCESSR_EL1_Type_P11 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 22 x)

def _update_SPMACCESSR_EL2_Type_P11 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 22 x)

def _update_SPMACCESSR_EL3_Type_P11 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 22 x)

def _get_AMCNTENCLR1_EL0_Type_P11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_AMCNTENCLR1_Type_P11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_AMCNTENSET1_EL0_Type_P11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_AMCNTENSET1_Type_P11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_ICH_AP0R_EL2_Type_P11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_ICH_AP0R_Type_P11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_ICH_AP1R_EL2_Type_P11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_ICH_AP1R_Type_P11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMCNTENCLR_Type_P11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMCNTENSET_EL0_Type_P11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMCNTENSET_Type_P11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMCNTEN_Type_P11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMINTENCLR_EL1_Type_P11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMINTENCLR_Type_P11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMINTENSET_EL1_Type_P11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMINTENSET_Type_P11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMINTEN_Type_P11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMOVSCLR_EL0_Type_P11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMOVSR_Type_P11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMOVSSET_EL0_Type_P11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMOVSSET_Type_P11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMOVS_Type_P11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMSWINC_EL0_Type_P11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMSWINC_Type_P11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMUACR_EL1_Type_P11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMZR_EL0_Type_P11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_SMPRIMAP_EL2_Type_P11 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_SPMACCESSR_EL1_Type_P11 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)

def _get_SPMACCESSR_EL2_Type_P11 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)

def _get_SPMACCESSR_EL3_Type_P11 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)

def _get_PMCNTENCLR_EL0_Type_P12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_PMCNTENCLR_EL0_Type_P12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_AMCNTENCLR1_EL0_Type_P12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_AMCNTENCLR1_Type_P12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_AMCNTENSET1_EL0_Type_P12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_AMCNTENSET1_Type_P12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_ICH_AP0R_EL2_Type_P12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_ICH_AP0R_Type_P12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_ICH_AP1R_EL2_Type_P12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_ICH_AP1R_Type_P12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMCNTENCLR_Type_P12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMCNTENSET_EL0_Type_P12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMCNTENSET_Type_P12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMCNTEN_Type_P12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMINTENCLR_EL1_Type_P12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMINTENCLR_Type_P12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMINTENSET_EL1_Type_P12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMINTENSET_Type_P12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMINTEN_Type_P12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMOVSCLR_EL0_Type_P12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMOVSR_Type_P12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMOVSSET_EL0_Type_P12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMOVSSET_Type_P12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMOVS_Type_P12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMSWINC_EL0_Type_P12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMSWINC_Type_P12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMUACR_EL1_Type_P12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMZR_EL0_Type_P12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_SMPRIMAP_EL2_Type_P12 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_SPMACCESSR_EL1_Type_P12 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)

def _update_SPMACCESSR_EL2_Type_P12 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)

def _update_SPMACCESSR_EL3_Type_P12 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)

def _get_AMCNTENCLR1_EL0_Type_P12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_AMCNTENCLR1_Type_P12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_AMCNTENSET1_EL0_Type_P12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_AMCNTENSET1_Type_P12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_ICH_AP0R_EL2_Type_P12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_ICH_AP0R_Type_P12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_ICH_AP1R_EL2_Type_P12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_ICH_AP1R_Type_P12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMCNTENCLR_Type_P12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMCNTENSET_EL0_Type_P12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMCNTENSET_Type_P12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMCNTEN_Type_P12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMINTENCLR_EL1_Type_P12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMINTENCLR_Type_P12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMINTENSET_EL1_Type_P12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMINTENSET_Type_P12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMINTEN_Type_P12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMOVSCLR_EL0_Type_P12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMOVSR_Type_P12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMOVSSET_EL0_Type_P12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMOVSSET_Type_P12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMOVS_Type_P12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMSWINC_EL0_Type_P12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMSWINC_Type_P12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMUACR_EL1_Type_P12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMZR_EL0_Type_P12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_SMPRIMAP_EL2_Type_P12 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_SPMACCESSR_EL1_Type_P12 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)

def _get_SPMACCESSR_EL2_Type_P12 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)

def _get_SPMACCESSR_EL3_Type_P12 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)

def _get_PMCNTENCLR_EL0_Type_P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_PMCNTENCLR_EL0_Type_P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_AMCNTENCLR1_EL0_Type_P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_AMCNTENCLR1_Type_P13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_AMCNTENSET1_EL0_Type_P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_AMCNTENSET1_Type_P13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_ICH_AP0R_EL2_Type_P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_ICH_AP0R_Type_P13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_ICH_AP1R_EL2_Type_P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_ICH_AP1R_Type_P13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMCNTENCLR_Type_P13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMCNTENSET_EL0_Type_P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMCNTENSET_Type_P13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMCNTEN_Type_P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMINTENCLR_EL1_Type_P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMINTENCLR_Type_P13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMINTENSET_EL1_Type_P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMINTENSET_Type_P13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMINTEN_Type_P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMOVSCLR_EL0_Type_P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMOVSR_Type_P13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMOVSSET_EL0_Type_P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMOVSSET_Type_P13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMOVS_Type_P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMSWINC_EL0_Type_P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMSWINC_Type_P13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMUACR_EL1_Type_P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMZR_EL0_Type_P13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_SMPRIMAP_EL2_Type_P13 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_SPMACCESSR_EL1_Type_P13 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 26 x)

def _update_SPMACCESSR_EL2_Type_P13 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 26 x)

def _update_SPMACCESSR_EL3_Type_P13 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 26 x)

def _get_AMCNTENCLR1_EL0_Type_P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_AMCNTENCLR1_Type_P13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_AMCNTENSET1_EL0_Type_P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_AMCNTENSET1_Type_P13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_ICH_AP0R_EL2_Type_P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_ICH_AP0R_Type_P13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_ICH_AP1R_EL2_Type_P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_ICH_AP1R_Type_P13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMCNTENCLR_Type_P13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMCNTENSET_EL0_Type_P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMCNTENSET_Type_P13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMCNTEN_Type_P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMINTENCLR_EL1_Type_P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMINTENCLR_Type_P13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMINTENSET_EL1_Type_P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMINTENSET_Type_P13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMINTEN_Type_P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMOVSCLR_EL0_Type_P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMOVSR_Type_P13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMOVSSET_EL0_Type_P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMOVSSET_Type_P13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMOVS_Type_P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMSWINC_EL0_Type_P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMSWINC_Type_P13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMUACR_EL1_Type_P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMZR_EL0_Type_P13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_SMPRIMAP_EL2_Type_P13 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _get_SPMACCESSR_EL1_Type_P13 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 27 26)

def _get_SPMACCESSR_EL2_Type_P13 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 27 26)

def _get_SPMACCESSR_EL3_Type_P13 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 27 26)

def _get_PMCNTENCLR_EL0_Type_P14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_PMCNTENCLR_EL0_Type_P14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_AMCNTENCLR1_EL0_Type_P14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_AMCNTENCLR1_Type_P14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_AMCNTENSET1_EL0_Type_P14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_AMCNTENSET1_Type_P14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_ICH_AP0R_EL2_Type_P14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_ICH_AP0R_Type_P14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_ICH_AP1R_EL2_Type_P14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_ICH_AP1R_Type_P14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMCNTENCLR_Type_P14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMCNTENSET_EL0_Type_P14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMCNTENSET_Type_P14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMCNTEN_Type_P14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMINTENCLR_EL1_Type_P14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMINTENCLR_Type_P14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMINTENSET_EL1_Type_P14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMINTENSET_Type_P14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMINTEN_Type_P14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMOVSCLR_EL0_Type_P14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMOVSR_Type_P14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMOVSSET_EL0_Type_P14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMOVSSET_Type_P14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMOVS_Type_P14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMSWINC_EL0_Type_P14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMSWINC_Type_P14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMUACR_EL1_Type_P14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMZR_EL0_Type_P14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_SMPRIMAP_EL2_Type_P14 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_SPMACCESSR_EL1_Type_P14 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 28 x)

def _update_SPMACCESSR_EL2_Type_P14 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 28 x)

def _update_SPMACCESSR_EL3_Type_P14 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 28 x)

def _get_AMCNTENCLR1_EL0_Type_P14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_AMCNTENCLR1_Type_P14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_AMCNTENSET1_EL0_Type_P14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_AMCNTENSET1_Type_P14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_ICH_AP0R_EL2_Type_P14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_ICH_AP0R_Type_P14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_ICH_AP1R_EL2_Type_P14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_ICH_AP1R_Type_P14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMCNTENCLR_Type_P14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMCNTENSET_EL0_Type_P14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMCNTENSET_Type_P14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMCNTEN_Type_P14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMINTENCLR_EL1_Type_P14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMINTENCLR_Type_P14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMINTENSET_EL1_Type_P14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMINTENSET_Type_P14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMINTEN_Type_P14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMOVSCLR_EL0_Type_P14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMOVSR_Type_P14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMOVSSET_EL0_Type_P14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMOVSSET_Type_P14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMOVS_Type_P14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMSWINC_EL0_Type_P14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMSWINC_Type_P14 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMUACR_EL1_Type_P14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMZR_EL0_Type_P14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_SMPRIMAP_EL2_Type_P14 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_SPMACCESSR_EL1_Type_P14 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 29 28)

def _get_SPMACCESSR_EL2_Type_P14 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 29 28)

def _get_SPMACCESSR_EL3_Type_P14 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 29 28)

def _get_PMCNTENCLR_EL0_Type_P15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_PMCNTENCLR_EL0_Type_P15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_AMCNTENCLR1_EL0_Type_P15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_AMCNTENCLR1_Type_P15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_AMCNTENSET1_EL0_Type_P15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_AMCNTENSET1_Type_P15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_ICH_AP0R_EL2_Type_P15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_ICH_AP0R_Type_P15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_ICH_AP1R_EL2_Type_P15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_ICH_AP1R_Type_P15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMCNTENCLR_Type_P15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMCNTENSET_EL0_Type_P15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMCNTENSET_Type_P15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMCNTEN_Type_P15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMINTENCLR_EL1_Type_P15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMINTENCLR_Type_P15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMINTENSET_EL1_Type_P15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMINTENSET_Type_P15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMINTEN_Type_P15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMOVSCLR_EL0_Type_P15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMOVSR_Type_P15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMOVSSET_EL0_Type_P15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMOVSSET_Type_P15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMOVS_Type_P15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMSWINC_EL0_Type_P15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMSWINC_Type_P15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMUACR_EL1_Type_P15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMZR_EL0_Type_P15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_SMPRIMAP_EL2_Type_P15 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_SPMACCESSR_EL1_Type_P15 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 30 x)

def _update_SPMACCESSR_EL2_Type_P15 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 30 x)

def _update_SPMACCESSR_EL3_Type_P15 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 30 x)

def _get_AMCNTENCLR1_EL0_Type_P15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_AMCNTENCLR1_Type_P15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_AMCNTENSET1_EL0_Type_P15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_AMCNTENSET1_Type_P15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_ICH_AP0R_EL2_Type_P15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_ICH_AP0R_Type_P15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_ICH_AP1R_EL2_Type_P15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_ICH_AP1R_Type_P15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMCNTENCLR_Type_P15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMCNTENSET_EL0_Type_P15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMCNTENSET_Type_P15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMCNTEN_Type_P15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMINTENCLR_EL1_Type_P15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMINTENCLR_Type_P15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMINTENSET_EL1_Type_P15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMINTENSET_Type_P15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMINTEN_Type_P15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMOVSCLR_EL0_Type_P15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMOVSR_Type_P15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMOVSSET_EL0_Type_P15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMOVSSET_Type_P15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMOVS_Type_P15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMSWINC_EL0_Type_P15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMSWINC_Type_P15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMUACR_EL1_Type_P15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMZR_EL0_Type_P15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_SMPRIMAP_EL2_Type_P15 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _get_SPMACCESSR_EL1_Type_P15 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)

def _get_SPMACCESSR_EL2_Type_P15 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)

def _get_SPMACCESSR_EL3_Type_P15 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)

def _get_PMCNTENCLR_EL0_Type_P16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_PMCNTENCLR_EL0_Type_P16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_ICH_AP0R_EL2_Type_P16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_ICH_AP0R_Type_P16 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_ICH_AP1R_EL2_Type_P16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_ICH_AP1R_Type_P16 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMCNTENCLR_Type_P16 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMCNTENSET_EL0_Type_P16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMCNTENSET_Type_P16 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMCNTEN_Type_P16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMINTENCLR_EL1_Type_P16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMINTENCLR_Type_P16 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMINTENSET_EL1_Type_P16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMINTENSET_Type_P16 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMINTEN_Type_P16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMOVSCLR_EL0_Type_P16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMOVSR_Type_P16 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMOVSSET_EL0_Type_P16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMOVSSET_Type_P16 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMOVS_Type_P16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMSWINC_EL0_Type_P16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMSWINC_Type_P16 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMUACR_EL1_Type_P16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMZR_EL0_Type_P16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_SPMACCESSR_EL1_Type_P16 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _update_SPMACCESSR_EL2_Type_P16 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _update_SPMACCESSR_EL3_Type_P16 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _get_ICH_AP0R_EL2_Type_P16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_ICH_AP0R_Type_P16 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_ICH_AP1R_EL2_Type_P16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_ICH_AP1R_Type_P16 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMCNTENCLR_Type_P16 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMCNTENSET_EL0_Type_P16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMCNTENSET_Type_P16 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMCNTEN_Type_P16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMINTENCLR_EL1_Type_P16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMINTENCLR_Type_P16 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMINTENSET_EL1_Type_P16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMINTENSET_Type_P16 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMINTEN_Type_P16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMOVSCLR_EL0_Type_P16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMOVSR_Type_P16 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMOVSSET_EL0_Type_P16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMOVSSET_Type_P16 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMOVS_Type_P16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMSWINC_EL0_Type_P16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMSWINC_Type_P16 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMUACR_EL1_Type_P16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMZR_EL0_Type_P16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_SPMACCESSR_EL1_Type_P16 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

def _get_SPMACCESSR_EL2_Type_P16 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

def _get_SPMACCESSR_EL3_Type_P16 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 33 32)

def _get_PMCNTENCLR_EL0_Type_P17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_PMCNTENCLR_EL0_Type_P17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_ICH_AP0R_EL2_Type_P17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_ICH_AP0R_Type_P17 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_ICH_AP1R_EL2_Type_P17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_ICH_AP1R_Type_P17 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMCNTENCLR_Type_P17 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMCNTENSET_EL0_Type_P17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMCNTENSET_Type_P17 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMCNTEN_Type_P17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMINTENCLR_EL1_Type_P17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMINTENCLR_Type_P17 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMINTENSET_EL1_Type_P17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMINTENSET_Type_P17 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMINTEN_Type_P17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMOVSCLR_EL0_Type_P17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMOVSR_Type_P17 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMOVSSET_EL0_Type_P17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMOVSSET_Type_P17 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMOVS_Type_P17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMSWINC_EL0_Type_P17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMSWINC_Type_P17 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMUACR_EL1_Type_P17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMZR_EL0_Type_P17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_SPMACCESSR_EL1_Type_P17 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 34 x)

def _update_SPMACCESSR_EL2_Type_P17 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 34 x)

def _update_SPMACCESSR_EL3_Type_P17 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 34 x)

def _get_ICH_AP0R_EL2_Type_P17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_ICH_AP0R_Type_P17 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_ICH_AP1R_EL2_Type_P17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_ICH_AP1R_Type_P17 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMCNTENCLR_Type_P17 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMCNTENSET_EL0_Type_P17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMCNTENSET_Type_P17 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMCNTEN_Type_P17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMINTENCLR_EL1_Type_P17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMINTENCLR_Type_P17 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMINTENSET_EL1_Type_P17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMINTENSET_Type_P17 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMINTEN_Type_P17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMOVSCLR_EL0_Type_P17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMOVSR_Type_P17 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMOVSSET_EL0_Type_P17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMOVSSET_Type_P17 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMOVS_Type_P17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMSWINC_EL0_Type_P17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMSWINC_Type_P17 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMUACR_EL1_Type_P17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMZR_EL0_Type_P17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_SPMACCESSR_EL1_Type_P17 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 35 34)

def _get_SPMACCESSR_EL2_Type_P17 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 35 34)

def _get_SPMACCESSR_EL3_Type_P17 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 35 34)

def _get_PMCNTENCLR_EL0_Type_P18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_PMCNTENCLR_EL0_Type_P18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_ICH_AP0R_EL2_Type_P18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_ICH_AP0R_Type_P18 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_ICH_AP1R_EL2_Type_P18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_ICH_AP1R_Type_P18 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMCNTENCLR_Type_P18 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMCNTENSET_EL0_Type_P18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMCNTENSET_Type_P18 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMCNTEN_Type_P18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMINTENCLR_EL1_Type_P18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMINTENCLR_Type_P18 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMINTENSET_EL1_Type_P18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMINTENSET_Type_P18 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMINTEN_Type_P18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMOVSCLR_EL0_Type_P18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMOVSR_Type_P18 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMOVSSET_EL0_Type_P18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMOVSSET_Type_P18 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMOVS_Type_P18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMSWINC_EL0_Type_P18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMSWINC_Type_P18 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMUACR_EL1_Type_P18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMZR_EL0_Type_P18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_SPMACCESSR_EL1_Type_P18 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 36 x)

def _update_SPMACCESSR_EL2_Type_P18 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 36 x)

def _update_SPMACCESSR_EL3_Type_P18 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 36 x)

def _get_ICH_AP0R_EL2_Type_P18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_ICH_AP0R_Type_P18 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_ICH_AP1R_EL2_Type_P18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_ICH_AP1R_Type_P18 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMCNTENCLR_Type_P18 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMCNTENSET_EL0_Type_P18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMCNTENSET_Type_P18 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMCNTEN_Type_P18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMINTENCLR_EL1_Type_P18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMINTENCLR_Type_P18 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMINTENSET_EL1_Type_P18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMINTENSET_Type_P18 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMINTEN_Type_P18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMOVSCLR_EL0_Type_P18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMOVSR_Type_P18 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMOVSSET_EL0_Type_P18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMOVSSET_Type_P18 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMOVS_Type_P18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMSWINC_EL0_Type_P18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMSWINC_Type_P18 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMUACR_EL1_Type_P18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMZR_EL0_Type_P18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_SPMACCESSR_EL1_Type_P18 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 37 36)

def _get_SPMACCESSR_EL2_Type_P18 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 37 36)

def _get_SPMACCESSR_EL3_Type_P18 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 37 36)

def _get_PMCNTENCLR_EL0_Type_P19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_PMCNTENCLR_EL0_Type_P19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_ICH_AP0R_EL2_Type_P19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_ICH_AP0R_Type_P19 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_ICH_AP1R_EL2_Type_P19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_ICH_AP1R_Type_P19 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMCNTENCLR_Type_P19 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMCNTENSET_EL0_Type_P19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMCNTENSET_Type_P19 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMCNTEN_Type_P19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMINTENCLR_EL1_Type_P19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMINTENCLR_Type_P19 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMINTENSET_EL1_Type_P19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMINTENSET_Type_P19 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMINTEN_Type_P19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMOVSCLR_EL0_Type_P19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMOVSR_Type_P19 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMOVSSET_EL0_Type_P19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMOVSSET_Type_P19 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMOVS_Type_P19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMSWINC_EL0_Type_P19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMSWINC_Type_P19 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMUACR_EL1_Type_P19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMZR_EL0_Type_P19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_SPMACCESSR_EL1_Type_P19 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 38 x)

def _update_SPMACCESSR_EL2_Type_P19 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 38 x)

def _update_SPMACCESSR_EL3_Type_P19 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 38 x)

def _get_ICH_AP0R_EL2_Type_P19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_ICH_AP0R_Type_P19 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_ICH_AP1R_EL2_Type_P19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_ICH_AP1R_Type_P19 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMCNTENCLR_Type_P19 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMCNTENSET_EL0_Type_P19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMCNTENSET_Type_P19 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMCNTEN_Type_P19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMINTENCLR_EL1_Type_P19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMINTENCLR_Type_P19 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMINTENSET_EL1_Type_P19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMINTENSET_Type_P19 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMINTEN_Type_P19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMOVSCLR_EL0_Type_P19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMOVSR_Type_P19 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMOVSSET_EL0_Type_P19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMOVSSET_Type_P19 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMOVS_Type_P19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMSWINC_EL0_Type_P19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMSWINC_Type_P19 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMUACR_EL1_Type_P19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMZR_EL0_Type_P19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_SPMACCESSR_EL1_Type_P19 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 39 38)

def _get_SPMACCESSR_EL2_Type_P19 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 39 38)

def _get_SPMACCESSR_EL3_Type_P19 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 39 38)

def _get_PMCNTENCLR_EL0_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_PMCNTENCLR_EL0_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_AMCNTENCLR0_EL0_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_AMCNTENCLR0_Type_P2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_AMCNTENCLR1_EL0_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_AMCNTENCLR1_Type_P2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_AMCNTENSET0_EL0_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_AMCNTENSET0_Type_P2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_AMCNTENSET1_EL0_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_AMCNTENSET1_Type_P2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICH_AP0R_EL2_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICH_AP0R_Type_P2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICH_AP1R_EL2_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICH_AP1R_Type_P2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMCNTENCLR_Type_P2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMCNTENSET_EL0_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMCNTENSET_Type_P2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMCNTEN_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMINTENCLR_EL1_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMINTENCLR_Type_P2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMINTENSET_EL1_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMINTENSET_Type_P2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMINTEN_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMOVSCLR_EL0_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMOVSR_Type_P2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMOVSSET_EL0_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMOVSSET_Type_P2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMOVS_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMSWINC_EL0_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMSWINC_Type_P2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMUACR_EL1_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMZR_EL0_Type_P2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_SMPRIMAP_EL2_Type_P2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_SPMACCESSR_EL1_Type_P2 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _update_SPMACCESSR_EL2_Type_P2 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _update_SPMACCESSR_EL3_Type_P2 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _get_AMCNTENCLR0_EL0_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_AMCNTENCLR0_Type_P2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_AMCNTENCLR1_EL0_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_AMCNTENCLR1_Type_P2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_AMCNTENSET0_EL0_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_AMCNTENSET0_Type_P2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_AMCNTENSET1_EL0_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_AMCNTENSET1_Type_P2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICH_AP0R_EL2_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICH_AP0R_Type_P2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICH_AP1R_EL2_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_ICH_AP1R_Type_P2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMCNTENCLR_Type_P2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMCNTENSET_EL0_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMCNTENSET_Type_P2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMCNTEN_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMINTENCLR_EL1_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMINTENCLR_Type_P2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMINTENSET_EL1_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMINTENSET_Type_P2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMINTEN_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMOVSCLR_EL0_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMOVSR_Type_P2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMOVSSET_EL0_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMOVSSET_Type_P2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMOVS_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMSWINC_EL0_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMSWINC_Type_P2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMUACR_EL1_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMZR_EL0_Type_P2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_SMPRIMAP_EL2_Type_P2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_SPMACCESSR_EL1_Type_P2 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _get_SPMACCESSR_EL2_Type_P2 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _get_SPMACCESSR_EL3_Type_P2 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _get_PMCNTENCLR_EL0_Type_P20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_PMCNTENCLR_EL0_Type_P20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_ICH_AP0R_EL2_Type_P20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_ICH_AP0R_Type_P20 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_ICH_AP1R_EL2_Type_P20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_ICH_AP1R_Type_P20 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMCNTENCLR_Type_P20 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMCNTENSET_EL0_Type_P20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMCNTENSET_Type_P20 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMCNTEN_Type_P20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMINTENCLR_EL1_Type_P20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMINTENCLR_Type_P20 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMINTENSET_EL1_Type_P20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMINTENSET_Type_P20 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMINTEN_Type_P20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMOVSCLR_EL0_Type_P20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMOVSR_Type_P20 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMOVSSET_EL0_Type_P20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMOVSSET_Type_P20 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMOVS_Type_P20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMSWINC_EL0_Type_P20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMSWINC_Type_P20 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMUACR_EL1_Type_P20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMZR_EL0_Type_P20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_SPMACCESSR_EL1_Type_P20 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 40 x)

def _update_SPMACCESSR_EL2_Type_P20 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 40 x)

def _update_SPMACCESSR_EL3_Type_P20 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 40 x)

def _get_ICH_AP0R_EL2_Type_P20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_ICH_AP0R_Type_P20 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_ICH_AP1R_EL2_Type_P20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_ICH_AP1R_Type_P20 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMCNTENCLR_Type_P20 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMCNTENSET_EL0_Type_P20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMCNTENSET_Type_P20 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMCNTEN_Type_P20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMINTENCLR_EL1_Type_P20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMINTENCLR_Type_P20 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMINTENSET_EL1_Type_P20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMINTENSET_Type_P20 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMINTEN_Type_P20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMOVSCLR_EL0_Type_P20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMOVSR_Type_P20 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMOVSSET_EL0_Type_P20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMOVSSET_Type_P20 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMOVS_Type_P20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMSWINC_EL0_Type_P20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMSWINC_Type_P20 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMUACR_EL1_Type_P20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMZR_EL0_Type_P20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_SPMACCESSR_EL1_Type_P20 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 41 40)

def _get_SPMACCESSR_EL2_Type_P20 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 41 40)

def _get_SPMACCESSR_EL3_Type_P20 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 41 40)

def _get_PMCNTENCLR_EL0_Type_P21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_PMCNTENCLR_EL0_Type_P21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_ICH_AP0R_EL2_Type_P21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_ICH_AP0R_Type_P21 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_ICH_AP1R_EL2_Type_P21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_ICH_AP1R_Type_P21 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMCNTENCLR_Type_P21 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMCNTENSET_EL0_Type_P21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMCNTENSET_Type_P21 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMCNTEN_Type_P21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMINTENCLR_EL1_Type_P21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMINTENCLR_Type_P21 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMINTENSET_EL1_Type_P21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMINTENSET_Type_P21 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMINTEN_Type_P21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMOVSCLR_EL0_Type_P21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMOVSR_Type_P21 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMOVSSET_EL0_Type_P21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMOVSSET_Type_P21 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMOVS_Type_P21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMSWINC_EL0_Type_P21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMSWINC_Type_P21 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMUACR_EL1_Type_P21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMZR_EL0_Type_P21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_SPMACCESSR_EL1_Type_P21 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 42 x)

def _update_SPMACCESSR_EL2_Type_P21 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 42 x)

def _update_SPMACCESSR_EL3_Type_P21 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 42 x)

def _get_ICH_AP0R_EL2_Type_P21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_ICH_AP0R_Type_P21 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_ICH_AP1R_EL2_Type_P21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_ICH_AP1R_Type_P21 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMCNTENCLR_Type_P21 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMCNTENSET_EL0_Type_P21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMCNTENSET_Type_P21 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMCNTEN_Type_P21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMINTENCLR_EL1_Type_P21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMINTENCLR_Type_P21 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMINTENSET_EL1_Type_P21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMINTENSET_Type_P21 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMINTEN_Type_P21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMOVSCLR_EL0_Type_P21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMOVSR_Type_P21 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMOVSSET_EL0_Type_P21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMOVSSET_Type_P21 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMOVS_Type_P21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMSWINC_EL0_Type_P21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMSWINC_Type_P21 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMUACR_EL1_Type_P21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMZR_EL0_Type_P21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_SPMACCESSR_EL1_Type_P21 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 43 42)

def _get_SPMACCESSR_EL2_Type_P21 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 43 42)

def _get_SPMACCESSR_EL3_Type_P21 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 43 42)

def _get_PMCNTENCLR_EL0_Type_P22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_PMCNTENCLR_EL0_Type_P22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_ICH_AP0R_EL2_Type_P22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_ICH_AP0R_Type_P22 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_ICH_AP1R_EL2_Type_P22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_ICH_AP1R_Type_P22 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMCNTENCLR_Type_P22 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMCNTENSET_EL0_Type_P22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMCNTENSET_Type_P22 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMCNTEN_Type_P22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMINTENCLR_EL1_Type_P22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMINTENCLR_Type_P22 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMINTENSET_EL1_Type_P22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMINTENSET_Type_P22 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMINTEN_Type_P22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMOVSCLR_EL0_Type_P22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMOVSR_Type_P22 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMOVSSET_EL0_Type_P22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMOVSSET_Type_P22 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMOVS_Type_P22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMSWINC_EL0_Type_P22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMSWINC_Type_P22 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMUACR_EL1_Type_P22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMZR_EL0_Type_P22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_SPMACCESSR_EL1_Type_P22 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 44 x)

def _update_SPMACCESSR_EL2_Type_P22 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 44 x)

def _update_SPMACCESSR_EL3_Type_P22 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 44 x)

def _get_ICH_AP0R_EL2_Type_P22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_ICH_AP0R_Type_P22 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_ICH_AP1R_EL2_Type_P22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_ICH_AP1R_Type_P22 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMCNTENCLR_Type_P22 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMCNTENSET_EL0_Type_P22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMCNTENSET_Type_P22 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMCNTEN_Type_P22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMINTENCLR_EL1_Type_P22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMINTENCLR_Type_P22 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMINTENSET_EL1_Type_P22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMINTENSET_Type_P22 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMINTEN_Type_P22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMOVSCLR_EL0_Type_P22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMOVSR_Type_P22 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMOVSSET_EL0_Type_P22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMOVSSET_Type_P22 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMOVS_Type_P22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMSWINC_EL0_Type_P22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMSWINC_Type_P22 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMUACR_EL1_Type_P22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMZR_EL0_Type_P22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_SPMACCESSR_EL1_Type_P22 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 45 44)

def _get_SPMACCESSR_EL2_Type_P22 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 45 44)

def _get_SPMACCESSR_EL3_Type_P22 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 45 44)

def _get_PMCNTENCLR_EL0_Type_P23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_PMCNTENCLR_EL0_Type_P23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_ICH_AP0R_EL2_Type_P23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_ICH_AP0R_Type_P23 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_ICH_AP1R_EL2_Type_P23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_ICH_AP1R_Type_P23 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMCNTENCLR_Type_P23 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMCNTENSET_EL0_Type_P23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMCNTENSET_Type_P23 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMCNTEN_Type_P23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMINTENCLR_EL1_Type_P23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMINTENCLR_Type_P23 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMINTENSET_EL1_Type_P23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMINTENSET_Type_P23 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMINTEN_Type_P23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMOVSCLR_EL0_Type_P23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMOVSR_Type_P23 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMOVSSET_EL0_Type_P23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMOVSSET_Type_P23 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMOVS_Type_P23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMSWINC_EL0_Type_P23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMSWINC_Type_P23 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMUACR_EL1_Type_P23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMZR_EL0_Type_P23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_SPMACCESSR_EL1_Type_P23 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 46 x)

def _update_SPMACCESSR_EL2_Type_P23 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 46 x)

def _update_SPMACCESSR_EL3_Type_P23 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 46 x)

def _get_ICH_AP0R_EL2_Type_P23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_ICH_AP0R_Type_P23 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_ICH_AP1R_EL2_Type_P23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_ICH_AP1R_Type_P23 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMCNTENCLR_Type_P23 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMCNTENSET_EL0_Type_P23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMCNTENSET_Type_P23 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMCNTEN_Type_P23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMINTENCLR_EL1_Type_P23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMINTENCLR_Type_P23 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMINTENSET_EL1_Type_P23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMINTENSET_Type_P23 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMINTEN_Type_P23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMOVSCLR_EL0_Type_P23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMOVSR_Type_P23 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMOVSSET_EL0_Type_P23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMOVSSET_Type_P23 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMOVS_Type_P23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMSWINC_EL0_Type_P23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMSWINC_Type_P23 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMUACR_EL1_Type_P23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMZR_EL0_Type_P23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_SPMACCESSR_EL1_Type_P23 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 47 46)

def _get_SPMACCESSR_EL2_Type_P23 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 47 46)

def _get_SPMACCESSR_EL3_Type_P23 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 47 46)

def _get_PMCNTENCLR_EL0_Type_P24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_PMCNTENCLR_EL0_Type_P24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_ICH_AP0R_EL2_Type_P24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_ICH_AP0R_Type_P24 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_ICH_AP1R_EL2_Type_P24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_ICH_AP1R_Type_P24 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMCNTENCLR_Type_P24 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMCNTENSET_EL0_Type_P24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMCNTENSET_Type_P24 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMCNTEN_Type_P24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMINTENCLR_EL1_Type_P24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMINTENCLR_Type_P24 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMINTENSET_EL1_Type_P24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMINTENSET_Type_P24 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMINTEN_Type_P24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMOVSCLR_EL0_Type_P24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMOVSR_Type_P24 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMOVSSET_EL0_Type_P24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMOVSSET_Type_P24 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMOVS_Type_P24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMSWINC_EL0_Type_P24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMSWINC_Type_P24 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMUACR_EL1_Type_P24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMZR_EL0_Type_P24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_SPMACCESSR_EL1_Type_P24 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 48 x)

def _update_SPMACCESSR_EL2_Type_P24 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 48 x)

def _update_SPMACCESSR_EL3_Type_P24 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 48 x)

def _get_ICH_AP0R_EL2_Type_P24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_ICH_AP0R_Type_P24 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_ICH_AP1R_EL2_Type_P24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_ICH_AP1R_Type_P24 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMCNTENCLR_Type_P24 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMCNTENSET_EL0_Type_P24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMCNTENSET_Type_P24 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMCNTEN_Type_P24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMINTENCLR_EL1_Type_P24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMINTENCLR_Type_P24 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMINTENSET_EL1_Type_P24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMINTENSET_Type_P24 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMINTEN_Type_P24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMOVSCLR_EL0_Type_P24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMOVSR_Type_P24 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMOVSSET_EL0_Type_P24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMOVSSET_Type_P24 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMOVS_Type_P24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMSWINC_EL0_Type_P24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMSWINC_Type_P24 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMUACR_EL1_Type_P24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMZR_EL0_Type_P24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_SPMACCESSR_EL1_Type_P24 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 49 48)

def _get_SPMACCESSR_EL2_Type_P24 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 49 48)

def _get_SPMACCESSR_EL3_Type_P24 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 49 48)

def _get_PMCNTENCLR_EL0_Type_P25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_PMCNTENCLR_EL0_Type_P25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_ICH_AP0R_EL2_Type_P25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_ICH_AP0R_Type_P25 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_ICH_AP1R_EL2_Type_P25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_ICH_AP1R_Type_P25 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMCNTENCLR_Type_P25 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMCNTENSET_EL0_Type_P25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMCNTENSET_Type_P25 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMCNTEN_Type_P25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMINTENCLR_EL1_Type_P25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMINTENCLR_Type_P25 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMINTENSET_EL1_Type_P25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMINTENSET_Type_P25 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMINTEN_Type_P25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMOVSCLR_EL0_Type_P25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMOVSR_Type_P25 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMOVSSET_EL0_Type_P25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMOVSSET_Type_P25 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMOVS_Type_P25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMSWINC_EL0_Type_P25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMSWINC_Type_P25 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMUACR_EL1_Type_P25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMZR_EL0_Type_P25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_SPMACCESSR_EL1_Type_P25 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 50 x)

def _update_SPMACCESSR_EL2_Type_P25 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 50 x)

def _update_SPMACCESSR_EL3_Type_P25 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 50 x)

def _get_ICH_AP0R_EL2_Type_P25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_ICH_AP0R_Type_P25 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_ICH_AP1R_EL2_Type_P25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_ICH_AP1R_Type_P25 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMCNTENCLR_Type_P25 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMCNTENSET_EL0_Type_P25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMCNTENSET_Type_P25 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMCNTEN_Type_P25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMINTENCLR_EL1_Type_P25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMINTENCLR_Type_P25 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMINTENSET_EL1_Type_P25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMINTENSET_Type_P25 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMINTEN_Type_P25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMOVSCLR_EL0_Type_P25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMOVSR_Type_P25 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMOVSSET_EL0_Type_P25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMOVSSET_Type_P25 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMOVS_Type_P25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMSWINC_EL0_Type_P25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMSWINC_Type_P25 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMUACR_EL1_Type_P25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMZR_EL0_Type_P25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_SPMACCESSR_EL1_Type_P25 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 51 50)

def _get_SPMACCESSR_EL2_Type_P25 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 51 50)

def _get_SPMACCESSR_EL3_Type_P25 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 51 50)

def _get_PMCNTENCLR_EL0_Type_P26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_PMCNTENCLR_EL0_Type_P26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_ICH_AP0R_EL2_Type_P26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_ICH_AP0R_Type_P26 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_ICH_AP1R_EL2_Type_P26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_ICH_AP1R_Type_P26 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMCNTENCLR_Type_P26 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMCNTENSET_EL0_Type_P26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMCNTENSET_Type_P26 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMCNTEN_Type_P26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMINTENCLR_EL1_Type_P26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMINTENCLR_Type_P26 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMINTENSET_EL1_Type_P26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMINTENSET_Type_P26 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMINTEN_Type_P26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMOVSCLR_EL0_Type_P26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMOVSR_Type_P26 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMOVSSET_EL0_Type_P26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMOVSSET_Type_P26 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMOVS_Type_P26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMSWINC_EL0_Type_P26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMSWINC_Type_P26 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMUACR_EL1_Type_P26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMZR_EL0_Type_P26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_SPMACCESSR_EL1_Type_P26 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 52 x)

def _update_SPMACCESSR_EL2_Type_P26 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 52 x)

def _update_SPMACCESSR_EL3_Type_P26 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 52 x)

def _get_ICH_AP0R_EL2_Type_P26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_ICH_AP0R_Type_P26 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_ICH_AP1R_EL2_Type_P26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_ICH_AP1R_Type_P26 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMCNTENCLR_Type_P26 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMCNTENSET_EL0_Type_P26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMCNTENSET_Type_P26 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMCNTEN_Type_P26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMINTENCLR_EL1_Type_P26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMINTENCLR_Type_P26 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMINTENSET_EL1_Type_P26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMINTENSET_Type_P26 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMINTEN_Type_P26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMOVSCLR_EL0_Type_P26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMOVSR_Type_P26 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMOVSSET_EL0_Type_P26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMOVSSET_Type_P26 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMOVS_Type_P26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMSWINC_EL0_Type_P26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMSWINC_Type_P26 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMUACR_EL1_Type_P26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMZR_EL0_Type_P26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_SPMACCESSR_EL1_Type_P26 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 53 52)

def _get_SPMACCESSR_EL2_Type_P26 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 53 52)

def _get_SPMACCESSR_EL3_Type_P26 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 53 52)

def _get_PMCNTENCLR_EL0_Type_P27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_PMCNTENCLR_EL0_Type_P27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_ICH_AP0R_EL2_Type_P27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_ICH_AP0R_Type_P27 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_ICH_AP1R_EL2_Type_P27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_ICH_AP1R_Type_P27 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMCNTENCLR_Type_P27 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMCNTENSET_EL0_Type_P27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMCNTENSET_Type_P27 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMCNTEN_Type_P27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMINTENCLR_EL1_Type_P27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMINTENCLR_Type_P27 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMINTENSET_EL1_Type_P27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMINTENSET_Type_P27 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMINTEN_Type_P27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMOVSCLR_EL0_Type_P27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMOVSR_Type_P27 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMOVSSET_EL0_Type_P27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMOVSSET_Type_P27 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMOVS_Type_P27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMSWINC_EL0_Type_P27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMSWINC_Type_P27 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMUACR_EL1_Type_P27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMZR_EL0_Type_P27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_SPMACCESSR_EL1_Type_P27 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 54 x)

def _update_SPMACCESSR_EL2_Type_P27 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 54 x)

def _update_SPMACCESSR_EL3_Type_P27 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 54 x)

def _get_ICH_AP0R_EL2_Type_P27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_ICH_AP0R_Type_P27 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_ICH_AP1R_EL2_Type_P27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_ICH_AP1R_Type_P27 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMCNTENCLR_Type_P27 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMCNTENSET_EL0_Type_P27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMCNTENSET_Type_P27 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMCNTEN_Type_P27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMINTENCLR_EL1_Type_P27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMINTENCLR_Type_P27 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMINTENSET_EL1_Type_P27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMINTENSET_Type_P27 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMINTEN_Type_P27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMOVSCLR_EL0_Type_P27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMOVSR_Type_P27 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMOVSSET_EL0_Type_P27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMOVSSET_Type_P27 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMOVS_Type_P27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMSWINC_EL0_Type_P27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMSWINC_Type_P27 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMUACR_EL1_Type_P27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMZR_EL0_Type_P27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_SPMACCESSR_EL1_Type_P27 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 55 54)

def _get_SPMACCESSR_EL2_Type_P27 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 55 54)

def _get_SPMACCESSR_EL3_Type_P27 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 55 54)

def _get_PMCNTENCLR_EL0_Type_P28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_PMCNTENCLR_EL0_Type_P28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_ICH_AP0R_EL2_Type_P28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_ICH_AP0R_Type_P28 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_ICH_AP1R_EL2_Type_P28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_ICH_AP1R_Type_P28 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMCNTENCLR_Type_P28 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMCNTENSET_EL0_Type_P28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMCNTENSET_Type_P28 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMCNTEN_Type_P28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMINTENCLR_EL1_Type_P28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMINTENCLR_Type_P28 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMINTENSET_EL1_Type_P28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMINTENSET_Type_P28 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMINTEN_Type_P28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMOVSCLR_EL0_Type_P28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMOVSR_Type_P28 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMOVSSET_EL0_Type_P28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMOVSSET_Type_P28 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMOVS_Type_P28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMSWINC_EL0_Type_P28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMSWINC_Type_P28 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMUACR_EL1_Type_P28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMZR_EL0_Type_P28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_SPMACCESSR_EL1_Type_P28 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 56 x)

def _update_SPMACCESSR_EL2_Type_P28 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 56 x)

def _update_SPMACCESSR_EL3_Type_P28 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 56 x)

def _get_ICH_AP0R_EL2_Type_P28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_ICH_AP0R_Type_P28 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_ICH_AP1R_EL2_Type_P28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_ICH_AP1R_Type_P28 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMCNTENCLR_Type_P28 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMCNTENSET_EL0_Type_P28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMCNTENSET_Type_P28 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMCNTEN_Type_P28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMINTENCLR_EL1_Type_P28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMINTENCLR_Type_P28 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMINTENSET_EL1_Type_P28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMINTENSET_Type_P28 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMINTEN_Type_P28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMOVSCLR_EL0_Type_P28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMOVSR_Type_P28 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMOVSSET_EL0_Type_P28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMOVSSET_Type_P28 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMOVS_Type_P28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMSWINC_EL0_Type_P28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMSWINC_Type_P28 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMUACR_EL1_Type_P28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMZR_EL0_Type_P28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_SPMACCESSR_EL1_Type_P28 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 57 56)

def _get_SPMACCESSR_EL2_Type_P28 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 57 56)

def _get_SPMACCESSR_EL3_Type_P28 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 57 56)

def _get_PMCNTENCLR_EL0_Type_P29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_PMCNTENCLR_EL0_Type_P29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_ICH_AP0R_EL2_Type_P29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_ICH_AP0R_Type_P29 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_ICH_AP1R_EL2_Type_P29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_ICH_AP1R_Type_P29 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMCNTENCLR_Type_P29 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMCNTENSET_EL0_Type_P29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMCNTENSET_Type_P29 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMCNTEN_Type_P29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMINTENCLR_EL1_Type_P29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMINTENCLR_Type_P29 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMINTENSET_EL1_Type_P29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMINTENSET_Type_P29 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMINTEN_Type_P29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMOVSCLR_EL0_Type_P29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMOVSR_Type_P29 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMOVSSET_EL0_Type_P29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMOVSSET_Type_P29 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMOVS_Type_P29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMSWINC_EL0_Type_P29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMSWINC_Type_P29 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMUACR_EL1_Type_P29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMZR_EL0_Type_P29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_SPMACCESSR_EL1_Type_P29 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 58 x)

def _update_SPMACCESSR_EL2_Type_P29 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 58 x)

def _update_SPMACCESSR_EL3_Type_P29 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 58 x)

def _get_ICH_AP0R_EL2_Type_P29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_ICH_AP0R_Type_P29 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_ICH_AP1R_EL2_Type_P29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_ICH_AP1R_Type_P29 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMCNTENCLR_Type_P29 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMCNTENSET_EL0_Type_P29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMCNTENSET_Type_P29 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMCNTEN_Type_P29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMINTENCLR_EL1_Type_P29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMINTENCLR_Type_P29 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMINTENSET_EL1_Type_P29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMINTENSET_Type_P29 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMINTEN_Type_P29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMOVSCLR_EL0_Type_P29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMOVSR_Type_P29 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMOVSSET_EL0_Type_P29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMOVSSET_Type_P29 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMOVS_Type_P29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMSWINC_EL0_Type_P29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMSWINC_Type_P29 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMUACR_EL1_Type_P29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMZR_EL0_Type_P29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_SPMACCESSR_EL1_Type_P29 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 59 58)

def _get_SPMACCESSR_EL2_Type_P29 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 59 58)

def _get_SPMACCESSR_EL3_Type_P29 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 59 58)

def _get_PMCNTENCLR_EL0_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_PMCNTENCLR_EL0_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_AMCNTENCLR0_EL0_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_AMCNTENCLR0_Type_P3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_AMCNTENCLR1_EL0_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_AMCNTENCLR1_Type_P3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_AMCNTENSET0_EL0_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_AMCNTENSET0_Type_P3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_AMCNTENSET1_EL0_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_AMCNTENSET1_Type_P3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ICH_AP0R_EL2_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ICH_AP0R_Type_P3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ICH_AP1R_EL2_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ICH_AP1R_Type_P3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMCNTENCLR_Type_P3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMCNTENSET_EL0_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMCNTENSET_Type_P3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMCNTEN_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMINTENCLR_EL1_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMINTENCLR_Type_P3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMINTENSET_EL1_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMINTENSET_Type_P3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMINTEN_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMOVSCLR_EL0_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMOVSR_Type_P3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMOVSSET_EL0_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMOVSSET_Type_P3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMOVS_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMSWINC_EL0_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMSWINC_Type_P3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMUACR_EL1_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMZR_EL0_Type_P3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_SMPRIMAP_EL2_Type_P3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_SPMACCESSR_EL1_Type_P3 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _update_SPMACCESSR_EL2_Type_P3 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _update_SPMACCESSR_EL3_Type_P3 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _get_AMCNTENCLR0_EL0_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_AMCNTENCLR0_Type_P3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_AMCNTENCLR1_EL0_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_AMCNTENCLR1_Type_P3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_AMCNTENSET0_EL0_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_AMCNTENSET0_Type_P3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_AMCNTENSET1_EL0_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_AMCNTENSET1_Type_P3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICH_AP0R_EL2_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICH_AP0R_Type_P3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICH_AP1R_EL2_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_ICH_AP1R_Type_P3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMCNTENCLR_Type_P3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMCNTENSET_EL0_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMCNTENSET_Type_P3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMCNTEN_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMINTENCLR_EL1_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMINTENCLR_Type_P3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMINTENSET_EL1_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMINTENSET_Type_P3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMINTEN_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMOVSCLR_EL0_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMOVSR_Type_P3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMOVSSET_EL0_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMOVSSET_Type_P3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMOVS_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMSWINC_EL0_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMSWINC_Type_P3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMUACR_EL1_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMZR_EL0_Type_P3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_SMPRIMAP_EL2_Type_P3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_SPMACCESSR_EL1_Type_P3 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def _get_SPMACCESSR_EL2_Type_P3 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def _get_SPMACCESSR_EL3_Type_P3 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def _get_PMCNTENCLR_EL0_Type_P30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_PMCNTENCLR_EL0_Type_P30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_ICH_AP0R_EL2_Type_P30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_ICH_AP0R_Type_P30 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_ICH_AP1R_EL2_Type_P30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_ICH_AP1R_Type_P30 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMCNTENCLR_Type_P30 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMCNTENSET_EL0_Type_P30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMCNTENSET_Type_P30 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMCNTEN_Type_P30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMINTENCLR_EL1_Type_P30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMINTENCLR_Type_P30 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMINTENSET_EL1_Type_P30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMINTENSET_Type_P30 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMINTEN_Type_P30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMOVSCLR_EL0_Type_P30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMOVSR_Type_P30 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMOVSSET_EL0_Type_P30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMOVSSET_Type_P30 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMOVS_Type_P30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMSWINC_EL0_Type_P30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMSWINC_Type_P30 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMUACR_EL1_Type_P30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMZR_EL0_Type_P30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_SPMACCESSR_EL1_Type_P30 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 60 x)

def _update_SPMACCESSR_EL2_Type_P30 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 60 x)

def _update_SPMACCESSR_EL3_Type_P30 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 60 x)

def _get_ICH_AP0R_EL2_Type_P30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_ICH_AP0R_Type_P30 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_ICH_AP1R_EL2_Type_P30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_ICH_AP1R_Type_P30 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMCNTENCLR_Type_P30 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMCNTENSET_EL0_Type_P30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMCNTENSET_Type_P30 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMCNTEN_Type_P30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMINTENCLR_EL1_Type_P30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMINTENCLR_Type_P30 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMINTENSET_EL1_Type_P30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMINTENSET_Type_P30 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMINTEN_Type_P30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMOVSCLR_EL0_Type_P30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMOVSR_Type_P30 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMOVSSET_EL0_Type_P30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMOVSSET_Type_P30 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMOVS_Type_P30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMSWINC_EL0_Type_P30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMSWINC_Type_P30 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMUACR_EL1_Type_P30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMZR_EL0_Type_P30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_SPMACCESSR_EL1_Type_P30 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 61 60)

def _get_SPMACCESSR_EL2_Type_P30 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 61 60)

def _get_SPMACCESSR_EL3_Type_P30 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 61 60)

def _get_PMCNTENCLR_EL0_Type_P4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_PMCNTENCLR_EL0_Type_P4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_AMCNTENCLR1_EL0_Type_P4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_AMCNTENCLR1_Type_P4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_AMCNTENSET1_EL0_Type_P4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_AMCNTENSET1_Type_P4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_ICH_AP0R_EL2_Type_P4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_ICH_AP0R_Type_P4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_ICH_AP1R_EL2_Type_P4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_ICH_AP1R_Type_P4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMCNTENCLR_Type_P4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMCNTENSET_EL0_Type_P4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMCNTENSET_Type_P4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMCNTEN_Type_P4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMINTENCLR_EL1_Type_P4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMINTENCLR_Type_P4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMINTENSET_EL1_Type_P4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMINTENSET_Type_P4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMINTEN_Type_P4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMOVSCLR_EL0_Type_P4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMOVSR_Type_P4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMOVSSET_EL0_Type_P4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMOVSSET_Type_P4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMOVS_Type_P4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMSWINC_EL0_Type_P4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMSWINC_Type_P4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMUACR_EL1_Type_P4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMZR_EL0_Type_P4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_SMPRIMAP_EL2_Type_P4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_SPMACCESSR_EL1_Type_P4 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def _update_SPMACCESSR_EL2_Type_P4 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def _update_SPMACCESSR_EL3_Type_P4 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def _get_AMCNTENCLR1_EL0_Type_P4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_AMCNTENCLR1_Type_P4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_AMCNTENSET1_EL0_Type_P4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_AMCNTENSET1_Type_P4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_ICH_AP0R_EL2_Type_P4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_ICH_AP0R_Type_P4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_ICH_AP1R_EL2_Type_P4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_ICH_AP1R_Type_P4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMCNTENCLR_Type_P4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMCNTENSET_EL0_Type_P4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMCNTENSET_Type_P4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMCNTEN_Type_P4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMINTENCLR_EL1_Type_P4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMINTENCLR_Type_P4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMINTENSET_EL1_Type_P4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMINTENSET_Type_P4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMINTEN_Type_P4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMOVSCLR_EL0_Type_P4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMOVSR_Type_P4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMOVSSET_EL0_Type_P4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMOVSSET_Type_P4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMOVS_Type_P4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMSWINC_EL0_Type_P4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMSWINC_Type_P4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMUACR_EL1_Type_P4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMZR_EL0_Type_P4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_SMPRIMAP_EL2_Type_P4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_SPMACCESSR_EL1_Type_P4 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)

def _get_SPMACCESSR_EL2_Type_P4 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)

def _get_SPMACCESSR_EL3_Type_P4 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)

def _get_PMCNTENCLR_EL0_Type_P5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_PMCNTENCLR_EL0_Type_P5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_AMCNTENCLR1_EL0_Type_P5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_AMCNTENCLR1_Type_P5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_AMCNTENSET1_EL0_Type_P5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_AMCNTENSET1_Type_P5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_ICH_AP0R_EL2_Type_P5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_ICH_AP0R_Type_P5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_ICH_AP1R_EL2_Type_P5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_ICH_AP1R_Type_P5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMCNTENCLR_Type_P5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMCNTENSET_EL0_Type_P5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMCNTENSET_Type_P5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMCNTEN_Type_P5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMINTENCLR_EL1_Type_P5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMINTENCLR_Type_P5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMINTENSET_EL1_Type_P5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMINTENSET_Type_P5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMINTEN_Type_P5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMOVSCLR_EL0_Type_P5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMOVSR_Type_P5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMOVSSET_EL0_Type_P5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMOVSSET_Type_P5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMOVS_Type_P5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMSWINC_EL0_Type_P5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMSWINC_Type_P5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMUACR_EL1_Type_P5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMZR_EL0_Type_P5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SMPRIMAP_EL2_Type_P5 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_SPMACCESSR_EL1_Type_P5 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_SPMACCESSR_EL2_Type_P5 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_SPMACCESSR_EL3_Type_P5 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _get_AMCNTENCLR1_EL0_Type_P5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_AMCNTENCLR1_Type_P5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_AMCNTENSET1_EL0_Type_P5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_AMCNTENSET1_Type_P5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_ICH_AP0R_EL2_Type_P5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_ICH_AP0R_Type_P5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_ICH_AP1R_EL2_Type_P5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_ICH_AP1R_Type_P5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMCNTENCLR_Type_P5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMCNTENSET_EL0_Type_P5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMCNTENSET_Type_P5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMCNTEN_Type_P5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMINTENCLR_EL1_Type_P5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMINTENCLR_Type_P5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMINTENSET_EL1_Type_P5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMINTENSET_Type_P5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMINTEN_Type_P5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMOVSCLR_EL0_Type_P5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMOVSR_Type_P5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMOVSSET_EL0_Type_P5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMOVSSET_Type_P5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMOVS_Type_P5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMSWINC_EL0_Type_P5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMSWINC_Type_P5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMUACR_EL1_Type_P5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMZR_EL0_Type_P5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_SMPRIMAP_EL2_Type_P5 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_SPMACCESSR_EL1_Type_P5 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _get_SPMACCESSR_EL2_Type_P5 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _get_SPMACCESSR_EL3_Type_P5 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _get_PMCNTENCLR_EL0_Type_P6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_PMCNTENCLR_EL0_Type_P6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_AMCNTENCLR1_EL0_Type_P6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_AMCNTENCLR1_Type_P6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_AMCNTENSET1_EL0_Type_P6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_AMCNTENSET1_Type_P6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ICH_AP0R_EL2_Type_P6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ICH_AP0R_Type_P6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ICH_AP1R_EL2_Type_P6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ICH_AP1R_Type_P6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMCNTENCLR_Type_P6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMCNTENSET_EL0_Type_P6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMCNTENSET_Type_P6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMCNTEN_Type_P6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMINTENCLR_EL1_Type_P6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMINTENCLR_Type_P6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMINTENSET_EL1_Type_P6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMINTENSET_Type_P6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMINTEN_Type_P6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMOVSCLR_EL0_Type_P6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMOVSR_Type_P6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMOVSSET_EL0_Type_P6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMOVSSET_Type_P6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMOVS_Type_P6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMSWINC_EL0_Type_P6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMSWINC_Type_P6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMUACR_EL1_Type_P6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMZR_EL0_Type_P6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SMPRIMAP_EL2_Type_P6 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_SPMACCESSR_EL1_Type_P6 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _update_SPMACCESSR_EL2_Type_P6 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _update_SPMACCESSR_EL3_Type_P6 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _get_AMCNTENCLR1_EL0_Type_P6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_AMCNTENCLR1_Type_P6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_AMCNTENSET1_EL0_Type_P6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_AMCNTENSET1_Type_P6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ICH_AP0R_EL2_Type_P6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ICH_AP0R_Type_P6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ICH_AP1R_EL2_Type_P6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ICH_AP1R_Type_P6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMCNTENCLR_Type_P6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMCNTENSET_EL0_Type_P6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMCNTENSET_Type_P6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMCNTEN_Type_P6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMINTENCLR_EL1_Type_P6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMINTENCLR_Type_P6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMINTENSET_EL1_Type_P6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMINTENSET_Type_P6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMINTEN_Type_P6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMOVSCLR_EL0_Type_P6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMOVSR_Type_P6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMOVSSET_EL0_Type_P6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMOVSSET_Type_P6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMOVS_Type_P6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMSWINC_EL0_Type_P6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMSWINC_Type_P6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMUACR_EL1_Type_P6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMZR_EL0_Type_P6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_SMPRIMAP_EL2_Type_P6 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_SPMACCESSR_EL1_Type_P6 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)

def _get_SPMACCESSR_EL2_Type_P6 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)

def _get_SPMACCESSR_EL3_Type_P6 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)

def _get_PMCNTENCLR_EL0_Type_P7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_PMCNTENCLR_EL0_Type_P7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_AMCNTENCLR1_EL0_Type_P7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_AMCNTENCLR1_Type_P7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_AMCNTENSET1_EL0_Type_P7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_AMCNTENSET1_Type_P7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_ICH_AP0R_EL2_Type_P7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_ICH_AP0R_Type_P7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_ICH_AP1R_EL2_Type_P7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_ICH_AP1R_Type_P7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMCNTENCLR_Type_P7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMCNTENSET_EL0_Type_P7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMCNTENSET_Type_P7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMCNTEN_Type_P7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMINTENCLR_EL1_Type_P7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMINTENCLR_Type_P7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMINTENSET_EL1_Type_P7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMINTENSET_Type_P7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMINTEN_Type_P7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMOVSCLR_EL0_Type_P7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMOVSR_Type_P7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMOVSSET_EL0_Type_P7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMOVSSET_Type_P7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMOVS_Type_P7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMSWINC_EL0_Type_P7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMSWINC_Type_P7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMUACR_EL1_Type_P7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMZR_EL0_Type_P7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SMPRIMAP_EL2_Type_P7 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_SPMACCESSR_EL1_Type_P7 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_SPMACCESSR_EL2_Type_P7 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_SPMACCESSR_EL3_Type_P7 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _get_AMCNTENCLR1_EL0_Type_P7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_AMCNTENCLR1_Type_P7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_AMCNTENSET1_EL0_Type_P7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_AMCNTENSET1_Type_P7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_ICH_AP0R_EL2_Type_P7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_ICH_AP0R_Type_P7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_ICH_AP1R_EL2_Type_P7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_ICH_AP1R_Type_P7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMCNTENCLR_Type_P7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMCNTENSET_EL0_Type_P7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMCNTENSET_Type_P7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMCNTEN_Type_P7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMINTENCLR_EL1_Type_P7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMINTENCLR_Type_P7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMINTENSET_EL1_Type_P7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMINTENSET_Type_P7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMINTEN_Type_P7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMOVSCLR_EL0_Type_P7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMOVSR_Type_P7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMOVSSET_EL0_Type_P7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMOVSSET_Type_P7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMOVS_Type_P7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMSWINC_EL0_Type_P7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMSWINC_Type_P7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMUACR_EL1_Type_P7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMZR_EL0_Type_P7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SMPRIMAP_EL2_Type_P7 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_SPMACCESSR_EL1_Type_P7 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)

def _get_SPMACCESSR_EL2_Type_P7 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)

def _get_SPMACCESSR_EL3_Type_P7 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)

def _get_PMCNTENCLR_EL0_Type_P8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_PMCNTENCLR_EL0_Type_P8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_AMCNTENCLR1_EL0_Type_P8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_AMCNTENCLR1_Type_P8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_AMCNTENSET1_EL0_Type_P8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_AMCNTENSET1_Type_P8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_ICH_AP0R_EL2_Type_P8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_ICH_AP0R_Type_P8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_ICH_AP1R_EL2_Type_P8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_ICH_AP1R_Type_P8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMCNTENCLR_Type_P8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMCNTENSET_EL0_Type_P8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMCNTENSET_Type_P8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMCNTEN_Type_P8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMINTENCLR_EL1_Type_P8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMINTENCLR_Type_P8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMINTENSET_EL1_Type_P8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMINTENSET_Type_P8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMINTEN_Type_P8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMOVSCLR_EL0_Type_P8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMOVSR_Type_P8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMOVSSET_EL0_Type_P8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMOVSSET_Type_P8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMOVS_Type_P8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMSWINC_EL0_Type_P8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMSWINC_Type_P8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMUACR_EL1_Type_P8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMZR_EL0_Type_P8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_SMPRIMAP_EL2_Type_P8 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_SPMACCESSR_EL1_Type_P8 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 16 x)

def _update_SPMACCESSR_EL2_Type_P8 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 16 x)

def _update_SPMACCESSR_EL3_Type_P8 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 16 x)

def _get_AMCNTENCLR1_EL0_Type_P8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_AMCNTENCLR1_Type_P8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_AMCNTENSET1_EL0_Type_P8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_AMCNTENSET1_Type_P8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_ICH_AP0R_EL2_Type_P8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_ICH_AP0R_Type_P8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_ICH_AP1R_EL2_Type_P8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_ICH_AP1R_Type_P8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMCNTENCLR_Type_P8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMCNTENSET_EL0_Type_P8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMCNTENSET_Type_P8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMCNTEN_Type_P8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMINTENCLR_EL1_Type_P8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMINTENCLR_Type_P8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMINTENSET_EL1_Type_P8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMINTENSET_Type_P8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMINTEN_Type_P8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMOVSCLR_EL0_Type_P8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMOVSR_Type_P8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMOVSSET_EL0_Type_P8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMOVSSET_Type_P8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMOVS_Type_P8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMSWINC_EL0_Type_P8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMSWINC_Type_P8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMUACR_EL1_Type_P8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMZR_EL0_Type_P8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_SMPRIMAP_EL2_Type_P8 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_SPMACCESSR_EL1_Type_P8 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 17 16)

def _get_SPMACCESSR_EL2_Type_P8 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 17 16)

def _get_SPMACCESSR_EL3_Type_P8 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 17 16)

def _get_PMCNTENCLR_EL0_Type_P9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_PMCNTENCLR_EL0_Type_P9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_AMCNTENCLR1_EL0_Type_P9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_AMCNTENCLR1_Type_P9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_AMCNTENSET1_EL0_Type_P9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_AMCNTENSET1_Type_P9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_ICH_AP0R_EL2_Type_P9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_ICH_AP0R_Type_P9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_ICH_AP1R_EL2_Type_P9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_ICH_AP1R_Type_P9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMCNTENCLR_Type_P9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMCNTENSET_EL0_Type_P9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMCNTENSET_Type_P9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMCNTEN_Type_P9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMINTENCLR_EL1_Type_P9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMINTENCLR_Type_P9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMINTENSET_EL1_Type_P9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMINTENSET_Type_P9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMINTEN_Type_P9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMOVSCLR_EL0_Type_P9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMOVSR_Type_P9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMOVSSET_EL0_Type_P9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMOVSSET_Type_P9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMOVS_Type_P9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMSWINC_EL0_Type_P9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMSWINC_Type_P9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMUACR_EL1_Type_P9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMZR_EL0_Type_P9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SMPRIMAP_EL2_Type_P9 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_SPMACCESSR_EL1_Type_P9 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 18 x)

def _update_SPMACCESSR_EL2_Type_P9 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 18 x)

def _update_SPMACCESSR_EL3_Type_P9 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 18 x)

def _get_AMCNTENCLR1_EL0_Type_P9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_AMCNTENCLR1_Type_P9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_AMCNTENSET1_EL0_Type_P9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_AMCNTENSET1_Type_P9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_ICH_AP0R_EL2_Type_P9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_ICH_AP0R_Type_P9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_ICH_AP1R_EL2_Type_P9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_ICH_AP1R_Type_P9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMCNTENCLR_Type_P9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMCNTENSET_EL0_Type_P9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMCNTENSET_Type_P9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMCNTEN_Type_P9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMINTENCLR_EL1_Type_P9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMINTENCLR_Type_P9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMINTENSET_EL1_Type_P9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMINTENSET_Type_P9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMINTEN_Type_P9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMOVSCLR_EL0_Type_P9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMOVSR_Type_P9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMOVSSET_EL0_Type_P9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMOVSSET_Type_P9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMOVS_Type_P9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMSWINC_EL0_Type_P9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMSWINC_Type_P9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMUACR_EL1_Type_P9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PMZR_EL0_Type_P9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_SMPRIMAP_EL2_Type_P9 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_SPMACCESSR_EL1_Type_P9 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 19 18)

def _get_SPMACCESSR_EL2_Type_P9 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 19 18)

def _get_SPMACCESSR_EL3_Type_P9 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 19 18)

def undefined_PMCNTENCLR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMCNTENCLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMCR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMCR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_PMCR_EL0_Type_D (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_DBGVCR32_EL2_Type_D (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_DBGVCR_Type_D (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_DSPSR_EL0_Type_D (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMCR_Type_D (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_SPSR_EL1_Type_D (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SPSR_EL2_Type_D (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SPSR_EL3_Type_D (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_DBGVCR32_EL2_Type_D (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_DBGVCR_Type_D (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_DSPSR_EL0_Type_D (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_SPSR_EL1_Type_D (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_SPSR_EL2_Type_D (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_SPSR_EL3_Type_D (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_PMCR_EL0_Type_DP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_ID_AA64ISAR0_EL1_Type_DP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_ID_ISAR6_EL1_Type_DP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_ISAR6_Type_DP (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_PMCR_Type_DP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_ID_AA64ISAR0_EL1_Type_DP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_ID_ISAR6_EL1_Type_DP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_ISAR6_Type_DP (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_PMCR_EL0_Type_E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_DBGBCR_EL1_Type_E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_DBGBCR_Type_E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_DBGWCR_EL1_Type_E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_DBGWCR_Type_E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_DSPSR_EL0_Type_E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_DSPSR_Type_E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMBLIMITR_EL1_Type_E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMCR_Type_E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_SPSR_EL1_Type_E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SPSR_EL2_Type_E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SPSR_EL3_Type_E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SPSR_abt_Type_E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SPSR_fiq_Type_E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SPSR_hyp_Type_E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SPSR_irq_Type_E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SPSR_mon_Type_E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SPSR_svc_Type_E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SPSR_und_Type_E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_DSPSR_EL0_Type_E (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_DSPSR_Type_E (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_SPSR_EL1_Type_E (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_SPSR_EL2_Type_E (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_SPSR_EL3_Type_E (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_SPSR_abt_Type_E (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_SPSR_fiq_Type_E (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_SPSR_hyp_Type_E (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_SPSR_irq_Type_E (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_SPSR_mon_Type_E (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_SPSR_svc_Type_E (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_SPSR_und_Type_E (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_PMCR_EL0_Type_FZO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMCFGR_Type_FZO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMCR_Type_FZO (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_PMCFGR_Type_FZO (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_PMCR_EL0_Type_FZS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_PMCR_EL0_Type_IDCODE (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_PMCR_Type_IDCODE (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _get_PMCR_Type_IDCODE (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _update_PMCR_EL0_Type_IMP (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_PMCR_Type_IMP (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_PMPCSCTL_Type_IMP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_TTBR0_Type_IMP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_TTBR1_Type_IMP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_PMCR_Type_IMP (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_PMPCSCTL_Type_IMP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_TTBR0_Type_IMP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_TTBR1_Type_IMP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_PMCR_EL0_Type_LC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMCR_Type_LC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMCR_EL0_Type_LP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMCR_Type_LP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_PMCR_Type_LP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_PMCR_EL0_Type_P (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_DBGVCR32_EL2_Type_P (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_DBGVCR_Type_P (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMBIDR_EL1_Type_P (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMCCFILTR_EL0_Type_P (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMCCFILTR_Type_P (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMCR_Type_P (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMEVTYPER_EL0_Type_P (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMEVTYPER_Type_P (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMICFILTR_EL0_Type_P (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_DBGVCR32_EL2_Type_P (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_DBGVCR_Type_P (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMBIDR_EL1_Type_P (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMCCFILTR_EL0_Type_P (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMCCFILTR_Type_P (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMCR_Type_P (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMEVTYPER_EL0_Type_P (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMEVTYPER_Type_P (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMICFILTR_EL0_Type_P (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_PMCR_EL0_Type_X (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMCR_Type_X (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_PMCR_Type_X (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def undefined_PMCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMINTENCLR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMINTENCLR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PMINTENCLR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMINTENCLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMOVSCLR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMOVSCLR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PMOVSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_MDCR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MDCR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_MDCR_EL3_Type_E3BREC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _update_MDCR_EL3_Type_E3BREW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _update_MDCR_EL3_Type_EDAD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_EDPRSR_Type_EDAD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SDCR_Type_EDAD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_EDPRSR_Type_EDAD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SDCR_Type_EDAD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_MDCR_EL3_Type_EDADE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_EDPRSR_Type_EDADE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_EDPRSR_Type_EDADE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_MDCR_EL3_Type_EPMAD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_EDPRSR_Type_EPMAD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SDCR_Type_EPMAD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_EDPRSR_Type_EPMAD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_SDCR_Type_EPMAD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_MDCR_EL3_Type_EPMADE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_EDPRSR_Type_EPMADE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_EDPRSR_Type_EPMADE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_MDCR_EL3_Type_EPMSSAD (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 45 x)

def _update_MDCR_EL3_Type_EnPM2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_MDCR_EL3_Type_EnPMS3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _update_MDCR_EL3_Type_EnPMSN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _update_MDCR_EL3_Type_EnPMSS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_MDCR_EL3_Type_MCCD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _update_MDCR_EL3_Type_MPMX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _update_MDCR_EL3_Type_NSPB (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _update_MDCR_EL3_Type_NSPBE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_MDCR_EL3_Type_RLTE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_MDCR_EL3_Type_SBRBE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 32 x)

def _update_MDCR_EL3_Type_SCCD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_SDCR_Type_SCCD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_MDCR_EL3_Type_SPD32 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_MDCR_EL3_Type_SPME (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_SDCR_Type_SPME (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_MDCR_EL3_Type_STE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_SDCR_Type_STE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_SDCR_Type_STE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def undefined_PMCCFILTR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMCCFILTR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMCCFILTR_EL0_Type_NSH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_PMCCFILTR_EL0_Type_NSH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMCCFILTR_Type_NSH (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMEVTYPER_EL0_Type_NSH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMEVTYPER_Type_NSH (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMICFILTR_EL0_Type_NSH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_PMCCFILTR_Type_NSH (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMEVTYPER_EL0_Type_NSH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMEVTYPER_Type_NSH (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMICFILTR_EL0_Type_NSH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMCCFILTR_EL0_Type_NSK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_PMCCFILTR_EL0_Type_NSK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMCCFILTR_Type_NSK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMEVTYPER_EL0_Type_NSK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMEVTYPER_Type_NSK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMICFILTR_EL0_Type_NSK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_PMCCFILTR_Type_NSK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMEVTYPER_EL0_Type_NSK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMEVTYPER_Type_NSK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMICFILTR_EL0_Type_NSK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMCCFILTR_EL0_Type_NSU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_PMCCFILTR_EL0_Type_NSU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_DBGVCR32_EL2_Type_NSU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_DBGVCR_Type_NSU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMCCFILTR_Type_NSU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMEVTYPER_EL0_Type_NSU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMEVTYPER_Type_NSU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMICFILTR_EL0_Type_NSU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_DBGVCR32_EL2_Type_NSU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_DBGVCR_Type_NSU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMCCFILTR_Type_NSU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMEVTYPER_EL0_Type_NSU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMEVTYPER_Type_NSU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMICFILTR_EL0_Type_NSU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMCCFILTR_EL0_Type_RLH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_PMCCFILTR_EL0_Type_RLH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMEVTYPER_EL0_Type_RLH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMICFILTR_EL0_Type_RLH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_PMEVTYPER_EL0_Type_RLH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMICFILTR_EL0_Type_RLH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMCCFILTR_EL0_Type_RLK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_PMCCFILTR_EL0_Type_RLK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMEVTYPER_EL0_Type_RLK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMICFILTR_EL0_Type_RLK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_PMEVTYPER_EL0_Type_RLK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMICFILTR_EL0_Type_RLK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMCCFILTR_EL0_Type_RLU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_PMCCFILTR_EL0_Type_RLU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMCCFILTR_Type_RLU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMEVTYPER_EL0_Type_RLU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMEVTYPER_Type_RLU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMICFILTR_EL0_Type_RLU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_PMCCFILTR_Type_RLU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMEVTYPER_EL0_Type_RLU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMEVTYPER_Type_RLU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMICFILTR_EL0_Type_RLU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMCCFILTR_EL0_Type_SH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_PMCCFILTR_EL0_Type_SH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_GPCCR_EL3_Type_SH (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _update_PAR_EL1_Type_SH (v : (BitVec 128)) (x : (BitVec 2)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 8 7 x)

def _update_PAR_Type_SH (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 7 x)

def _update_PMEVTYPER_EL0_Type_SH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMICFILTR_EL0_Type_SH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_PAR_EL1_Type_SH (v : (BitVec 128)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 8 7)

def _get_PAR_Type_SH (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 8 7)

def _get_PMEVTYPER_EL0_Type_SH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMICFILTR_EL0_Type_SH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMCCFILTR_EL0_Type_U (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_PMCCFILTR_EL0_Type_U (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_DBGVCR32_EL2_Type_U (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_DBGVCR_Type_U (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_GICH_MISR_Type_U (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICH_MISR_EL2_Type_U (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICH_MISR_Type_U (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_MPIDR_EL1_Type_U (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_MPIDR_Type_U (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMCCFILTR_Type_U (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMEVTYPER_EL0_Type_U (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMEVTYPER_Type_U (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMICFILTR_EL0_Type_U (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_VMPIDR_EL2_Type_U (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_VMPIDR_Type_U (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_DBGVCR32_EL2_Type_U (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_DBGVCR_Type_U (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_GICH_MISR_Type_U (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICH_MISR_EL2_Type_U (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_ICH_MISR_Type_U (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_MPIDR_EL1_Type_U (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_MPIDR_Type_U (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMCCFILTR_Type_U (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMEVTYPER_EL0_Type_U (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMEVTYPER_Type_U (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMICFILTR_EL0_Type_U (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_VMPIDR_EL2_Type_U (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_VMPIDR_Type_U (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def undefined_PMCCFILTR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMCCFILTR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMCNTENSET_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMCNTENSET_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PMCNTENSET_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMCNTENSET_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMEVTYPER_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMEVTYPER_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMEVTYPER_EL0_Type_MT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_PMEVTYPER_EL0_Type_MT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_MPIDR_EL1_Type_MT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_MPIDR_Type_MT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMEVTYPER_Type_MT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_VMPIDR_EL2_Type_MT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_VMPIDR_Type_MT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_MPIDR_EL1_Type_MT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_MPIDR_Type_MT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMEVTYPER_Type_MT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_VMPIDR_EL2_Type_MT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_VMPIDR_Type_MT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMEVTYPER_EL0_Type_SYNC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _update_PMEVTYPER_EL0_Type_SYNC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _update_PMICFILTR_EL0_Type_SYNC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _get_PMICFILTR_EL0_Type_SYNC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _update_PMEVTYPER_EL0_Type_TC (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 61 x)

def _update_ICH_HCR_EL2_Type_TC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_ICH_HCR_Type_TC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_ICH_HCR_EL2_Type_TC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_ICH_HCR_Type_TC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_PMEVTYPER_EL0_Type_TE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _update_HSCTLR_Type_TE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_SCTLR_Type_TE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMEVTYPER_EL0_Type_TH (v : (BitVec 64)) (x : (BitVec 12)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 32 x)

def _update_PMEVTYPER_EL0_Type_evtCount (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 10 (Sail.BitVec.extractLsb x (16 -i 1) (((16 -i 1) -i ((15 -i 10) +i 1)) +i 1))) 9 0 (Sail.BitVec.extractLsb x ((16 -i 1) -i ((15 -i 10) +i 1)) ((((16 -i 1) -i ((15 -i 10) +i 1)) -i ((9 -i 0) +i 1)) +i 1)))

def _update_AMEVTYPER0_EL0_Type_evtCount (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_AMEVTYPER0_Type_evtCount (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_AMEVTYPER1_EL0_Type_evtCount (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_AMEVTYPER1_Type_evtCount (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_PMEVTYPER_Type_evtCount (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 10 (Sail.BitVec.extractLsb x (16 -i 1) (((16 -i 1) -i ((15 -i 10) +i 1)) +i 1))) 9 0 (Sail.BitVec.extractLsb x ((16 -i 1) -i ((15 -i 10) +i 1)) ((((16 -i 1) -i ((15 -i 10) +i 1)) -i ((9 -i 0) +i 1)) +i 1)))

def _update_PMICFILTR_EL0_Type_evtCount (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _get_AMEVTYPER0_EL0_Type_evtCount (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _get_AMEVTYPER0_Type_evtCount (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _get_AMEVTYPER1_EL0_Type_evtCount (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _get_AMEVTYPER1_Type_evtCount (v : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _get_PMICFILTR_EL0_Type_evtCount (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def undefined_PMEVTYPER_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMEVTYPER_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMICFILTR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMICFILTR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_SDCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_SDCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _update_SDCR_Type_SPD (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_EDPRSR_Type_SPD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_EDPRSR_Type_SPD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def undefined_SDER32_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SDER32_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_SDER32_EL2_Type_SUIDEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_SDER32_EL2_Type_SUIDEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_SDER32_EL3_Type_SUIDEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_SDER_Type_SUIDEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_SDER32_EL2_Type_SUNIDEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_SDER32_EL2_Type_SUNIDEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_SDER32_EL3_Type_SUNIDEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_SDER_Type_SUNIDEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def undefined_SDER32_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SDER32_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_SDER_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_SDER_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMICNTR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _get_PMICNTR_EL0_Type_ICNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _update_PMICNTR_EL0_Type_ICNT (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_PMICNTSVR_EL1_Type_ICNT (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _get_PMICNTSVR_EL1_Type_ICNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def undefined_PMOVSSET_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMOVSSET_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_BRBCR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_BRBCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_BRBCR_EL1_Type_E0BRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_BRBCR_EL1_Type_E1BRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_BRBCR_EL1_Type_ERTN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_BRBCR_EL1_Type_ERTN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_BRBCR_EL2_Type_ERTN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_BRBCR_EL2_Type_ERTN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_BRBCR_EL1_Type_EXCEPTION (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_BRBCR_EL2_Type_EXCEPTION (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_BRBCR_EL1_Type_FZP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_BRBCR_EL2_Type_FZP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_BRBCR_EL1_Type_FZPSS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_BRBCR_EL1_Type_FZPSS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_BRBCR_EL2_Type_FZPSS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_BRBCR_EL2_Type_FZPSS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def undefined_BRBCR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_BRBCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_BRBCR_EL2_Type_E0HBRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_BRBCR_EL2_Type_E2BRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def undefined_BRBFCR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_BRBFCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_BRBFCR_EL1_Type_BANK (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 28 x)

def _update_MDSELR_EL1_Type_BANK (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _update_SPMSELR_EL0_Type_BANK (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _get_MDSELR_EL1_Type_BANK (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _get_SPMSELR_EL0_Type_BANK (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _update_BRBFCR_EL1_Type_CONDDIR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_BRBFCR_EL1_Type_DIRCALL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_BRBFCR_EL1_Type_DIRECT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_BRBFCR_EL1_Type_EnI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_BRBFCR_EL1_Type_INDCALL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_BRBFCR_EL1_Type_INDIRECT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_BRBFCR_EL1_Type_PAUSED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_BRBFCR_EL1_Type_RTN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def undefined_BRBTS_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_CNTHCTL_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTHCTL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_CNTHCTL_EL2_Type_CNTPMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_CNTHCTL_EL2_Type_CNTVMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_CNTHCTL_EL2_Type_ECV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_ID_AA64MMFR0_EL1_Type_ECV (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _get_ID_AA64MMFR0_EL1_Type_ECV (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _get_CNTHCTL_EL2_Type_EL0PCTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_CNTHCTL_EL2_Type_EL0PCTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CNTEL0ACR_Type_EL0PCTEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CNTKCTL_EL1_Type_EL0PCTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_CNTEL0ACR_Type_EL0PCTEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_CNTKCTL_EL1_Type_EL0PCTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_CNTHCTL_EL2_Type_EL0PTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_CNTHCTL_EL2_Type_EL0PTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_CNTEL0ACR_Type_EL0PTEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_CNTKCTL_EL1_Type_EL0PTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_CNTEL0ACR_Type_EL0PTEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_CNTKCTL_EL1_Type_EL0PTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_CNTHCTL_EL2_Type_EL0VCTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_CNTHCTL_EL2_Type_EL0VCTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_CNTEL0ACR_Type_EL0VCTEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_CNTKCTL_EL1_Type_EL0VCTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_CNTEL0ACR_Type_EL0VCTEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_CNTKCTL_EL1_Type_EL0VCTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_CNTHCTL_EL2_Type_EL0VTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_CNTHCTL_EL2_Type_EL0VTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_CNTEL0ACR_Type_EL0VTEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_CNTKCTL_EL1_Type_EL0VTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_CNTEL0ACR_Type_EL0VTEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_CNTKCTL_EL1_Type_EL0VTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_CNTHCTL_EL2_Type_EL1NVPCT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_CNTHCTL_EL2_Type_EL1NVPCT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_CNTHCTL_EL2_Type_EL1NVVCT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_CNTHCTL_EL2_Type_EL1NVVCT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_CNTHCTL_EL2_Type_EL1PCEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_CNTHCTL_EL2_Type_EL1PCEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_CNTHCTL_EL2_Type_EL1PTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_CNTHCTL_EL2_Type_EL1PTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_CNTHCTL_EL2_Type_EL1TVCT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_CNTHCTL_EL2_Type_EL1TVCT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_CNTHCTL_EL2_Type_EL1TVT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_CNTHCTL_EL2_Type_EL1TVT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_CNTHCTL_EL2_Type_EVNTDIR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_CNTHCTL_Type_EVNTDIR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_CNTKCTL_EL1_Type_EVNTDIR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_CNTKCTL_Type_EVNTDIR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_CNTHCTL_Type_EVNTDIR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_CNTKCTL_Type_EVNTDIR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_CNTHCTL_EL2_Type_EVNTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_CNTHCTL_Type_EVNTEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_CNTKCTL_EL1_Type_EVNTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_CNTKCTL_Type_EVNTEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_CNTHCTL_Type_EVNTEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_CNTKCTL_Type_EVNTEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_CNTHCTL_EL2_Type_EVNTI (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_CNTHCTL_Type_EVNTI (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_CNTKCTL_EL1_Type_EVNTI (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_CNTKCTL_Type_EVNTI (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_CNTHCTL_Type_EVNTI (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_CNTKCTL_Type_EVNTI (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_CNTHCTL_EL2_Type_EVNTIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_CNTHCTL_Type_EVNTIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_CNTKCTL_EL1_Type_EVNTIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_CNTKCTL_Type_EVNTIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_CNTHCTL_Type_EVNTIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_CNTKCTL_Type_EVNTIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def undefined_EDECR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDECR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_EDECR_Type_OSUCE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_EDECR_Type_OSUCE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CTIDEVCTL_Type_OSUCE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_CTIDEVCTL_Type_OSUCE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_EDECR_Type_PME (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_EDECR_Type_RCE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_EDECR_Type_RCE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_CTIDEVCTL_Type_RCE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_CTIDEVCTL_Type_RCE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_EDECR_Type_SS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_EDECR_Type_SS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_DBGVCR32_EL2_Type_SS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_DBGVCR_Type_SS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_DSPSR_EL0_Type_SS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_DSPSR_Type_SS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_EDESR_Type_SS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_MDSCR_EL1_Type_SS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PAR_Type_SS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMCFGR_Type_SS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMPCSCTL_Type_SS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMSSCR_EL1_Type_SS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_SPSR_EL1_Type_SS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_SPSR_EL2_Type_SS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_SPSR_EL3_Type_SS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_DBGVCR32_EL2_Type_SS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_DBGVCR_Type_SS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_DSPSR_EL0_Type_SS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_DSPSR_Type_SS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PAR_Type_SS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMCFGR_Type_SS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMPCSCTL_Type_SS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMSSCR_EL1_Type_SS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_SPSR_EL1_Type_SS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_SPSR_EL2_Type_SS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_SPSR_EL3_Type_SS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def undefined_DSPSR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _get_DSPSR_EL0_Type_ALLINT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_DSPSR_EL0_Type_ALLINT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_SPSR_EL1_Type_ALLINT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_SPSR_EL2_Type_ALLINT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_SPSR_EL3_Type_ALLINT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_SPSR_EL1_Type_ALLINT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_SPSR_EL2_Type_ALLINT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_SPSR_EL3_Type_ALLINT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_DSPSR_EL0_Type_BTYPE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _update_DSPSR_EL0_Type_BTYPE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_SPSR_EL1_Type_BTYPE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_SPSR_EL2_Type_BTYPE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_SPSR_EL3_Type_BTYPE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _get_SPSR_EL1_Type_BTYPE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _get_SPSR_EL2_Type_BTYPE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _get_SPSR_EL3_Type_BTYPE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _get_DSPSR_EL0_Type_DIT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_DSPSR_EL0_Type_DIT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_DSPSR_Type_DIT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_ID_AA64PFR0_EL1_Type_DIT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_ID_PFR0_EL1_Type_DIT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_PFR0_Type_DIT (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_SPSR_EL1_Type_DIT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_SPSR_EL2_Type_DIT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_SPSR_EL3_Type_DIT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_SPSR_abt_Type_DIT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_SPSR_fiq_Type_DIT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_SPSR_hyp_Type_DIT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_SPSR_irq_Type_DIT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_SPSR_mon_Type_DIT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_SPSR_svc_Type_DIT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_SPSR_und_Type_DIT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_DSPSR_Type_DIT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_ID_AA64PFR0_EL1_Type_DIT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_ID_PFR0_EL1_Type_DIT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_PFR0_Type_DIT (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_SPSR_EL1_Type_DIT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_SPSR_EL2_Type_DIT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_SPSR_EL3_Type_DIT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_SPSR_abt_Type_DIT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_SPSR_fiq_Type_DIT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_SPSR_hyp_Type_DIT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_SPSR_irq_Type_DIT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_SPSR_mon_Type_DIT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_SPSR_svc_Type_DIT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_SPSR_und_Type_DIT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_DSPSR_EL0_Type_EXLOCK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)

def _update_DSPSR_EL0_Type_EXLOCK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _update_SPSR_EL1_Type_EXLOCK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _update_SPSR_EL2_Type_EXLOCK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _update_SPSR_EL3_Type_EXLOCK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _get_SPSR_EL1_Type_EXLOCK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)

def _get_SPSR_EL2_Type_EXLOCK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)

def _get_SPSR_EL3_Type_EXLOCK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)

def _get_DSPSR_EL0_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_DSPSR_EL0_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_DBGVCR32_EL2_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_DBGVCR_Type_F (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_DSPSR_Type_F (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ISR_EL1_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ISR_Type_F (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PAR_EL1_Type_F (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PAR_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMBIDR_EL1_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SPSR_EL1_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SPSR_EL2_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SPSR_EL3_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SPSR_abt_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SPSR_fiq_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SPSR_hyp_Type_F (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SPSR_irq_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SPSR_mon_Type_F (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SPSR_svc_Type_F (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SPSR_und_Type_F (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_DBGVCR32_EL2_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_DBGVCR_Type_F (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_DSPSR_Type_F (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ISR_EL1_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_ISR_Type_F (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PAR_EL1_Type_F (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PAR_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMBIDR_EL1_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_SPSR_EL1_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_SPSR_EL2_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_SPSR_EL3_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_SPSR_abt_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_SPSR_fiq_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_SPSR_hyp_Type_F (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_SPSR_irq_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_SPSR_mon_Type_F (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_SPSR_svc_Type_F (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_SPSR_und_Type_F (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_DSPSR_EL0_Type_GE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_DSPSR_EL0_Type_GE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_DSPSR_Type_GE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_SPSR_EL1_Type_GE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_SPSR_EL2_Type_GE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_SPSR_EL3_Type_GE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_SPSR_abt_Type_GE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_SPSR_fiq_Type_GE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_SPSR_hyp_Type_GE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_SPSR_irq_Type_GE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_SPSR_mon_Type_GE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_SPSR_svc_Type_GE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_SPSR_und_Type_GE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_DSPSR_Type_GE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_SPSR_EL1_Type_GE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_SPSR_EL2_Type_GE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_SPSR_EL3_Type_GE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_SPSR_abt_Type_GE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_SPSR_fiq_Type_GE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_SPSR_hyp_Type_GE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_SPSR_irq_Type_GE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_SPSR_mon_Type_GE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_SPSR_svc_Type_GE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_SPSR_und_Type_GE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_DSPSR_EL0_Type_IT (v : (BitVec 64)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))

def _update_DSPSR_EL0_Type_IT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 10 (Sail.BitVec.extractLsb x (8 -i 1) (((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))) 26 25 (Sail.BitVec.extractLsb x ((8 -i 1) -i ((15 -i 10) +i 1)) ((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))

def _update_DSPSR_Type_IT (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 10 (Sail.BitVec.extractLsb x (8 -i 1) (((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))) 26 25 (Sail.BitVec.extractLsb x ((8 -i 1) -i ((15 -i 10) +i 1)) ((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))

def _update_SPSR_EL1_Type_IT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 10 (Sail.BitVec.extractLsb x (8 -i 1) (((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))) 26 25 (Sail.BitVec.extractLsb x ((8 -i 1) -i ((15 -i 10) +i 1)) ((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))

def _update_SPSR_EL2_Type_IT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 10 (Sail.BitVec.extractLsb x (8 -i 1) (((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))) 26 25 (Sail.BitVec.extractLsb x ((8 -i 1) -i ((15 -i 10) +i 1)) ((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))

def _update_SPSR_EL3_Type_IT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 10 (Sail.BitVec.extractLsb x (8 -i 1) (((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))) 26 25 (Sail.BitVec.extractLsb x ((8 -i 1) -i ((15 -i 10) +i 1)) ((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))

def _update_SPSR_abt_Type_IT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 10 (Sail.BitVec.extractLsb x (8 -i 1) (((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))) 26 25 (Sail.BitVec.extractLsb x ((8 -i 1) -i ((15 -i 10) +i 1)) ((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))

def _update_SPSR_fiq_Type_IT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 10 (Sail.BitVec.extractLsb x (8 -i 1) (((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))) 26 25 (Sail.BitVec.extractLsb x ((8 -i 1) -i ((15 -i 10) +i 1)) ((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))

def _update_SPSR_hyp_Type_IT (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 10 (Sail.BitVec.extractLsb x (8 -i 1) (((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))) 26 25 (Sail.BitVec.extractLsb x ((8 -i 1) -i ((15 -i 10) +i 1)) ((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))

def _update_SPSR_irq_Type_IT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 10 (Sail.BitVec.extractLsb x (8 -i 1) (((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))) 26 25 (Sail.BitVec.extractLsb x ((8 -i 1) -i ((15 -i 10) +i 1)) ((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))

def _update_SPSR_mon_Type_IT (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 10 (Sail.BitVec.extractLsb x (8 -i 1) (((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))) 26 25 (Sail.BitVec.extractLsb x ((8 -i 1) -i ((15 -i 10) +i 1)) ((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))

def _update_SPSR_svc_Type_IT (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 10 (Sail.BitVec.extractLsb x (8 -i 1) (((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))) 26 25 (Sail.BitVec.extractLsb x ((8 -i 1) -i ((15 -i 10) +i 1)) ((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))

def _update_SPSR_und_Type_IT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 10 (Sail.BitVec.extractLsb x (8 -i 1) (((8 -i 1) -i ((15 -i 10) +i 1)) +i 1))) 26 25 (Sail.BitVec.extractLsb x ((8 -i 1) -i ((15 -i 10) +i 1)) ((((8 -i 1) -i ((15 -i 10) +i 1)) -i ((26 -i 25) +i 1)) +i 1)))

def _get_DSPSR_Type_IT (v : (BitVec 32)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))

def _get_SPSR_EL1_Type_IT (v : (BitVec 64)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))

def _get_SPSR_EL2_Type_IT (v : (BitVec 64)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))

def _get_SPSR_EL3_Type_IT (v : (BitVec 64)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))

def _get_SPSR_abt_Type_IT (v : (BitVec 64)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))

def _get_SPSR_fiq_Type_IT (v : (BitVec 64)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))

def _get_SPSR_hyp_Type_IT (v : (BitVec 32)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))

def _get_SPSR_irq_Type_IT (v : (BitVec 64)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))

def _get_SPSR_mon_Type_IT (v : (BitVec 32)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))

def _get_SPSR_svc_Type_IT (v : (BitVec 32)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))

def _get_SPSR_und_Type_IT (v : (BitVec 64)) : (BitVec 8) :=
  ((Sail.BitVec.extractLsb v 15 10) +++ (Sail.BitVec.extractLsb v 26 25))

def _get_DSPSR_EL0_Type_PAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_DSPSR_EL0_Type_PAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_DSPSR_Type_PAN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_ID_AA64MMFR1_EL1_Type_PAN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_MMFR3_EL1_Type_PAN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_ID_MMFR3_Type_PAN (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_SPSR_EL1_Type_PAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_SPSR_EL2_Type_PAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_SPSR_EL3_Type_PAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_SPSR_abt_Type_PAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_SPSR_fiq_Type_PAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_SPSR_hyp_Type_PAN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_SPSR_irq_Type_PAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_SPSR_mon_Type_PAN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_SPSR_svc_Type_PAN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_SPSR_und_Type_PAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_DSPSR_Type_PAN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_ID_AA64MMFR1_EL1_Type_PAN (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_MMFR3_EL1_Type_PAN (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_MMFR3_Type_PAN (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_SPSR_EL1_Type_PAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_SPSR_EL2_Type_PAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_SPSR_EL3_Type_PAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_SPSR_abt_Type_PAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_SPSR_fiq_Type_PAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_SPSR_hyp_Type_PAN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_SPSR_irq_Type_PAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_SPSR_mon_Type_PAN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_SPSR_svc_Type_PAN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_SPSR_und_Type_PAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_DSPSR_EL0_Type_PM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _update_DSPSR_EL0_Type_PM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_SPSR_EL1_Type_PM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_SPSR_EL2_Type_PM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_SPSR_EL3_Type_PM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _get_SPSR_EL1_Type_PM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _get_SPSR_EL2_Type_PM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _get_SPSR_EL3_Type_PM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _get_DSPSR_EL0_Type_PPEND (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _update_DSPSR_EL0_Type_PPEND (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _update_DSPSR2_Type_PPEND (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_SPSR_EL1_Type_PPEND (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _update_SPSR_EL2_Type_PPEND (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _update_SPSR_EL3_Type_PPEND (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _get_DSPSR2_Type_PPEND (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_SPSR_EL1_Type_PPEND (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _get_SPSR_EL2_Type_PPEND (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _get_SPSR_EL3_Type_PPEND (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _get_DSPSR_EL0_Type_Q (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_DSPSR_EL0_Type_Q (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_DSPSR_Type_Q (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_SPSR_EL1_Type_Q (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_SPSR_EL2_Type_Q (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_SPSR_EL3_Type_Q (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_SPSR_abt_Type_Q (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_SPSR_fiq_Type_Q (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_SPSR_hyp_Type_Q (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_SPSR_irq_Type_Q (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_SPSR_mon_Type_Q (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_SPSR_svc_Type_Q (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_SPSR_und_Type_Q (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_DSPSR_Type_Q (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_SPSR_EL1_Type_Q (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_SPSR_EL2_Type_Q (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_SPSR_EL3_Type_Q (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_SPSR_abt_Type_Q (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_SPSR_fiq_Type_Q (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_SPSR_hyp_Type_Q (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_SPSR_irq_Type_Q (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_SPSR_mon_Type_Q (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_SPSR_svc_Type_Q (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_SPSR_und_Type_Q (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_DSPSR_EL0_Type_TCO (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_DSPSR_EL0_Type_TCO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_SPSR_EL1_Type_TCO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_SPSR_EL2_Type_TCO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_SPSR_EL3_Type_TCO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_SPSR_EL1_Type_TCO (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_SPSR_EL2_Type_TCO (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_SPSR_EL3_Type_TCO (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_DSPSR_EL0_Type_UAO (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_DSPSR_EL0_Type_UAO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_ID_AA64MMFR2_EL1_Type_UAO (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_SPSR_EL1_Type_UAO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_SPSR_EL2_Type_UAO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_SPSR_EL3_Type_UAO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_ID_AA64MMFR2_EL1_Type_UAO (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_SPSR_EL1_Type_UAO (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_SPSR_EL2_Type_UAO (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_SPSR_EL3_Type_UAO (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def undefined_DSPSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def _get_DSPSR_Type_SSBS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_DSPSR_Type_SSBS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_ID_AA64PFR1_EL1_Type_SSBS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_PFR2_EL1_Type_SSBS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_PFR2_Type_SSBS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_SPSR_abt_Type_SSBS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_SPSR_fiq_Type_SSBS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_SPSR_hyp_Type_SSBS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_SPSR_irq_Type_SSBS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_SPSR_mon_Type_SSBS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_SPSR_svc_Type_SSBS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_SPSR_und_Type_SSBS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_ID_AA64PFR1_EL1_Type_SSBS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_PFR2_EL1_Type_SSBS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_PFR2_Type_SSBS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_SPSR_abt_Type_SSBS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_SPSR_fiq_Type_SSBS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_SPSR_hyp_Type_SSBS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_SPSR_irq_Type_SSBS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_SPSR_mon_Type_SSBS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_SPSR_svc_Type_SSBS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_SPSR_und_Type_SSBS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def undefined_DSPSR2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_TCR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_TCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_TCR_EL1_Type_A1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_TCR_EL2_Type_A1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_TTBCR_Type_A1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_TCR_EL1_Type_AS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _update_TCR_EL2_Type_AS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _update_TCR_EL1_Type_DS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_GICD_CTLR_Type_DS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_LORC_EL1_Type_DS (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 2 x)

def _update_TCR_EL3_Type_DS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_VTCR_EL2_Type_DS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _get_GICD_CTLR_Type_DS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_LORC_EL1_Type_DS (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 9 2)

def _update_TCR_EL1_Type_E0PD0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _update_TCR_EL2_Type_E0PD0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _update_TCR_EL1_Type_E0PD1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _update_TCR_EL2_Type_E0PD1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _update_TCR_EL1_Type_EPD0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_TCR_EL2_Type_EPD0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_TTBCR_Type_EPD0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_TCR_EL1_Type_EPD1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_TCR_EL2_Type_EPD1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_TTBCR_Type_EPD1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_TCR_EL1_Type_HA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)

def _update_TCR_EL3_Type_HA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_VTCR_EL2_Type_HA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_TCR_EL1_Type_HD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _update_TCR_EL3_Type_HD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_VTCR_EL2_Type_HD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_TCR_EL1_Type_HPD0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _update_TCR_EL2_Type_HPD0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _update_TTBCR2_Type_HPD0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_TCR_EL1_Type_HPD1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _update_TCR_EL2_Type_HPD1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _update_TTBCR2_Type_HPD1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_TCR_EL1_Type_HWU059 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)

def _update_TCR_EL1_Type_HWU059 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _update_TCR_EL2_Type_HWU059 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _update_TTBCR2_Type_HWU059 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_TCR_EL2_Type_HWU059 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)

def _get_TTBCR2_Type_HWU059 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_TCR_EL1_Type_HWU060 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)

def _update_TCR_EL1_Type_HWU060 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_TCR_EL2_Type_HWU060 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_TTBCR2_Type_HWU060 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_TCR_EL2_Type_HWU060 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)

def _get_TTBCR2_Type_HWU060 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_TCR_EL1_Type_HWU061 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)

def _update_TCR_EL1_Type_HWU061 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _update_TCR_EL2_Type_HWU061 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _update_TTBCR2_Type_HWU061 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_TCR_EL2_Type_HWU061 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)

def _get_TTBCR2_Type_HWU061 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_TCR_EL1_Type_HWU062 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)

def _update_TCR_EL1_Type_HWU062 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _update_TCR_EL2_Type_HWU062 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _update_TTBCR2_Type_HWU062 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_TCR_EL2_Type_HWU062 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)

def _get_TTBCR2_Type_HWU062 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_TCR_EL1_Type_HWU159 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 47 47)

def _update_TCR_EL1_Type_HWU159 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 47 x)

def _update_TCR_EL2_Type_HWU159 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 47 x)

def _update_TTBCR2_Type_HWU159 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_TCR_EL2_Type_HWU159 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 47 47)

def _get_TTBCR2_Type_HWU159 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_TCR_EL1_Type_HWU160 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _update_TCR_EL1_Type_HWU160 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _update_TCR_EL2_Type_HWU160 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _update_TTBCR2_Type_HWU160 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_TCR_EL2_Type_HWU160 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _get_TTBCR2_Type_HWU160 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_TCR_EL1_Type_HWU161 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)

def _update_TCR_EL1_Type_HWU161 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def _update_TCR_EL2_Type_HWU161 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def _update_TTBCR2_Type_HWU161 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_TCR_EL2_Type_HWU161 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)

def _get_TTBCR2_Type_HWU161 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_TCR_EL1_Type_HWU162 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)

def _update_TCR_EL1_Type_HWU162 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _update_TCR_EL2_Type_HWU162 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _update_TTBCR2_Type_HWU162 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_TCR_EL2_Type_HWU162 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)

def _get_TTBCR2_Type_HWU162 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_TCR_EL1_Type_IPS (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 32 x)

def _update_TCR_EL2_Type_IPS (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 32 x)

def _update_TCR_EL1_Type_IRGN0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def _update_HTCR_Type_IRGN0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def _update_TCR_EL2_Type_IRGN0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def _update_TCR_EL3_Type_IRGN0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def _update_TTBCR_Type_IRGN0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def _update_VTCR_EL2_Type_IRGN0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def _update_VTCR_Type_IRGN0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def _update_TCR_EL1_Type_IRGN1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)

def _update_TCR_EL2_Type_IRGN1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)

def _update_TTBCR_Type_IRGN1 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 24 x)

def _update_TCR_EL1_Type_MTX0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _update_TCR_EL2_Type_MTX0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _update_TCR_EL1_Type_MTX1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_TCR_EL2_Type_MTX1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_TCR_EL1_Type_NFD0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _update_TCR_EL2_Type_NFD0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _update_TCR_EL1_Type_NFD1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _update_TCR_EL2_Type_NFD1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _update_TCR_EL1_Type_ORGN0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_HTCR_Type_ORGN0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_TCR_EL2_Type_ORGN0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_TCR_EL3_Type_ORGN0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_TTBCR_Type_ORGN0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_VTCR_EL2_Type_ORGN0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_VTCR_Type_ORGN0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_TCR_EL1_Type_ORGN1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 26 x)

def _update_TCR_EL2_Type_ORGN1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 26 x)

def _update_TTBCR_Type_ORGN1 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 26 x)

def _update_TCR_EL1_Type_SH0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _update_HTCR_Type_SH0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _update_TCR_EL2_Type_SH0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _update_TCR_EL3_Type_SH0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _update_TTBCR_Type_SH0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _update_VTCR_EL2_Type_SH0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _update_VTCR_Type_SH0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _update_TCR_EL1_Type_SH1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 28 x)

def _update_TCR_EL2_Type_SH1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 28 x)

def _update_TTBCR_Type_SH1 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 28 x)

def _update_TCR_EL1_Type_T0SZ (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 0 x)

def _update_HTCR_Type_T0SZ (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_TCR_EL2_Type_T0SZ (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 0 x)

def _update_TCR_EL3_Type_T0SZ (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 0 x)

def _update_TTBCR_Type_T0SZ (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_VSTCR_EL2_Type_T0SZ (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 0 x)

def _update_VTCR_EL2_Type_T0SZ (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 0 x)

def _update_VTCR_Type_T0SZ (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_TCR_EL1_Type_T1SZ (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 16 x)

def _update_TCR_EL2_Type_T1SZ (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 16 x)

def _update_TTBCR_Type_T1SZ (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 16 x)

def _update_TCR_EL1_Type_TBI0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _update_TCR_EL2_Type_TBI0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _update_TCR_EL1_Type_TBI1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _update_TCR_EL2_Type_TBI1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _update_TCR_EL1_Type_TBID0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)

def _update_TCR_EL2_Type_TBID0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)

def _update_TCR_EL1_Type_TBID1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _update_TCR_EL2_Type_TBID1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _update_TCR_EL1_Type_TCMA0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _update_TCR_EL2_Type_TCMA0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _update_TCR_EL1_Type_TCMA1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _update_TCR_EL2_Type_TCMA1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _update_TCR_EL1_Type_TG0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_TCR_EL2_Type_TG0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_TCR_EL3_Type_TG0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_VSTCR_EL2_Type_TG0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_VTCR_EL2_Type_TG0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_TCR_EL1_Type_TG1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 30 x)

def _update_TCR_EL2_Type_TG1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 30 x)

def undefined_TCR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_TCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_TCR_EL2_Type_HPD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_HTCR_Type_HPD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_TCR_EL3_Type_HPD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_TCR_EL2_Type_HWU59 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_TCR_EL2_Type_HWU59 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_HTCR_Type_HWU59 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_TCR_EL3_Type_HWU59 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_VTCR_EL2_Type_HWU59 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_VTCR_Type_HWU59 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_HTCR_Type_HWU59 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_VTCR_EL2_Type_HWU59 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_VTCR_Type_HWU59 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_TCR_EL2_Type_HWU60 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_TCR_EL2_Type_HWU60 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_HTCR_Type_HWU60 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_TCR_EL3_Type_HWU60 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_VTCR_EL2_Type_HWU60 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_VTCR_Type_HWU60 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_HTCR_Type_HWU60 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_VTCR_EL2_Type_HWU60 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_VTCR_Type_HWU60 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_TCR_EL2_Type_HWU61 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_TCR_EL2_Type_HWU61 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_HTCR_Type_HWU61 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_TCR_EL3_Type_HWU61 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_VTCR_EL2_Type_HWU61 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_VTCR_Type_HWU61 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_HTCR_Type_HWU61 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_VTCR_EL2_Type_HWU61 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_VTCR_Type_HWU61 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_TCR_EL2_Type_HWU62 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_TCR_EL2_Type_HWU62 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_HTCR_Type_HWU62 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_TCR_EL3_Type_HWU62 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_VTCR_EL2_Type_HWU62 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_VTCR_Type_HWU62 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_HTCR_Type_HWU62 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_VTCR_EL2_Type_HWU62 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_VTCR_Type_HWU62 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_TCR_EL2_Type_MTX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _update_TCR_EL3_Type_MTX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _update_TCR_EL2_Type_PS (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 16 x)

def _update_TCR_EL3_Type_PS (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 16 x)

def _update_VTCR_EL2_Type_PS (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 16 x)

def _update_TCR_EL2_Type_TBI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_TCR_EL3_Type_TBI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_TCR_EL2_Type_TBID (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_TCR_EL3_Type_TBID (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_TCR_EL2_Type_TCMA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_TCR_EL3_Type_TCMA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def undefined_TCR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_TCR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_TCR_EL3_Type_AIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _update_ID_AA64MMFR3_EL1_Type_AIE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_TCR2_EL1_Type_AIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_TCR2_EL2_Type_AIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_ID_AA64MMFR3_EL1_Type_AIE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_TCR_EL3_Type_D128 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _update_ID_AA64MMFR3_EL1_Type_D128 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_PAR_EL1_Type_D128 (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 64 64 x)

def _update_TCR2_EL1_Type_D128 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_TCR2_EL2_Type_D128 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_VTCR_EL2_Type_D128 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _get_ID_AA64MMFR3_EL1_Type_D128 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_PAR_EL1_Type_D128 (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 64 64)

def _update_TCR_EL3_Type_DisCH0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _update_TCR2_EL1_Type_DisCH0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_TCR2_EL2_Type_DisCH0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_TCR_EL3_Type_HAFT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _update_TCR2_EL1_Type_HAFT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_TCR2_EL2_Type_HAFT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_VTCR_EL2_Type_HAFT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_TCR_EL3_Type_PIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _update_TCR2_EL1_Type_PIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_TCR2_EL2_Type_PIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_TCR_EL3_Type_POE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _update_TCR2_EL1_Type_POE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_TCR2_EL2_Type_POE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_TCR_EL3_Type_PTTWI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _update_HCRX_EL2_Type_PTTWI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_TCR2_EL1_Type_PTTWI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_TCR2_EL2_Type_PTTWI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_HCRX_EL2_Type_PTTWI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_TCR2_EL1_Type_PTTWI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_TCR2_EL2_Type_PTTWI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_TCR_EL3_Type_PnCH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _update_TCR2_EL1_Type_PnCH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_TCR2_EL2_Type_PnCH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

/-- Type quantifiers: n : Int -/
def Rmode_read (n : Int) (mode : (BitVec 5)) : SailM (BitVec 32) := do
  sail_assert ((n ≥b 0) && (n ≤b 14)) "src/v8_base.sail:6376.27-6376.28"
  if ((bne (← (CurrentSecurityState ())) SS_Secure) : Bool)
  then sail_assert (mode != M32_Monitor) "src/v8_base.sail:6378.34-6378.35"
  else (pure ())
  sail_assert (! (← (BadMode mode))) "src/v8_base.sail:6380.34-6380.35"
  if ((mode == M32_Monitor) : Bool)
  then
    (do
      if ((n == 13) : Bool)
      then readReg SP_mon
      else
        (do
          if ((n == 14) : Bool)
          then readReg LR_mon
          else (pure (Sail.BitVec.extractLsb (← (get_R n)) 31 0))))
  else (pure (Sail.BitVec.extractLsb (← (get_R (← (LookUpRIndex n mode)))) 31 0))

def undefined_BRBIDR0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_BRBIDR0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_BRBIDR0_EL1_Type_FORMAT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_BRBIDR0_EL1_Type_FORMAT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_BRBIDR0_EL1_Type_NUMREC (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def undefined_PMSIDR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMSIDR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMSIDR_EL1_Type_ArchInst (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_PMSIDR_EL1_Type_ArchInst (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_PMSIDR_EL1_Type_CRR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_PMSIDR_EL1_Type_CRR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_PMSIDR_EL1_Type_CountSize (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_PMSIDR_EL1_Type_CountSize (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_PMSIDR_EL1_Type_ERnd (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_PMSIDR_EL1_Type_ERnd (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_PMSIDR_EL1_Type_FDS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_PMSIDR_EL1_Type_FDS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMSFCR_EL1_Type_FDS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_PMSFCR_EL1_Type_FDS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMSIDR_EL1_Type_FE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_PMSIDR_EL1_Type_FE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMSFCR_EL1_Type_FE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_PMSFCR_EL1_Type_FE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMSIDR_EL1_Type_FL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_PMSIDR_EL1_Type_FL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMSFCR_EL1_Type_FL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_PMSFCR_EL1_Type_FL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMSIDR_EL1_Type_FT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_PMSIDR_EL1_Type_FT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMSFCR_EL1_Type_FT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_PMSFCR_EL1_Type_FT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMSIDR_EL1_Type_FnE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_PMSIDR_EL1_Type_FnE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMSFCR_EL1_Type_FnE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_PMSFCR_EL1_Type_FnE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMSIDR_EL1_Type_Format (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_PMSIDR_EL1_Type_Format (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_PMSIDR_EL1_Type_Interval (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_PMSIDR_EL1_Type_Interval (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_PMSIDR_EL1_Type_LDS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_PMSIDR_EL1_Type_LDS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_PMSIDR_EL1_Type_MaxSize (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_PMSIDR_EL1_Type_MaxSize (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_PMSIDR_EL1_Type_PBT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def undefined_PMSCR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMSCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMSCR_EL1_Type_CX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_PMSCR_EL1_Type_CX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_HTRFCR_Type_CX (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_PMSCR_EL2_Type_CX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_TRFCR_EL2_Type_CX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_HTRFCR_Type_CX (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMSCR_EL2_Type_CX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_TRFCR_EL2_Type_CX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_PMSCR_EL1_Type_E0SPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMSCR_EL1_Type_E1SPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMSCR_EL1_Type_PA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_MFAR_EL3_Type_PA (v : (BitVec 64)) (x : (BitVec 56)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 55 52 (Sail.BitVec.extractLsb x (56 -i 1) (((56 -i 1) -i ((55 -i 52) +i 1)) +i 1))) 51 48 (Sail.BitVec.extractLsb x ((56 -i 1) -i ((55 -i 52) +i 1)) ((((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) +i 1))) 47 0 (Sail.BitVec.extractLsb x (((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) (((((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) -i ((47 -i 0) +i 1)) +i 1)))

def _update_PAR_Type_PA (v : (BitVec 64)) (x : (BitVec 28)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 12 x)

def _update_PFAR_EL1_Type_PA (v : (BitVec 64)) (x : (BitVec 56)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 55 52 (Sail.BitVec.extractLsb x (56 -i 1) (((56 -i 1) -i ((55 -i 52) +i 1)) +i 1))) 51 48 (Sail.BitVec.extractLsb x ((56 -i 1) -i ((55 -i 52) +i 1)) ((((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) +i 1))) 47 0 (Sail.BitVec.extractLsb x (((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) (((((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) -i ((47 -i 0) +i 1)) +i 1)))

def _update_PFAR_EL2_Type_PA (v : (BitVec 64)) (x : (BitVec 56)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 55 52 (Sail.BitVec.extractLsb x (56 -i 1) (((56 -i 1) -i ((55 -i 52) +i 1)) +i 1))) 51 48 (Sail.BitVec.extractLsb x ((56 -i 1) -i ((55 -i 52) +i 1)) ((((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) +i 1))) 47 0 (Sail.BitVec.extractLsb x (((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) (((((56 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) -i ((47 -i 0) +i 1)) +i 1)))

def _update_PMSCR_EL2_Type_PA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_MFAR_EL3_Type_PA (v : (BitVec 64)) : (BitVec 56) :=
  ((Sail.BitVec.extractLsb v 55 52) +++ ((Sail.BitVec.extractLsb v 51 48) +++ (Sail.BitVec.extractLsb v 47 0)))

def _get_PAR_Type_PA (v : (BitVec 64)) : (BitVec 28) :=
  (Sail.BitVec.extractLsb v 39 12)

def _get_PFAR_EL1_Type_PA (v : (BitVec 64)) : (BitVec 56) :=
  ((Sail.BitVec.extractLsb v 55 52) +++ ((Sail.BitVec.extractLsb v 51 48) +++ (Sail.BitVec.extractLsb v 47 0)))

def _get_PFAR_EL2_Type_PA (v : (BitVec 64)) : (BitVec 56) :=
  ((Sail.BitVec.extractLsb v 55 52) +++ ((Sail.BitVec.extractLsb v 51 48) +++ (Sail.BitVec.extractLsb v 47 0)))

def _get_PMSCR_EL1_Type_PCT (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def _update_PMSCR_EL1_Type_PCT (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _update_PMSCR_EL2_Type_PCT (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _get_PMSCR_EL2_Type_PCT (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def undefined_PMSCR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMSCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_PMSCR_EL2_Type_E0HSPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMSCR_EL2_Type_E2SPE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def undefined_PMBLIMITR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMBLIMITR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMBLIMITR_EL1_Type_FM (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 2 1)

def _update_PMBLIMITR_EL1_Type_FM (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 1 x)

def _get_PMBLIMITR_EL1_Type_LIMIT (v : (BitVec 64)) : (BitVec 52) :=
  (Sail.BitVec.extractLsb v 63 12)

def _update_PMBLIMITR_EL1_Type_LIMIT (v : (BitVec 64)) (x : (BitVec 52)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 12 x)

def _get_PMBLIMITR_EL1_Type_PMFZ (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_PMBLIMITR_EL1_Type_PMFZ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def undefined_PMBSR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMBSR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_PMBSR_EL1_Type_AssuredOnly (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)

def _update_PAR_EL1_Type_AssuredOnly (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_VTCR_EL2_Type_AssuredOnly (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _get_PAR_EL1_Type_AssuredOnly (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_PMBSR_EL1_Type_COLL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMBSR_EL1_Type_DL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMBSR_EL1_Type_DirtyBit (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _update_PAR_EL1_Type_DirtyBit (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_PAR_EL1_Type_DirtyBit (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_PMBSR_EL1_Type_MSS (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_PMBSR_EL1_Type_Overlay (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _update_PAR_EL1_Type_Overlay (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_PAR_EL1_Type_Overlay (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_PMBSR_EL1_Type_S (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_DBGVCR32_EL2_Type_S (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_DBGVCR_Type_S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PAR_EL1_Type_S (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_TTBR0_Type_S (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_TTBR1_Type_S (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_VTCR_Type_S (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_DBGVCR32_EL2_Type_S (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_DBGVCR_Type_S (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PAR_EL1_Type_S (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def undefined_ZCR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ZCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_ZCR_EL1_Type_LEN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_SMCR_EL1_Type_LEN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_SMCR_EL2_Type_LEN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_SMCR_EL3_Type_LEN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ZCR_EL2_Type_LEN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ZCR_EL3_Type_LEN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def undefined_ZCR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ZCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_ZCR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ZCR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_SMCR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SMCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_SMCR_EL1_Type_EZT0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_SMCR_EL1_Type_EZT0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_SMCR_EL2_Type_EZT0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_SMCR_EL3_Type_EZT0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_SMCR_EL2_Type_EZT0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_SMCR_EL3_Type_EZT0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_SMCR_EL1_Type_FA64 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_SMCR_EL1_Type_FA64 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_ID_AA64SMFR0_EL1_Type_FA64 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_SMCR_EL2_Type_FA64 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SMCR_EL3_Type_FA64 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_ID_AA64SMFR0_EL1_Type_FA64 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_SMCR_EL2_Type_FA64 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_SMCR_EL3_Type_FA64 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def undefined_SMCR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SMCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_SMCR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SMCR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_GCSPR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _update_GCSPR_EL0_Type_PTR (v : (BitVec 64)) (x : (BitVec 61)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 3 x)

def _update_GCSPR_EL1_Type_PTR (v : (BitVec 64)) (x : (BitVec 61)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 3 x)

def _update_GCSPR_EL2_Type_PTR (v : (BitVec 64)) (x : (BitVec 61)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 3 x)

def _update_GCSPR_EL3_Type_PTR (v : (BitVec 64)) (x : (BitVec 61)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 3 x)

def _update_PMBPTR_EL1_Type_PTR (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _get_PMBPTR_EL1_Type_PTR (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def undefined_GCSPR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_GCSPR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_GCSPR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_CPACR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CPACR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_CPACR_EL1_Type_E0POE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_CPACR_EL1_Type_E0POE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_CPTR_EL2_Type_E0POE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_TCR2_EL1_Type_E0POE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_TCR2_EL2_Type_E0POE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_CPTR_EL2_Type_E0POE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_CPACR_EL1_Type_FPEN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 20 x)

def _update_CPTR_EL2_Type_FPEN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 20 x)

def _update_CPACR_EL1_Type_SMEN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)

def _update_CPTR_EL2_Type_SMEN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)

def _get_CPACR_EL1_Type_TTA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_CPACR_EL1_Type_TTA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_CPTR_EL3_Type_TTA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_HCPTR_Type_TTA (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_CPTR_EL3_Type_TTA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_HCPTR_Type_TTA (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_CPACR_EL1_Type_ZEN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 16 x)

def _update_CPTR_EL2_Type_ZEN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 16 x)

def undefined_CPTR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CPTR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_CPTR_EL2_Type_TAM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_CPTR_EL2_Type_TAM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_CPTR_EL3_Type_TAM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_HCPTR_Type_TAM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_CPTR_EL3_Type_TAM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_HCPTR_Type_TAM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_CPTR_EL2_Type_TCPAC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_CPTR_EL2_Type_TCPAC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_CPTR_EL3_Type_TCPAC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_HCPTR_Type_TCPAC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_CPTR_EL3_Type_TCPAC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_HCPTR_Type_TCPAC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_CPTR_EL2_Type_TFP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_CPTR_EL3_Type_TFP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_CPTR_EL2_Type_TSM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_CPTR_EL2_Type_TZ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def undefined_CPTR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CPTR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_CPTR_EL3_Type_ESM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_CPTR_EL3_Type_EZ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def undefined_CPACR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CPACR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CPACR_Type_ASEDIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_CPACR_Type_ASEDIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_CPACR_Type_TRCDIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_CPACR_Type_TRCDIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_CPACR_Type_cp10 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 20 x)

def _update_NSACR_Type_cp10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_CPACR_Type_cp11 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)

def _update_CPACR_Type_cp11 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 22 x)

def _update_NSACR_Type_cp11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_NSACR_Type_cp11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def undefined_HCPTR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_HCPTR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_HCPTR_Type_TASE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_HCPTR_Type_TASE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_HCPTR_Type_TCP10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_HCPTR_Type_TCP11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_HCPTR_Type_TCP11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def undefined_NSACR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_NSACR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_NSACR_Type_NSASEDIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_NSACR_Type_NSASEDIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_NSACR_Type_NSTRCDIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_NSACR_Type_NSTRCDIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def undefined_DBGOSDLR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGOSDLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _update_DBGOSDLR_Type_DLK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_EDPRSR_Type_DLK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_OSDLR_EL1_Type_DLK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_EDPRSR_Type_DLK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def undefined_OSDLR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_OSDLR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_DBGPRCR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_DBGPRCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_DBGPRCR_EL1_Type_CORENPDRQ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_DBGPRCR_Type_CORENPDRQ (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_EDPRCR_Type_CORENPDRQ (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_EDPRCR_Type_CORENPDRQ (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def undefined_DBGPRCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGPRCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

/-- Type quantifiers: k_M : Nat, N : Nat, k_M > N ∧ k_M ≥ 0 ∧ 0 ≤ (N - 1) -/
def Split (value_name : (BitVec k_M)) (N : Nat) : SailM ((BitVec (k_M - N)) × (BitVec N)) := do
  sail_assert ((Sail.BitVec.length value_name) >b N) "src/v8_base.sail:8058.17-8058.18"
  (pure ((Sail.BitVec.extractLsb value_name ((Sail.BitVec.length value_name) -i 1) N), (Sail.BitVec.extractLsb value_name (N -i 1) 0)))

/-- Type quantifiers: k_round : Bool, shift : Int, value_name : Int -/
def RShr (value_name : Int) (shift : Int) (round : Bool) : SailM Int := do
  sail_assert (shift >b 0) "src/v8_base.sail:8066.20-8066.21"
  if (round : Bool)
  then (pure (Int.shiftr (value_name +i (Int.shiftl 1 (shift -i 1))) shift))
  else (pure (Int.shiftr value_name shift))

def IsHighestEL (el : (BitVec 2)) : Bool :=
  ((HighestEL ()) == el)

/-- Type quantifiers: k_N : Nat, 4 < k_N -/
def ELFromSPSR (spsr : (BitVec k_N)) : SailM (Bool × (BitVec 2)) := do
  let el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let valid_name ← (( do (undefined_bool ()) ) : SailM Bool )
  let effective_nse_ns ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let (el, valid_name) ← (( do
    if (((BitVec.join1 [(BitVec.access spsr 4)]) == 0#1) : Bool)
    then
      (do
        let el : (BitVec 2) := (Sail.BitVec.extractLsb spsr 3 2)
        let effective_nse_ns ← (( do (pure ((← (EffectiveSCR_EL3_NSE ())) +++ (← (EffectiveSCR_EL3_NS ())))) ) : SailM (BitVec 2) )
        let valid_name ← (( do
          if ((! (← (HaveAArch64 ()))) : Bool)
          then (pure false)
          else
            (do
              if ((! (HaveEL el)) : Bool)
              then (pure false)
              else
                (do
                  if (((BitVec.join1 [(BitVec.access spsr 1)]) == 1#1) : Bool)
                  then (pure false)
                  else
                    (do
                      if (((el == EL0) && ((BitVec.join1 [(BitVec.access spsr 0)]) == 1#1)) : Bool)
                      then (pure false)
                      else
                        (do
                          if ((((← (HaveRME ())) && (el != EL3)) && (effective_nse_ns == 0b10#2)) : Bool)
                          then (pure false)
                          else
                            (do
                              if ((←((pure ((el == EL2) && (HaveEL EL3))) <&&> (do
                                   (pure (! (← (IsSecureEL2Enabled ()))))) <&&> (do
                                   (pure ((_get_SCR_EL3_Type_NS (← readReg SCR_EL3)) == 0#1))))) : Bool)
                              then (pure false)
                              else (pure true)))))) ) : SailM Bool )
        (pure (el, valid_name)))
    else
      (do
        let (el, valid_name) ← (( do
          if ((HaveAArch32 ()) : Bool)
          then
            (do
              let (tup__0, tup__1) ← do (ELFromM32 (Sail.BitVec.extractLsb spsr 4 0))
              let valid_name : Bool := tup__0
              let el : (BitVec 2) := tup__1
              (pure (el, valid_name)))
          else
            (let valid_name : Bool := false
            (pure (el, valid_name))) ) : SailM ((BitVec 2) × Bool) )
        (pure (el, valid_name))) ) : SailM ((BitVec 2) × Bool) )
  let el ← (( do
    if ((! valid_name) : Bool)
    then (do (__UNKNOWN_bits 2))
    else (pure el) ) : SailM (BitVec 2) )
  let el := el
  (pure (valid_name, el))

def ELUsingAArch32K (el : (BitVec 2)) : SailM (Bool × Bool) := do
  (ELStateUsingAArch32K el (← (IsSecureBelowEL3 ())))

def undefined_GCSCR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GCSCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_GCSCR_EL1_Type_EXLOCKEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_GCSCR_EL2_Type_EXLOCKEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_GCSCR_EL3_Type_EXLOCKEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_GCSCR_EL1_Type_PCRSEL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_GCSCRE0_EL1_Type_PCRSEL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_GCSCR_EL2_Type_PCRSEL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_GCSCR_EL3_Type_PCRSEL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_GCSCR_EL1_Type_PUSHMEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_GCSCR_EL1_Type_PUSHMEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_GCSCRE0_EL1_Type_PUSHMEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_GCSCR_EL2_Type_PUSHMEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_GCSCR_EL3_Type_PUSHMEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_GCSCRE0_EL1_Type_PUSHMEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_GCSCR_EL2_Type_PUSHMEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_GCSCR_EL3_Type_PUSHMEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_GCSCR_EL1_Type_RVCHKEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_GCSCRE0_EL1_Type_RVCHKEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_GCSCR_EL2_Type_RVCHKEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_GCSCR_EL3_Type_RVCHKEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_GCSCR_EL1_Type_STREn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_GCSCR_EL1_Type_STREn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_GCSCRE0_EL1_Type_STREn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_GCSCR_EL2_Type_STREn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_GCSCR_EL3_Type_STREn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_GCSCRE0_EL1_Type_STREn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_GCSCR_EL2_Type_STREn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_GCSCR_EL3_Type_STREn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def undefined_GCSCR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GCSCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_GCSCR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GCSCR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_MDSCR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MDSCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_MDSCR_EL1_Type_EHBWE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _update_EDSCR2_Type_EHBWE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_MDSCR_EL1_Type_EMBWE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_MDSCR_EL1_Type_KDE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_MDSCR_EL1_Type_MDE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def undefined_OSLSR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_OSLSR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_OSLSR_EL1_Type_OSLK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_DBGOSLSR_Type_OSLK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_EDPRSR_Type_OSLK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_OSLAR_EL1_Type_OSLK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_EDPRSR_Type_OSLK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_OSLAR_EL1_Type_OSLK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_OSLSR_EL1_Type_OSLM (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 3 3 (Sail.BitVec.extractLsb x (2 -i 1) (((2 -i 1) -i ((3 -i 3) +i 1)) +i 1))) 0 0 (Sail.BitVec.extractLsb x ((2 -i 1) -i ((3 -i 3) +i 1)) ((((2 -i 1) -i ((3 -i 3) +i 1)) -i ((0 -i 0) +i 1)) +i 1)))

def _update_DBGOSLSR_Type_OSLM (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 3 3 (Sail.BitVec.extractLsb x (2 -i 1) (((2 -i 1) -i ((3 -i 3) +i 1)) +i 1))) 0 0 (Sail.BitVec.extractLsb x ((2 -i 1) -i ((3 -i 3) +i 1)) ((((2 -i 1) -i ((3 -i 3) +i 1)) -i ((0 -i 0) +i 1)) +i 1)))

def _get_DBGOSLSR_Type_OSLM (v : (BitVec 32)) : (BitVec 2) :=
  ((Sail.BitVec.extractLsb v 3 3) +++ (Sail.BitVec.extractLsb v 0 0))

def _update_OSLSR_EL1_Type_nTT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_CTILSR_Type_nTT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_DBGOSLSR_Type_nTT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_EDLSR_Type_nTT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMLSR_Type_nTT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_CTILSR_Type_nTT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_DBGOSLSR_Type_nTT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_EDLSR_Type_nTT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMLSR_Type_nTT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def undefined_DBGOSLSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGOSLSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_HCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_HCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_HCR_Type_TAC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_HCR_Type_TAC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_DBGBVR_EL1_Type_VA (v : (BitVec 64)) (x : (BitVec 55)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 56 53 (Sail.BitVec.extractLsb x (55 -i 1) (((55 -i 1) -i ((56 -i 53) +i 1)) +i 1))) 52 49 (Sail.BitVec.extractLsb x ((55 -i 1) -i ((56 -i 53) +i 1)) ((((55 -i 1) -i ((56 -i 53) +i 1)) -i ((52 -i 49) +i 1)) +i 1))) 48 2 (Sail.BitVec.extractLsb x (((55 -i 1) -i ((56 -i 53) +i 1)) -i ((52 -i 49) +i 1)) (((((55 -i 1) -i ((56 -i 53) +i 1)) -i ((52 -i 49) +i 1)) -i ((48 -i 2) +i 1)) +i 1)))

def _update_DBGBVR_Type_VA (v : (BitVec 32)) (x : (BitVec 30)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 2 x)

def _update_DBGWVR_EL1_Type_VA (v : (BitVec 64)) (x : (BitVec 55)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 56 53 (Sail.BitVec.extractLsb x (55 -i 1) (((55 -i 1) -i ((56 -i 53) +i 1)) +i 1))) 52 49 (Sail.BitVec.extractLsb x ((55 -i 1) -i ((56 -i 53) +i 1)) ((((55 -i 1) -i ((56 -i 53) +i 1)) -i ((52 -i 49) +i 1)) +i 1))) 48 2 (Sail.BitVec.extractLsb x (((55 -i 1) -i ((56 -i 53) +i 1)) -i ((52 -i 49) +i 1)) (((((55 -i 1) -i ((56 -i 53) +i 1)) -i ((52 -i 49) +i 1)) -i ((48 -i 2) +i 1)) +i 1)))

def _update_DBGWVR_Type_VA (v : (BitVec 32)) (x : (BitVec 30)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 2 x)

def _set_HCR_Type_VA (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_HCR_Type_VA r v)

def _get_DBGBVR_EL1_Type_VA (v : (BitVec 64)) : (BitVec 55) :=
  ((Sail.BitVec.extractLsb v 56 53) +++ ((Sail.BitVec.extractLsb v 52 49) +++ (Sail.BitVec.extractLsb v 48 2)))

def _get_DBGBVR_Type_VA (v : (BitVec 32)) : (BitVec 30) :=
  (Sail.BitVec.extractLsb v 31 2)

def _get_DBGWVR_EL1_Type_VA (v : (BitVec 64)) : (BitVec 55) :=
  ((Sail.BitVec.extractLsb v 56 53) +++ ((Sail.BitVec.extractLsb v 52 49) +++ (Sail.BitVec.extractLsb v 48 2)))

def _get_DBGWVR_Type_VA (v : (BitVec 32)) : (BitVec 30) :=
  (Sail.BitVec.extractLsb v 31 2)

def Restarting (_ : Unit) : SailM Bool := do
  (pure ((_get_EDSCR_Type_STATUS (← (EDSCR_read ()))) == 0b000001#6))

def undefined_HSCTLR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_HSCTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_HSCTLR_Type_LSMAOE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_HSCTLR_Type_LSMAOE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_SCTLR_EL1_Type_LSMAOE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_SCTLR_EL2_Type_LSMAOE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_SCTLR_Type_LSMAOE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_SCTLR_EL1_Type_LSMAOE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_SCTLR_EL2_Type_LSMAOE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_SCTLR_Type_LSMAOE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_HSCTLR_Type_nTLSMD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_SCTLR_EL1_Type_nTLSMD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_SCTLR_EL2_Type_nTLSMD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_SCTLR_Type_nTLSMD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def undefined_SCTLR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SCTLR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_SCTLR_EL2_Type_ATA0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _update_SCTLR_EL1_Type_ATA0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _get_SCTLR_EL2_Type_BT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)

def _update_SCTLR_EL2_Type_BT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _update_DBGBCR_EL1_Type_BT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_DBGBCR_Type_BT (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_AA64PFR1_EL1_Type_BT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_SCTLR_EL3_Type_BT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _get_ID_AA64PFR1_EL1_Type_BT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_SCTLR_EL2_Type_BT0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)

def _update_SCTLR_EL2_Type_BT0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _update_SCTLR_EL1_Type_BT0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _get_SCTLR_EL1_Type_BT0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)

def _update_SCTLR_EL2_Type_CMOW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_HCRX_EL2_Type_CMOW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_ID_AA64MMFR1_EL1_Type_CMOW (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_SCTLR_EL1_Type_CMOW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _get_ID_AA64MMFR1_EL1_Type_CMOW (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_SCTLR_EL2_Type_EIS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_SCTLR_EL2_Type_EIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_SCTLR_EL1_Type_EIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_SCTLR_EL3_Type_EIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_SCTLR_EL1_Type_EIS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_SCTLR_EL2_Type_EOS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_SCTLR_EL2_Type_EOS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_SCTLR_EL1_Type_EOS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_SCTLR_EL3_Type_EOS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_SCTLR_EL1_Type_EOS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_SCTLR_EL2_Type_EnALS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)

def _update_SCTLR_EL2_Type_EnALS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _update_HCRX_EL2_Type_EnALS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_SCTLR_EL1_Type_EnALS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _get_HCRX_EL2_Type_EnALS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_SCTLR_EL1_Type_EnALS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)

def _get_SCTLR_EL2_Type_EnASR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)

def _update_SCTLR_EL2_Type_EnASR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _update_HCRX_EL2_Type_EnASR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_SCTLR_EL1_Type_EnASR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _get_HCRX_EL2_Type_EnASR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_SCTLR_EL1_Type_EnASR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)

def _get_SCTLR_EL2_Type_EnDA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_SCTLR_EL2_Type_EnDA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_SCTLR_EL1_Type_EnDA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_SCTLR_EL3_Type_EnDA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_SCTLR_EL1_Type_EnDA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_SCTLR_EL2_Type_EnDB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_SCTLR_EL2_Type_EnDB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_SCTLR_EL1_Type_EnDB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_SCTLR_EL3_Type_EnDB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_SCTLR_EL1_Type_EnDB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_SCTLR_EL2_Type_EnIA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SCTLR_EL1_Type_EnIA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SCTLR_EL3_Type_EnIA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SCTLR_EL2_Type_EnIB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_SCTLR_EL1_Type_EnIB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_SCTLR_EL3_Type_EnIB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_SCTLR_EL2_Type_EnRCTX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_SCTLR_EL2_Type_EnRCTX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_SCTLR_EL1_Type_EnRCTX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_SCTLR_Type_EnRCTX (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_SCTLR_EL1_Type_EnRCTX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_SCTLR_Type_EnRCTX (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_SCTLR_EL2_Type_ITFSB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)

def _update_SCTLR_EL2_Type_ITFSB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _update_SCTLR_EL1_Type_ITFSB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _update_SCTLR_EL3_Type_ITFSB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _get_SCTLR_EL1_Type_ITFSB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)

def _get_SCTLR_EL2_Type_MSCEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _update_SCTLR_EL2_Type_MSCEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _update_HCRX_EL2_Type_MSCEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_SCTLR_EL1_Type_MSCEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _get_HCRX_EL2_Type_MSCEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_SCTLR_EL1_Type_MSCEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _update_SCTLR_EL2_Type_TCF (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 40 x)

def _update_SCTLR_EL1_Type_TCF (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 40 x)

def _update_SCTLR_EL3_Type_TCF (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 40 x)

def _update_SCTLR_EL2_Type_TCF0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 38 x)

def _update_SCTLR_EL1_Type_TCF0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 38 x)

def _update_SCTLR_EL2_Type_TCSO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_SCTLR_EL1_Type_TCSO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_SCTLR_EL3_Type_TCSO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_SCTLR_EL2_Type_TCSO0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _update_SCTLR_EL1_Type_TCSO0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def undefined_SCTLR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SCTLR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_SCTLR_EL1_Type_BT1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)

def _update_SCTLR_EL1_Type_BT1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def undefined_SCTLR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SCTLR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_SCTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _update_SCTLR_Type_AFE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_SCTLR_Type_TRE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_SCTLR_Type_UNK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_SCTLR_Type_UNK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SCTLR_Type_UWXN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def IsCurrentSecurityState (ss : SecurityState) : SailM Bool := do
  (pure (BEq.beq (← (CurrentSecurityState ())) ss))

def undefined_ESR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _get_ESR_EL1_Type_ISS2 (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 55 32)

def _update_ESR_EL1_Type_ISS2 (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 32 x)

def _update_ESR_EL2_Type_ISS2 (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 32 x)

def _update_ESR_EL3_Type_ISS2 (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 32 x)

def _get_ESR_EL2_Type_ISS2 (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 55 32)

def _get_ESR_EL3_Type_ISS2 (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 55 32)

def undefined_ESR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_ESR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def ESR_set__1 (value_name : (BitVec 64)) : SailM Unit := do
  (ESR_set (← (S1TranslationRegime__1 ())) value_name)

def undefined_HPFAR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_HPFAR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_HPFAR_EL2_Type_FIPA (v : (BitVec 64)) : (BitVec 44) :=
  (Sail.BitVec.extractLsb v 47 4)

def _update_HPFAR_EL2_Type_FIPA (v : (BitVec 64)) (x : (BitVec 44)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 4 x)

def _update_HPFAR_Type_FIPA (v : (BitVec 32)) (x : (BitVec 28)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 4 x)

def _get_HPFAR_Type_FIPA (v : (BitVec 32)) : (BitVec 28) :=
  (Sail.BitVec.extractLsb v 31 4)

def undefined_MFAR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _get_MFAR_EL3_Type_FPA (v : (BitVec 64)) : (BitVec 44) :=
  ((Sail.BitVec.extractLsb v 55 52) +++ ((Sail.BitVec.extractLsb v 51 48) +++ (Sail.BitVec.extractLsb v 47 12)))

def _update_MFAR_EL3_Type_FPA (v : (BitVec 64)) (x : (BitVec 44)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 55 52 (Sail.BitVec.extractLsb x (44 -i 1) (((44 -i 1) -i ((55 -i 52) +i 1)) +i 1))) 51 48 (Sail.BitVec.extractLsb x ((44 -i 1) -i ((55 -i 52) +i 1)) ((((44 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) +i 1))) 47 12 (Sail.BitVec.extractLsb x (((44 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) (((((44 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) -i ((47 -i 12) +i 1)) +i 1)))

def undefined_PFAR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_PFAR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_SPSR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SPSR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_SPSR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SPSR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_SPSR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SPSR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_SPSR_abt_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SPSR_abt_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_SPSR_abt_Type_J (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_SPSR_abt_Type_J (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_SPSR_fiq_Type_J (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_SPSR_hyp_Type_J (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_SPSR_irq_Type_J (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_SPSR_mon_Type_J (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_SPSR_svc_Type_J (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_SPSR_und_Type_J (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_SPSR_fiq_Type_J (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_SPSR_hyp_Type_J (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_SPSR_irq_Type_J (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_SPSR_mon_Type_J (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_SPSR_svc_Type_J (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_SPSR_und_Type_J (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def undefined_SPSR_fiq_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SPSR_fiq_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_SPSR_hyp_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_SPSR_irq_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SPSR_irq_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_SPSR_mon_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_SPSR_mon_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_SPSR_svc_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_SPSR_und_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SPSR_und_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_EDECCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDECCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_EDECCR_Type_NSE0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_EDECCR_Type_NSE0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_EDECCR_Type_NSE1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_EDECCR_Type_NSE1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_EDECCR_Type_NSE2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_EDECCR_Type_NSE2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_EDECCR_Type_NSE3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_EDECCR_Type_NSE3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_EDECCR_Type_NSR0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_EDECCR_Type_NSR0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_EDECCR_Type_NSR1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_EDECCR_Type_NSR1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_EDECCR_Type_NSR2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_EDECCR_Type_NSR2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_EDECCR_Type_NSR3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_EDECCR_Type_NSR3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_EDECCR_Type_RLE0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_EDECCR_Type_RLE0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_EDECCR_Type_RLE1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_EDECCR_Type_RLE1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_EDECCR_Type_RLE2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_EDECCR_Type_RLE2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_EDECCR_Type_RLR0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_EDECCR_Type_RLR0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_EDECCR_Type_RLR1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_EDECCR_Type_RLR1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_EDECCR_Type_RLR2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_EDECCR_Type_RLR2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_EDECCR_Type_SE0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_EDECCR_Type_SE0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_EDECCR_Type_SE1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_EDECCR_Type_SE1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_EDECCR_Type_SE2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_EDECCR_Type_SE2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_EDECCR_Type_SE3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_EDECCR_Type_SE3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_EDECCR_Type_SR0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_EDECCR_Type_SR0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_EDECCR_Type_SR1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_EDECCR_Type_SR1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_EDECCR_Type_SR2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_EDECCR_Type_SR2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_EDECCR_Type_SR3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_EDECCR_Type_SR3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def undefined_OSECCR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_OSECCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_OSECCR_EL1_Type_EDECCR (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_OSECCR_EL1_Type_EDECCR (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_DBGOSECCR_Type_EDECCR (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _get_DBGOSECCR_Type_EDECCR (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def undefined_EDESR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDESR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _update_EDESR_Type_OSUC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_EDESR_Type_RC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def AArch64_BranchTargetException (vaddress : (BitVec 52)) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_BranchTarget) ) : SailM ExceptionRecord )
  let except ← (pure { except with syndrome := ← (do (pure (Sail.BitVec.updateSubrange except.syndrome 1 0 (← readReg PSTATE).BTYPE))) })
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 24 2 (Zeros (n := 23))) }
  let target_el : (BitVec 2) := EL1
  let target_el ← (( do
    if (((BitVec.toNat (← readReg PSTATE).EL) >b (BitVec.toNat EL1)) : Bool)
    then (do (pure (← readReg PSTATE).EL))
    else
      (do
        if ((←((pure ((← readReg PSTATE).EL == EL0)) <&&> (do
             (EL2Enabled ())) <&&> (do
             (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
        then (pure EL2)
        else (pure target_el)) ) : SailM (BitVec 2) )
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)

def AArch64_ExecutingBROrBLROrRetInstr (_ : Unit) : SailM Bool := do
  let opc ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  if ((! (← (HaveBTIExt ()))) : Bool)
  then (pure false)
  else
    (do
      let instr ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
      if ((((Sail.BitVec.extractLsb instr 31 25) == 0b1101011#7) && ((Sail.BitVec.extractLsb instr 20 16) == 0b11111#5)) : Bool)
      then
        (let opc : (BitVec 4) := (Sail.BitVec.extractLsb instr 24 21)
        (pure (opc != 0b0101#4)))
      else (pure false))

def AArch64_ExecutingBTIInstr (_ : Unit) : SailM Bool := do
  let CRm ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let op2 ← (( do (undefined_bitvector 3) ) : SailM (BitVec 3) )
  if ((! (← (HaveBTIExt ()))) : Bool)
  then (pure false)
  else
    (do
      let instr ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
      if (((((Sail.BitVec.extractLsb instr 31 22) == 0b1101010100#10) && ((Sail.BitVec.extractLsb instr 21 12) == 0b0000110010#10)) && ((Sail.BitVec.extractLsb instr 4 0) == 0b11111#5)) : Bool)
      then
        (let CRm : (BitVec 4) := (Sail.BitVec.extractLsb instr 11 8)
        let op2 : (BitVec 3) := (Sail.BitVec.extractLsb instr 7 5)
        (pure ((CRm == 0b0100#4) && ((BitVec.join1 [(BitVec.access op2 0)]) == 0#1))))
      else (pure false))

def AArch32_CurrentCond (_ : Unit) : SailM (BitVec 4) := do
  readReg __currentCond

def ClearEventRegister (_ : Unit) : SailM Unit := do
  writeReg EventRegister 0#1

def IsEventRegisterSet (_ : Unit) : SailM Bool := do
  (pure ((← readReg EventRegister) == 1#1))

def EnterLowPowerState (_ : Unit) : Unit :=
  ()

/-- Type quantifiers: localtimeout : Int -/
def LocalTimeoutEvent (localtimeout : Int) : SailM Bool := do
  (__UNKNOWN_boolean ())

/-- Type quantifiers: delay : Int, k_delay_enabled : Bool -/
def WaitForEventUntilDelay (delay_enabled : Bool) (delay : Int) : SailM Bool := do
  (__UNKNOWN_boolean ())

def IsVirtualSErrorPending (_ : Unit) : SailM Bool := do
  if ((← (ELUsingAArch32 EL2)) : Bool)
  then (pure ((_get_HCR_Type_VA (← (HCR_read ()))) == 1#1))
  else (pure ((_get_HCR_EL2_Type_VSE (← readReg HCR_EL2)) == 1#1))

def VirtualFIQPending (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())

def VirtualIRQPending (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())

def SendEventLocal (_ : Unit) : SailM Unit := do
  writeReg EventRegister 1#1

def undefined_GCSCRE0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GCSCRE0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_GCSCRE0_EL1_Type_nTR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_GCSCRE0_EL1_Type_nTR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def undefined_HCRX_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_HCRX_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_HCRX_EL2_Type_EnSDERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_HCRX_EL2_Type_EnSDERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_HCRX_EL2_Type_EnSNERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_HCRX_EL2_Type_EnSNERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_HCRX_EL2_Type_FGTnXS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_HCRX_EL2_Type_FGTnXS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_HCRX_EL2_Type_FnXS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_HCRX_EL2_Type_FnXS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_HCRX_EL2_Type_MCE2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_HCRX_EL2_Type_MCE2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_HCRX_EL2_Type_SMPME (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_HCRX_EL2_Type_SMPME (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_HCRX_EL2_Type_TALLINT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_HCRX_EL2_Type_TALLINT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_HCRX_EL2_Type_VFNMI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_HCRX_EL2_Type_VINMI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def AArch64_ChkFeat (feat_select : (BitVec 64)) : SailM (BitVec 64) := do
  let feat_en : (BitVec 64) := (Zeros (n := 64))
  let feat_en ←
    (pure (BitVec.update feat_en 0
        (Bit
          (← (do
            if ((←((HaveGCS ()) <&&> (do
                 (GCSEnabled (← readReg PSTATE).EL)))) : Bool)
            then (pure 1#1)
            else (pure 0#1))))))
  (pure (feat_select &&& (Complement.complement feat_en)))

def TAG_GRANULE : Nat := 16

def undefined_MPAM2_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPAM2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_MPAM2_EL2_Type_ALTSP_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _get_MPAM2_EL2_Type_ALTSP_FRCD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)

def _update_MPAM2_EL2_Type_ALTSP_FRCD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _update_MPAM1_EL1_Type_ALTSP_FRCD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _get_MPAM1_EL1_Type_ALTSP_FRCD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)

def _update_MPAM2_EL2_Type_ALTSP_HFC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _update_MPAM3_EL3_Type_ALTSP_HFC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _get_MPAM2_EL2_Type_EnMPAMSM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)

def _update_MPAM2_EL2_Type_EnMPAMSM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _update_MPAM2_EL2_Type_MPAMEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_MPAM1_EL1_Type_MPAMEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_MPAM3_EL3_Type_MPAMEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_MPAM2_EL2_Type_PARTID_D (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)

def _update_MPAM0_EL1_Type_PARTID_D (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)

def _update_MPAM1_EL1_Type_PARTID_D (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)

def _update_MPAM3_EL3_Type_PARTID_D (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)

def _update_MPAMSM_EL1_Type_PARTID_D (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)

def _update_MPAM2_EL2_Type_PARTID_I (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_MPAM0_EL1_Type_PARTID_I (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_MPAM1_EL1_Type_PARTID_I (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_MPAM3_EL3_Type_PARTID_I (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_MPAM2_EL2_Type_PMG_D (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)

def _update_MPAM0_EL1_Type_PMG_D (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)

def _update_MPAM1_EL1_Type_PMG_D (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)

def _update_MPAM3_EL3_Type_PMG_D (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)

def _update_MPAMSM_EL1_Type_PMG_D (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)

def _update_MPAM2_EL2_Type_PMG_I (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _update_MPAM0_EL1_Type_PMG_I (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _update_MPAM1_EL1_Type_PMG_I (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _update_MPAM3_EL3_Type_PMG_I (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _get_MPAM2_EL2_Type_TIDR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _update_MPAM2_EL2_Type_TIDR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _get_MPAM2_EL2_Type_TRAPMPAM0EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)

def _update_MPAM2_EL2_Type_TRAPMPAM0EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def _get_MPAM2_EL2_Type_TRAPMPAM1EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _update_MPAM2_EL2_Type_TRAPMPAM1EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def undefined_MPAM3_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPAM3_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_MPAM3_EL3_Type_ALTSP_EL3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _update_MPAM3_EL3_Type_ALTSP_HEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _update_MPAM3_EL3_Type_FORCE_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _update_MPAM3_EL3_Type_RT_ALTSP_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _update_MPAM3_EL3_Type_SDEFLT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_MPAM3_EL3_Type_TRAPLOWER (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def undefined_MPAM1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPAM1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MPAM1_EL1_Type_FORCED_NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _update_MPAM1_EL1_Type_FORCED_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def undefined_MPAMIDR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPAMIDR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_MPAMIDR_EL1_Type_HAS_ALTSP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _update_MPAMIDR_EL1_Type_HAS_FORCE_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _update_MPAMIDR_EL1_Type_HAS_HCR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_MPAMIDR_EL1_Type_HAS_SDEFLT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _get_MPAMIDR_EL1_Type_HAS_TIDR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _update_MPAMIDR_EL1_Type_HAS_TIDR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _update_MPAMIDR_EL1_Type_PARTID_MAX (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_MPAMIDR_EL1_Type_PMG_MAX (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _get_MPAMIDR_EL1_Type_SP4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _update_MPAMIDR_EL1_Type_SP4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_MPAMIDR_EL1_Type_VPMR_MAX (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 18 x)

def undefined_MPAMHCR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPAMHCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_MPAMHCR_EL2_Type_EL0_VPMEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_MPAMHCR_EL2_Type_EL1_VPMEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_MPAMHCR_EL2_Type_GSTAPP_PLK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_MPAMHCR_EL2_Type_TRAP_MPAMIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_MPAMHCR_EL2_Type_TRAP_MPAMIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def undefined_MPAMVPM0_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPAMVPM0_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MPAMVPM0_EL2_Type_PhyPARTID0 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _update_MPAMVPM0_EL2_Type_PhyPARTID0 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _get_MPAMVPM0_EL2_Type_PhyPARTID1 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)

def _update_MPAMVPM0_EL2_Type_PhyPARTID1 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)

def _get_MPAMVPM0_EL2_Type_PhyPARTID2 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)

def _update_MPAMVPM0_EL2_Type_PhyPARTID2 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)

def _get_MPAMVPM0_EL2_Type_PhyPARTID3 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)

def _update_MPAMVPM0_EL2_Type_PhyPARTID3 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 48 x)

def undefined_MPAMVPMV_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPAMVPMV_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MPAMVPMV_EL2_Type_VPM_V0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_MPAMVPMV_EL2_Type_VPM_V0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_MPAMVPMV_EL2_Type_VPM_V1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_MPAMVPMV_EL2_Type_VPM_V1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_MPAMVPMV_EL2_Type_VPM_V10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_MPAMVPMV_EL2_Type_VPM_V10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_MPAMVPMV_EL2_Type_VPM_V11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_MPAMVPMV_EL2_Type_VPM_V11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_MPAMVPMV_EL2_Type_VPM_V12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_MPAMVPMV_EL2_Type_VPM_V12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_MPAMVPMV_EL2_Type_VPM_V13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_MPAMVPMV_EL2_Type_VPM_V13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_MPAMVPMV_EL2_Type_VPM_V14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_MPAMVPMV_EL2_Type_VPM_V14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_MPAMVPMV_EL2_Type_VPM_V15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_MPAMVPMV_EL2_Type_VPM_V15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_MPAMVPMV_EL2_Type_VPM_V16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_MPAMVPMV_EL2_Type_VPM_V16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_MPAMVPMV_EL2_Type_VPM_V17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_MPAMVPMV_EL2_Type_VPM_V17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_MPAMVPMV_EL2_Type_VPM_V18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_MPAMVPMV_EL2_Type_VPM_V18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_MPAMVPMV_EL2_Type_VPM_V19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_MPAMVPMV_EL2_Type_VPM_V19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_MPAMVPMV_EL2_Type_VPM_V2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_MPAMVPMV_EL2_Type_VPM_V2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_MPAMVPMV_EL2_Type_VPM_V20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_MPAMVPMV_EL2_Type_VPM_V20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_MPAMVPMV_EL2_Type_VPM_V21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_MPAMVPMV_EL2_Type_VPM_V21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_MPAMVPMV_EL2_Type_VPM_V22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_MPAMVPMV_EL2_Type_VPM_V22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_MPAMVPMV_EL2_Type_VPM_V23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_MPAMVPMV_EL2_Type_VPM_V23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_MPAMVPMV_EL2_Type_VPM_V24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_MPAMVPMV_EL2_Type_VPM_V24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_MPAMVPMV_EL2_Type_VPM_V25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_MPAMVPMV_EL2_Type_VPM_V25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_MPAMVPMV_EL2_Type_VPM_V26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_MPAMVPMV_EL2_Type_VPM_V26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_MPAMVPMV_EL2_Type_VPM_V27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_MPAMVPMV_EL2_Type_VPM_V27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_MPAMVPMV_EL2_Type_VPM_V28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_MPAMVPMV_EL2_Type_VPM_V28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_MPAMVPMV_EL2_Type_VPM_V29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_MPAMVPMV_EL2_Type_VPM_V29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_MPAMVPMV_EL2_Type_VPM_V3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_MPAMVPMV_EL2_Type_VPM_V3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_MPAMVPMV_EL2_Type_VPM_V30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_MPAMVPMV_EL2_Type_VPM_V30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_MPAMVPMV_EL2_Type_VPM_V31 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_MPAMVPMV_EL2_Type_VPM_V31 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_MPAMVPMV_EL2_Type_VPM_V4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_MPAMVPMV_EL2_Type_VPM_V4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_MPAMVPMV_EL2_Type_VPM_V5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_MPAMVPMV_EL2_Type_VPM_V5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_MPAMVPMV_EL2_Type_VPM_V6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_MPAMVPMV_EL2_Type_VPM_V6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_MPAMVPMV_EL2_Type_VPM_V7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_MPAMVPMV_EL2_Type_VPM_V7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_MPAMVPMV_EL2_Type_VPM_V8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_MPAMVPMV_EL2_Type_VPM_V8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_MPAMVPMV_EL2_Type_VPM_V9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_MPAMVPMV_EL2_Type_VPM_V9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def undefined_MPAMVPM1_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPAMVPM1_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MPAMVPM1_EL2_Type_PhyPARTID4 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _update_MPAMVPM1_EL2_Type_PhyPARTID4 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _get_MPAMVPM1_EL2_Type_PhyPARTID5 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)

def _update_MPAMVPM1_EL2_Type_PhyPARTID5 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)

def _get_MPAMVPM1_EL2_Type_PhyPARTID6 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)

def _update_MPAMVPM1_EL2_Type_PhyPARTID6 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)

def _get_MPAMVPM1_EL2_Type_PhyPARTID7 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)

def _update_MPAMVPM1_EL2_Type_PhyPARTID7 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 48 x)

def undefined_MPAMVPM2_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPAMVPM2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MPAMVPM2_EL2_Type_PhyPARTID10 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)

def _update_MPAMVPM2_EL2_Type_PhyPARTID10 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)

def _get_MPAMVPM2_EL2_Type_PhyPARTID11 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)

def _update_MPAMVPM2_EL2_Type_PhyPARTID11 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 48 x)

def _get_MPAMVPM2_EL2_Type_PhyPARTID8 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _update_MPAMVPM2_EL2_Type_PhyPARTID8 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _get_MPAMVPM2_EL2_Type_PhyPARTID9 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)

def _update_MPAMVPM2_EL2_Type_PhyPARTID9 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)

def undefined_MPAMVPM3_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPAMVPM3_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MPAMVPM3_EL2_Type_PhyPARTID12 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _update_MPAMVPM3_EL2_Type_PhyPARTID12 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _get_MPAMVPM3_EL2_Type_PhyPARTID13 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)

def _update_MPAMVPM3_EL2_Type_PhyPARTID13 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)

def _get_MPAMVPM3_EL2_Type_PhyPARTID14 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)

def _update_MPAMVPM3_EL2_Type_PhyPARTID14 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)

def _get_MPAMVPM3_EL2_Type_PhyPARTID15 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)

def _update_MPAMVPM3_EL2_Type_PhyPARTID15 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 48 x)

def undefined_MPAMVPM4_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPAMVPM4_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MPAMVPM4_EL2_Type_PhyPARTID16 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _update_MPAMVPM4_EL2_Type_PhyPARTID16 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _get_MPAMVPM4_EL2_Type_PhyPARTID17 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)

def _update_MPAMVPM4_EL2_Type_PhyPARTID17 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)

def _get_MPAMVPM4_EL2_Type_PhyPARTID18 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)

def _update_MPAMVPM4_EL2_Type_PhyPARTID18 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)

def _get_MPAMVPM4_EL2_Type_PhyPARTID19 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)

def _update_MPAMVPM4_EL2_Type_PhyPARTID19 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 48 x)

def undefined_MPAMVPM5_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPAMVPM5_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MPAMVPM5_EL2_Type_PhyPARTID20 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _update_MPAMVPM5_EL2_Type_PhyPARTID20 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _get_MPAMVPM5_EL2_Type_PhyPARTID21 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)

def _update_MPAMVPM5_EL2_Type_PhyPARTID21 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)

def _get_MPAMVPM5_EL2_Type_PhyPARTID22 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)

def _update_MPAMVPM5_EL2_Type_PhyPARTID22 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)

def _get_MPAMVPM5_EL2_Type_PhyPARTID23 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)

def _update_MPAMVPM5_EL2_Type_PhyPARTID23 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 48 x)

def undefined_MPAMVPM6_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPAMVPM6_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MPAMVPM6_EL2_Type_PhyPARTID24 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _update_MPAMVPM6_EL2_Type_PhyPARTID24 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _get_MPAMVPM6_EL2_Type_PhyPARTID25 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)

def _update_MPAMVPM6_EL2_Type_PhyPARTID25 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)

def _get_MPAMVPM6_EL2_Type_PhyPARTID26 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)

def _update_MPAMVPM6_EL2_Type_PhyPARTID26 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)

def _get_MPAMVPM6_EL2_Type_PhyPARTID27 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)

def _update_MPAMVPM6_EL2_Type_PhyPARTID27 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 48 x)

def undefined_MPAMVPM7_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPAMVPM7_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_MPAMVPM7_EL2_Type_PhyPARTID28 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _update_MPAMVPM7_EL2_Type_PhyPARTID28 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _get_MPAMVPM7_EL2_Type_PhyPARTID29 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)

def _update_MPAMVPM7_EL2_Type_PhyPARTID29 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)

def _get_MPAMVPM7_EL2_Type_PhyPARTID30 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)

def _update_MPAMVPM7_EL2_Type_PhyPARTID30 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)

def _get_MPAMVPM7_EL2_Type_PhyPARTID31 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)

def _update_MPAMVPM7_EL2_Type_PhyPARTID31 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 48 x)

def undefined_MPAM0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPAM0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_MPAMSM_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MPAMSM_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

/-- Type quantifiers: k_acqrel : Bool, k_tagchecked : Bool -/
def CreateAccDescExLDST (memop : MemOp) (acqrel : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with acqsc := (acqrel && (BEq.beq memop MemOp_LOAD)) }
  let accdesc : AccessDescriptor := { accdesc with relsc := (acqrel && (BEq.beq memop MemOp_STORE)) }
  let accdesc : AccessDescriptor := { accdesc with exclusive := true }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

def CreateAccDescLDGSTG (memop : MemOp) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagaccess := true }
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

/-- Type quantifiers: k_nontemporal : Bool, k_privileged : Bool -/
def CreateAccDescMOPS (memop : MemOp) (privileged : Bool) (nontemporal : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc ←
    (pure { accdesc with el := ← (do 
        if ((! privileged) : Bool)
        then (pure EL0)
        else (pure (← readReg PSTATE).EL)) })
  let accdesc : AccessDescriptor := { accdesc with nontemporal := nontemporal }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with mops := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := true }
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

/-- Type quantifiers: k_nontemporal : Bool, k_privileged : Bool -/
def CreateAccDescSTGMOPS (privileged : Bool) (nontemporal : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc ←
    (pure { accdesc with el := ← (do 
        if ((! privileged) : Bool)
        then (pure EL0)
        else (pure (← readReg PSTATE).EL)) })
  let accdesc : AccessDescriptor := { accdesc with nontemporal := nontemporal }
  let accdesc : AccessDescriptor := { accdesc with write := true }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with mops := true }
  let accdesc : AccessDescriptor := { accdesc with tagaccess := true }
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

/-- Type quantifiers: k_acquire : Bool, k_release : Bool, k_tagchecked : Bool -/
def CreateAccDescAtomicOp (modop : MemAtomicOp) (acquire : Bool) (release : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with acqsc := acquire }
  let accdesc : AccessDescriptor := { accdesc with relsc := release }
  let accdesc : AccessDescriptor := { accdesc with atomicop := true }
  let accdesc : AccessDescriptor := { accdesc with modop := modop }
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with write := true }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

/-- Type quantifiers: k_acquire : Bool, k_release : Bool, k_soft : Bool, k_tagchecked : Bool -/
def CreateAccDescRCW (modop : MemAtomicOp) (soft : Bool) (acquire : Bool) (release : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with acqsc := acquire }
  let accdesc : AccessDescriptor := { accdesc with relsc := release }
  let accdesc : AccessDescriptor := { accdesc with rcw := true }
  let accdesc : AccessDescriptor := { accdesc with rcws := soft }
  let accdesc : AccessDescriptor := { accdesc with atomicop := true }
  let accdesc : AccessDescriptor := { accdesc with modop := modop }
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with write := true }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

/-- Type quantifiers: k_tagchecked : Bool -/
def CreateAccDescAcqRel (memop : MemOp) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with acqsc := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with relsc := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

/-- Type quantifiers: k_tagchecked : Bool -/
def CreateAccDescLOR (memop : MemOp) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with acqsc := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with relsc := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with limitedordered := true }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

/-- Type quantifiers: k_tagchecked : Bool -/
def CreateAccDescLDAcqPC (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with acqpc := true }
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

def CreateAccDescA32LSMD (memop : MemOp) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with a32lsmd := true }
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

/-- Type quantifiers: k_tagchecked : Bool -/
def CreateAccDescLS64 (memop : MemOp) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPR) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with ls64 := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

def InStreamingMode (_ : Unit) : SailM Bool := do
  (HaveSME ()) <&&> (do
    (pure ((← readReg PSTATE).SM == 1#1)))

def CreateAccDescIC (cache : CacheRecord) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_IC) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with cacheop := cache.cacheop }
  let accdesc : AccessDescriptor := { accdesc with cachetype := cache.cachetype }
  (pure { accdesc with opscope := cache.opscope })

def CreateAccDescDC (cache : CacheRecord) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_DC) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with cacheop := cache.cacheop }
  let accdesc : AccessDescriptor := { accdesc with cachetype := cache.cachetype }
  (pure { accdesc with opscope := cache.opscope })

/-- Type quantifiers: k_tagaccess : Bool, k_tagchecked : Bool -/
def CreateAccDescDCZero (tagaccess : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_DCZero) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with write := true }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with tagchecked := tagchecked }
  let accdesc : AccessDescriptor := { accdesc with tagaccess := tagaccess }
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

/-- Type quantifiers: k_pan : Bool, k_write : Bool -/
def CreateAccDescAT (ss : SecurityState) (el : (BitVec 2)) (write : Bool) (pan : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_AT) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with el := el }
  let accdesc : AccessDescriptor := { accdesc with ss := ss }
  let accdesc : AccessDescriptor := { accdesc with read := (! write) }
  let accdesc : AccessDescriptor := { accdesc with write := write }
  (pure { accdesc with pan := pan })

/-- Type quantifiers: k_contiguous : Bool, k_nontemporal : Bool, k_tagchecked : Bool -/
def CreateAccDescSME (memop : MemOp) (nontemporal : Bool) (contiguous : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_SME) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with nontemporal := nontemporal }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with contiguous := contiguous }
  let accdesc : AccessDescriptor := { accdesc with streamingsve := true }
  let accdesc ← (( do
    if ((← (__IMPDEF_boolean "No tag checking of SME LDR & STR instructions")) : Bool)
    then (pure { accdesc with tagchecked := false })
    else (pure { accdesc with tagchecked := tagchecked }) ) : SailM AccessDescriptor )
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

def CreateAccDescNV2 (memop : MemOp) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_NV2) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with el := EL2 }
  let accdesc ← (pure { accdesc with ss := ← (do (SecurityStateAtEL EL2)) })
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  (pure { accdesc with transactional := ← (do (HaveTME ()) <&&> (do (pure ((← readReg TSTATE).depth >b 0)))) })

def CreateAccDescSPE (owning_ss : SecurityState) (owning_el : (BitVec 2)) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_SPE) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with el := owning_el }
  let accdesc : AccessDescriptor := { accdesc with ss := owning_ss }
  let accdesc : AccessDescriptor := { accdesc with write := true }
  (pure { accdesc with mpam := ← (do (GenMPAMatEL AccessType_SPE owning_el)) })

def CreateAccDescGCSSS1 (el : (BitVec 2)) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GCS) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with el := el }
  let accdesc : AccessDescriptor := { accdesc with atomicop := true }
  let accdesc : AccessDescriptor := { accdesc with modop := MemAtomicOp_GCSSS1 }
  let accdesc : AccessDescriptor := { accdesc with read := true }
  (pure { accdesc with write := true })

def CPASAtPAS (pas : PASpace) : CachePASpace :=
  match pas with
  | .PAS_NonSecure => CPAS_NonSecure
  | .PAS_Secure => CPAS_Secure
  | .PAS_Root => CPAS_Root
  | .PAS_Realm => CPAS_Realm

def CPASAtSecurityState (ss : SecurityState) : CachePASpace :=
  match ss with
  | .SS_NonSecure => CPAS_NonSecure
  | .SS_Secure => CPAS_SecureNonSecure
  | .SS_Root => CPAS_Any
  | .SS_Realm => CPAS_RealmNonSecure

def ICInstNeedsTranslation (opscope : CacheOpScope) : SailM Bool := do
  (__IMPDEF_boolean "Instruction Cache needs translation")


