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

def undefined_Configuration_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_Configuration_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_Configuration_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _update_Configuration_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ACCDATA_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_AMCFGR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_AMCFGR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMCG1IDR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_AMCGCR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_AMCGCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMCIDR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMCIDR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMCIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMCIDR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMCNTENCLR0_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_AMCNTENCLR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMCNTENCLR1_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_AMCNTENCLR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMCNTENSET0_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_AMCNTENSET0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMCNTENSET1_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_AMCNTENSET1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMCR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_AMCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMDEVARCH_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMDEVTYPE_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMEVCNTR0_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_AMEVCNTR0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_AMEVCNTR1_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_AMEVCNTR1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_AMEVTYPER0_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_AMEVTYPER0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMEVTYPER1_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_AMEVTYPER1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMIIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMPIDR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMPIDR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMPIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMPIDR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMPIDR4_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_AMUSERENR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_AMUSERENR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_BRBCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_BRBCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_BRBFCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_BRBIDR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_BRBINFINJ_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_BRBINFType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_BRBINF_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_BRBSRCINJ_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_BRBSRCType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_BRBSRC_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_BRBTGTINJ_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_BRBTGTType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_BRBTGT_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_BRBTS_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CCSIDR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CCSIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CCSIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CCSIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CLIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CLIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CNTCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CNTEL0ACR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CNTFID0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CNTHCTL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTHCTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CNTHPS_CTL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTHPS_CTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CNTHPS_CVAL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTHPS_TVAL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTHP_CTL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTHP_CTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CNTHP_CVAL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTHP_CVAL_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTHP_TVAL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTHVS_CTL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTHVS_CTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CNTHVS_CVAL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTHVS_TVAL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTHV_CTL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTHV_CTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CNTHV_CVAL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTHV_TVAL_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTID_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CNTKCTL_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTKCTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CNTNSAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CNTPS_CTL_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTPS_CVAL_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTPS_TVAL_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTP_CTL_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTP_CTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CNTP_CVAL_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTP_CVAL_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTP_TVAL_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTSCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CNTSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CNTV_CTL_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTV_CTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CNTV_CVAL_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTV_CVAL_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CNTV_TVAL_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CONTEXTIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CONTEXTIDR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CONTEXTIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CPACR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CPACR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CPTR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CPTR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CSSELR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CSSELR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTIAUTHSTATUS_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTICIDR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTICIDR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTICIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTICIDR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTICONTROL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTIDEVARCH_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTIDEVCTL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTIDEVID_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTIDEVTYPE_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTIITCTRL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTILAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTILSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTIPIDR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTIPIDR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTIPIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTIPIDR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTIPIDR4_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_CTR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_CTR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DACR32_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_DACR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGAUTHSTATUS_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_DBGAUTHSTATUS_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGBCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_DBGBCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGBVR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_DBGBVR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGBXVR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGCLAIMCLR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_DBGCLAIMCLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGCLAIMSET_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_DBGCLAIMSET_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGDCCINT_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGDEVID1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGDEVID_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGDIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGDRAR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_DBGDSCRext_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGDSCRint_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGDTRRXext_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGDTRRXint_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGDTRTXext_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGDTRTXint_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGDTR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_DBGOSDLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGOSECCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGOSLAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGOSLSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGPRCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_DBGPRCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGVCR32_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_DBGVCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGWCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_DBGWCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DBGWVR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_DBGWVR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DCZID_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_DFSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DISR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_DISR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DSPSR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DSPSR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_DSPSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_DormantCtl_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDAA32PFR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_EDCIDR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDCIDR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDCIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDCIDR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDDEVARCH_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDDEVID1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDDEVID_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDDEVTYPE_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDDFR1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_EDDFR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_EDECCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDECR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDESR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDHSR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_EDITCTRL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDLAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDLSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDPCSR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_EDPFR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_EDPIDR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDPIDR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDPIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDPIDR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDPIDR4_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDPRCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDPRSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDRCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDSCR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDSCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_EDVIDSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ERRIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ERRIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ERRSELR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ERRSELR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ERRnFR_ElemType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ERXGSR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ESRType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ESR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ESR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ESR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_FPCRType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_FPCR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_FPEXC32_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_FPEXC_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_FPSCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_FPSID_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_FPSR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GCSCRE0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GCSCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GCSCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GCSCR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GCSPR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GCSPR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GCSPR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GCSPR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GICC_ABPR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICC_AEOIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICC_AHPPIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICC_AIAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICC_BPR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICC_CTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICC_DIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICC_EOIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICC_HPPIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICC_IAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICC_PMR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICC_RPR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICC_STATUSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICD_CLRSPI_NSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICD_CLRSPI_SR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICD_CTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICD_IIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICD_SETSPI_NSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICD_SETSPI_SR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICD_SGIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICD_STATUSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICD_TYPER2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICD_TYPER_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICH_EISR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICH_ELRSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICH_HCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICH_MISR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICH_VMCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICH_VTR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICM_CLRSPI_NSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICM_CLRSPI_SR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICM_IIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICM_SETSPI_NSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICM_SETSPI_SR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICM_TYPER_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICR_CLRLPIR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GICR_CTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICR_IIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICR_INMIR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICR_INVALLR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GICR_INVLPIR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GICR_ISENABLER0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICR_MPAMIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICR_PARTIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICR_PENDBASER_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GICR_PROPBASER_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GICR_SETLPIR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GICR_STATUSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICR_SYNCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICR_VPENDBASER_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GICR_VPROPBASER_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GICR_VSGIPENDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICR_VSGIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICR_WAKER_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICV_ABPR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICV_AEOIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICV_AHPPIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICV_AIAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICV_BPR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICV_CTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICV_DIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICV_EOIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICV_HPPIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICV_IAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICV_PMR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICV_RPR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GICV_STATUSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GITS_CBASER_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GITS_CREADR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GITS_CTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GITS_CWRITER_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GITS_IIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GITS_MPAMIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GITS_MPIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GITS_PARTIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GITS_SGIR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GITS_STATUSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_GITS_TYPER_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GMID_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GPCCR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_GPTBR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_HAFGRTR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_HCPTR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_HCR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_HCRX_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_HCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_HCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_HDCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_HDFGRTR2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_HDFGRTR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_HDFGWTR2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_HDFGWTR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_HFGITR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_HFGRTR2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_HFGRTR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_HFGWTR2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_HFGWTR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_HMAIR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_HMAIR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_HPFAR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_HPFAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_HRMR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_HSCTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_HSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_HSTR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_HSTR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_HTCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_HTRFCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_HTTBR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_AP1R_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_ASGI1R_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_ASGI1R_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_BPR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_BPR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_BPR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_BPR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_CTLR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_CTLR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_CTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_DIR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_DIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_EOIR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_EOIR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_EOIR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_EOIR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_HPPIR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_HPPIR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_HPPIR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_HPPIR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_HSRE_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_IAR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_IAR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_IAR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_IAR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_IGRPEN0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_IGRPEN0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_IGRPEN1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_IGRPEN1_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_IGRPEN1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_MCTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_MGRPEN1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_MSRE_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_NMIAR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_PMR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_PMR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_RPR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_RPR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICC_SGI0R_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_SGI0R_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_SGI1R_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_SGI1R_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_SRE_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_SRE_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_SRE_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICC_SRE_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICH_AP0R_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICH_AP0R_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICH_AP1R_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICH_AP1R_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICH_EISR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICH_EISR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICH_ELRSR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICH_ELRSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICH_HCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICH_HCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICH_LRC_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICH_LR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICH_LR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICH_MISR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICH_MISR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICH_VMCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICH_VMCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICH_VTR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICH_VTR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICV_AP1R_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICV_BPR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICV_BPR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICV_BPR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICV_BPR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICV_CTLR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICV_CTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICV_DIR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICV_DIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICV_EOIR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICV_EOIR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICV_EOIR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICV_EOIR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICV_HPPIR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICV_HPPIR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICV_HPPIR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICV_HPPIR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICV_IAR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICV_IAR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICV_IAR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICV_IAR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICV_IGRPEN0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICV_IGRPEN0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICV_IGRPEN1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICV_IGRPEN1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICV_NMIAR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICV_PMR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICV_PMR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ICV_RPR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ICV_RPR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_AA64DFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_AA64DFR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_AA64ISAR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_AA64ISAR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_AA64ISAR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_AA64MMFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_AA64MMFR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_AA64MMFR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_AA64MMFR3_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_AA64MMFR4_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_AA64PFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_AA64PFR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_AA64PFR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_AA64SMFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_AA64ZFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_DFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_DFR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_DFR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_DFR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_ISAR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_ISAR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_ISAR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_ISAR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_ISAR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_ISAR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_ISAR3_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_ISAR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_ISAR4_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_ISAR4_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_ISAR5_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_ISAR5_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_ISAR6_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_ISAR6_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_MMFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_MMFR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_MMFR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_MMFR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_MMFR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_MMFR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_MMFR3_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_MMFR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_MMFR4_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_MMFR4_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_MMFR5_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_MMFR5_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_PFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_PFR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_PFR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_PFR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ID_PFR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ID_PFR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_IFSR32_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_IFSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_ISR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ISR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_LORC_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_LOREA_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_LORID_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_LORN_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_LORSA_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MAIR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_MAIR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_MAIR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MAIR2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MAIR2_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MAIRType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MAIR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MAIR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MAIR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MDCCINT_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MDCCSR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MDCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MDCR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MDRAR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MDSCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MDSELR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MECIDR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MECID_A0_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MECID_A1_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MECID_P0_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MECID_P1_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MECID_RL_A_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MFAR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_MPAM0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPAM1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPAM2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPAM3_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPAMHCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPAMIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPAMSM_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPAMVPM0_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPAMVPM1_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPAMVPM2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPAMVPM3_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPAMVPM4_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPAMVPM5_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPAMVPM6_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPAMVPM7_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPAMVPMV_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MPIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_MVBAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_MVFR0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MVFR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_MVFR1_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MVFR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_MVFR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_MVFR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_NMRR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_NSACR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_OSDLR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_OSECCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_OSLAR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_OSLSR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PAR_EL1_Type_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (128 -i 1) 0 x)

def _update_PAR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PFAR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PFAR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PIRE0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PIRE0_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PIR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PIR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PIR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMAUTHSTATUS_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMBIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMBLIMITR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMBPTR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMBSR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMCCFILTR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMCCFILTR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMCCNTR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMCCNTR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMCCNTSVR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMCEID0_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMCEID0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMCEID1_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMCEID1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMCEID2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMCEID3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMCFGR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMCGCR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMCIDR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMCIDR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMCIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMCIDR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMCNTENCLR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMCNTENCLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMCNTENSET_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMCNTENSET_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMCNTEN_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMCR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMDEVID_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMDEVTYPE_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMECR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMEVCNTSVR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMEVTYPER_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMEVTYPER_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMIAR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMICFILTR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMICNTR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMICNTSVR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMIIDR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMINTENCLR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMINTENCLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMINTENSET_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMINTENSET_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMINTEN_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMITCTRL_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMLAR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMLSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMMIR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMMIR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMOVSCLR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMOVSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMOVSSET_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMOVSSET_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMOVS_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMPCSCTL_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMPCSR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMPIDR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMPIDR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMPIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMPIDR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMPIDR4_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMSCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMSCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMSDSFR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMSELR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMSELR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMSEVFR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMSFCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMSICR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMSIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMSIRR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMSLATFR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMSNEVFR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMSSCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMSWINC_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMSWINC_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMUACR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMUSERENR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMUSERENR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMVCIDSR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMVIDSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_PMXEVCNTR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PMZR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_POR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_POR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_POR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_POR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_PRRR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_RCWMASK_EL1_Type_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (128 -i 1) 0 x)

def _update_RCWSMASK_EL1_Type_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (128 -i 1) 0 x)

def _update_RGSR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_RMR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_RMR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_RMR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_RMR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_RNDRRS_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_RNDR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_RVBAR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_RVBAR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_RVBAR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_S1PIRType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_S1PORType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_S2PIRType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_S2PIR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_S2POR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SCRType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SCR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_SCTLR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SCTLR2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SCTLR2_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SCTLRType_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SCTLR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SCTLR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SCTLR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SCTLR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_SDCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_SDER32_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SDER32_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SDER_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_SMCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SMCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SMCR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SMIDR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SMPRIMAP_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SMPRI_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SPMACCESSR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SPMACCESSR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SPMACCESSR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SPMSELR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SPSR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SPSR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SPSR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SPSR_abt_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SPSR_fiq_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SPSR_hyp_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_SPSR_irq_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_SPSR_mon_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_SPSR_svc_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_SPSR_und_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_TCR2_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_TCR2_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_TCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_TCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_TCR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_TFSRE0_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_TFSR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_TFSR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_TFSR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_TLBTR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_TRFCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_TRFCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_TRFCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_TTBCR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_TTBCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_TTBR0_EL1_Type_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (128 -i 1) 0 x)

def _update_TTBR0_EL2_Type_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (128 -i 1) 0 x)

def _update_TTBR0_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_TTBR0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_TTBR1_EL1_Type_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (128 -i 1) 0 x)

def _update_TTBR1_EL2_Type_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (128 -i 1) 0 x)

def _update_TTBR1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_VDFSR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_VDISR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_VDISR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_VMECID_A_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_VMECID_P_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_VMPIDR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_VMPIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_VNCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_VPIDR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_VPIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_VSESR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_VSTCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_VSTTBR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_VTCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_VTCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (32 -i 1) 0 x)

def _update_VTTBR_EL2_Type_bits (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v (128 -i 1) 0 x)

def _update_VTTBR_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ZCR_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ZCR_EL2_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _update_ZCR_EL3_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (64 -i 1) 0 x)

def _get_ACCDATA_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_AMCFGR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_AMCFGR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMCG1IDR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_AMCGCR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_AMCGCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMCIDR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMCIDR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMCIDR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMCIDR3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMCNTENCLR0_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_AMCNTENCLR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMCNTENCLR1_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_AMCNTENCLR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMCNTENSET0_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_AMCNTENSET0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMCNTENSET1_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_AMCNTENSET1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMCR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_AMCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMDEVARCH_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMDEVTYPE_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMEVCNTR0_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_AMEVCNTR0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_AMEVCNTR1_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_AMEVCNTR1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_AMEVTYPER0_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_AMEVTYPER0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMEVTYPER1_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_AMEVTYPER1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMIIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMPIDR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMPIDR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMPIDR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMPIDR3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMPIDR4_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_AMUSERENR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_AMUSERENR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_BRBCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_BRBCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_BRBIDR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_BRBINFINJ_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_BRBINFType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_BRBINF_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_BRBSRCINJ_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_BRBSRCType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_BRBSRC_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_BRBTGTINJ_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_BRBTGTType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_BRBTGT_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_BRBTS_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CCSIDR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CCSIDR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CCSIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CCSIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CLIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CLIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CNTEL0ACR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CNTFID0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CNTHCTL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTHCTL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CNTHPS_CTL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTHPS_CTL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CNTHPS_CVAL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTHPS_TVAL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTHP_CTL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CNTHP_CVAL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTHP_CVAL_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTHP_TVAL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTHVS_CTL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTHVS_CTL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CNTHVS_CVAL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTHVS_TVAL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTHV_CTL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTHV_CTL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CNTHV_CVAL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTHV_TVAL_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTID_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CNTKCTL_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTKCTL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CNTNSAR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CNTPS_CVAL_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTPS_TVAL_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTP_CTL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CNTP_CVAL_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTP_CVAL_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTP_TVAL_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTSCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CNTSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CNTV_CTL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CNTV_CVAL_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTV_CVAL_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CNTV_TVAL_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CONTEXTIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CONTEXTIDR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CONTEXTIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CPACR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CPACR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CPTR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CPTR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CSSELR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CSSELR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTIAUTHSTATUS_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTICIDR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTICIDR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTICIDR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTICIDR3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTICONTROL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTIDEVARCH_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTIDEVCTL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTIDEVID_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTIDEVTYPE_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTIITCTRL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTILAR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTILSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTIPIDR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTIPIDR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTIPIDR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTIPIDR3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTIPIDR4_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_CTR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_CTR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DACR32_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_DACR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGAUTHSTATUS_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_DBGAUTHSTATUS_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGBCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_DBGBCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGBVR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_DBGBVR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGBXVR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGCLAIMCLR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_DBGCLAIMCLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGCLAIMSET_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_DBGCLAIMSET_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGDCCINT_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGDEVID1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGDEVID_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGDIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGDRAR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_DBGDSCRext_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGDSCRint_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGDTRRXext_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGDTRRXint_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGDTRTXext_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGDTRTXint_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGDTR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_DBGOSDLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGOSECCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGOSLAR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGOSLSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGPRCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_DBGPRCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGVCR32_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_DBGVCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGWCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_DBGWCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DBGWVR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_DBGWVR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DCZID_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_DFSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DISR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_DISR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DSPSR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DSPSR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_DSPSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_DormantCtl_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDAA32PFR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_EDCIDR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDCIDR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDCIDR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDCIDR3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDDEVARCH_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDDEVID1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDDEVID_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDDEVTYPE_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDDFR1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_EDDFR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_EDECCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDECR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDHSR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_EDITCTRL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDLAR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDLSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDPCSR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_EDPFR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_EDPIDR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDPIDR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDPIDR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDPIDR3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDPIDR4_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDPRCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDPRSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDRCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDSCR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_EDVIDSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ERRIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ERRIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ERRSELR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ERRSELR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ERRnFR_ElemType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ERXGSR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ESRType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ESR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ESR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ESR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_FPCRType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_FPCR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_FPEXC32_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_FPEXC_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_FPSCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_FPSID_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_FPSR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GCSCRE0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GCSCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GCSCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GCSCR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GCSPR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GCSPR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GCSPR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GCSPR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GICC_ABPR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICC_AEOIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICC_AHPPIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICC_AIAR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICC_BPR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICC_CTLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICC_DIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICC_EOIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICC_HPPIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICC_IAR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICC_PMR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICC_RPR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICC_STATUSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICD_CLRSPI_NSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICD_CLRSPI_SR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICD_CTLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICD_IIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICD_SETSPI_NSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICD_SETSPI_SR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICD_SGIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICD_STATUSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICD_TYPER2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICD_TYPER_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICH_EISR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICH_ELRSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICH_HCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICH_MISR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICH_VMCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICH_VTR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICM_CLRSPI_NSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICM_CLRSPI_SR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICM_IIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICM_SETSPI_NSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICM_SETSPI_SR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICM_TYPER_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICR_CLRLPIR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GICR_CTLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICR_IIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICR_INMIR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICR_INVALLR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GICR_INVLPIR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GICR_ISENABLER0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICR_MPAMIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICR_PARTIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICR_PENDBASER_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GICR_PROPBASER_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GICR_SETLPIR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GICR_STATUSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICR_SYNCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICR_VPENDBASER_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GICR_VPROPBASER_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GICR_VSGIPENDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICR_VSGIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICR_WAKER_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICV_ABPR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICV_AEOIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICV_AHPPIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICV_AIAR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICV_BPR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICV_CTLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICV_DIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICV_EOIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICV_HPPIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICV_IAR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICV_PMR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICV_RPR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GICV_STATUSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GITS_CBASER_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GITS_CREADR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GITS_CTLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GITS_CWRITER_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GITS_IIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GITS_MPAMIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GITS_MPIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GITS_PARTIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GITS_SGIR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GITS_STATUSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_GITS_TYPER_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GMID_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GPCCR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_GPTBR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_HAFGRTR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_HCPTR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_HCR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_HCRX_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_HCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_HDCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_HDFGRTR2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_HDFGRTR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_HDFGWTR2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_HDFGWTR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_HFGITR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_HFGRTR2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_HFGRTR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_HFGWTR2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_HFGWTR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_HMAIR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_HMAIR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_HPFAR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_HPFAR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_HRMR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_HSCTLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_HSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_HSTR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_HSTR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_HTCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_HTRFCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_HTTBR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_AP1R_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_ASGI1R_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_ASGI1R_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_BPR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_BPR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_BPR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_BPR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_CTLR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_CTLR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_CTLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_DIR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_DIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_EOIR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_EOIR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_EOIR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_EOIR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_HPPIR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_HPPIR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_HPPIR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_HPPIR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_HSRE_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_IAR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_IAR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_IAR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_IAR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_IGRPEN0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_IGRPEN0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_IGRPEN1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_IGRPEN1_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_IGRPEN1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_MCTLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_MGRPEN1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_MSRE_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_NMIAR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_PMR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_PMR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_RPR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_RPR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICC_SGI0R_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_SGI0R_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_SGI1R_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_SGI1R_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_SRE_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_SRE_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_SRE_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICC_SRE_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICH_AP0R_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICH_AP0R_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICH_AP1R_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICH_AP1R_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICH_EISR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICH_EISR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICH_ELRSR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICH_ELRSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICH_HCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICH_HCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICH_LRC_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICH_LR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICH_LR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICH_MISR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICH_MISR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICH_VMCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICH_VMCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICH_VTR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICH_VTR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICV_AP1R_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICV_BPR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICV_BPR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICV_BPR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICV_BPR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICV_CTLR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICV_CTLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICV_DIR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICV_DIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICV_EOIR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICV_EOIR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICV_EOIR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICV_EOIR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICV_HPPIR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICV_HPPIR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICV_HPPIR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICV_HPPIR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICV_IAR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICV_IAR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICV_IAR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICV_IAR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICV_IGRPEN0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICV_IGRPEN0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICV_IGRPEN1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICV_IGRPEN1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICV_NMIAR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICV_PMR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICV_PMR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ICV_RPR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ICV_RPR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_AA64DFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_AA64DFR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_AA64ISAR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_AA64ISAR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_AA64ISAR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_AA64MMFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_AA64MMFR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_AA64MMFR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_AA64MMFR3_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_AA64MMFR4_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_AA64PFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_AA64PFR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_AA64PFR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_AA64SMFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_AA64ZFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_DFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_DFR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_DFR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_DFR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_ISAR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_ISAR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_ISAR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_ISAR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_ISAR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_ISAR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_ISAR3_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_ISAR3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_ISAR4_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_ISAR4_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_ISAR5_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_ISAR5_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_ISAR6_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_ISAR6_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_MMFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_MMFR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_MMFR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_MMFR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_MMFR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_MMFR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_MMFR3_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_MMFR3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_MMFR4_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_MMFR4_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_MMFR5_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_MMFR5_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_PFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_PFR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_PFR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_PFR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ID_PFR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ID_PFR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_IFSR32_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_IFSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_ISR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ISR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_LORC_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_LOREA_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_LORID_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_LORN_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_LORSA_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MAIR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_MAIR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_MAIR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MAIR2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MAIR2_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MAIR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MAIR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MAIR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MDCCINT_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MDCCSR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MDRAR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MDSELR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MECIDR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MECID_A0_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MECID_A1_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MECID_P0_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MECID_P1_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MECID_RL_A_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MFAR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_MPAM0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MPAM1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MPAM2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MPAMHCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MPAMIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MPAMSM_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MPAMVPM0_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MPAMVPM1_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MPAMVPM2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MPAMVPM3_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MPAMVPM4_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MPAMVPM5_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MPAMVPM6_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MPAMVPM7_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MPAMVPMV_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MPIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MPIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_MVBAR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_MVFR0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MVFR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_MVFR1_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MVFR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_MVFR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_MVFR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_NMRR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_NSACR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_OSDLR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_OSECCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_OSLAR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PAR_EL1_Type_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (128 -i 1) 0)

def _get_PAR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PFAR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PFAR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PIRE0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PIRE0_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PIR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PIR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PIR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMAUTHSTATUS_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMBIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMBLIMITR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMBPTR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMCCFILTR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMCCFILTR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMCCNTR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMCCNTR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMCCNTSVR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMCEID0_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMCEID0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMCEID1_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMCEID1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMCEID2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMCEID3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMCFGR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMCGCR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMCIDR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMCIDR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMCIDR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMCIDR3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMCNTENCLR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMCNTENCLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMCNTENSET_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMCNTENSET_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMCNTEN_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMDEVID_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMDEVTYPE_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMECR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMEVCNTSVR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMEVTYPER_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMEVTYPER_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMIAR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMICFILTR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMICNTR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMICNTSVR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMIIDR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMINTENCLR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMINTENCLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMINTENSET_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMINTENSET_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMINTEN_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMITCTRL_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMLAR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMLSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMMIR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMMIR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMOVSCLR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMOVSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMOVSSET_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMOVSSET_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMOVS_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMPCSCTL_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMPCSR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMPIDR0_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMPIDR1_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMPIDR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMPIDR3_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMPIDR4_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMSCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMSCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMSDSFR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMSELR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMSELR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMSEVFR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMSFCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMSICR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMSIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMSIRR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMSLATFR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMSNEVFR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMSSCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMSWINC_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMSWINC_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMUACR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMUSERENR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMUSERENR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMVCIDSR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMVIDSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_PMXEVCNTR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PMZR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_POR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_POR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_POR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_POR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_PRRR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_RCWMASK_EL1_Type_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (128 -i 1) 0)

def _get_RCWSMASK_EL1_Type_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (128 -i 1) 0)

def _get_RGSR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_RMR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_RMR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_RMR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_RMR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_RNDRRS_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_RNDR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_RVBAR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_RVBAR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_RVBAR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_S1PIRType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_S1PORType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_S2PIRType_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_S2PIR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_S2POR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_SCTLR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SCTLR2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SCTLR2_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SCTLR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SCTLR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SCTLR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_SDCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_SDER32_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SDER32_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SDER_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_SMCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SMCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SMCR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SMIDR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SMPRIMAP_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SMPRI_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SPMACCESSR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SPMACCESSR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SPMACCESSR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SPMSELR_EL0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SPSR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SPSR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SPSR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SPSR_abt_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SPSR_fiq_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SPSR_hyp_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_SPSR_irq_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_SPSR_mon_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_SPSR_svc_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_SPSR_und_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_TCR2_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_TCR2_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_TCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_TCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_TFSRE0_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_TFSR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_TFSR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_TFSR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_TLBTR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_TRFCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_TRFCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_TRFCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_TTBCR2_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_TTBCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_TTBR0_EL1_Type_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (128 -i 1) 0)

def _get_TTBR0_EL2_Type_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (128 -i 1) 0)

def _get_TTBR0_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_TTBR1_EL1_Type_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (128 -i 1) 0)

def _get_TTBR1_EL2_Type_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (128 -i 1) 0)

def _get_TTBR1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_VDFSR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_VDISR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_VDISR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_VMECID_A_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_VMECID_P_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_VMPIDR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_VMPIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_VNCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_VPIDR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_VPIDR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_VSESR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_VSTCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_VSTTBR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_VTCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_VTCR_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (32 -i 1) 0)

def _get_VTTBR_EL2_Type_bits (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v (128 -i 1) 0)

def _get_VTTBR_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ZCR_EL1_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ZCR_EL2_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_ZCR_EL3_Type_bits (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v (64 -i 1) 0)

def _get_Configuration_Type_CFGEND (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_Configuration_Type_CFGEND (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_Configuration_Type_CONFIG64 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_Configuration_Type_CONFIG64 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_Configuration_Type_CfgNMFI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_Configuration_Type_CfgNMFI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_Configuration_Type_Cp15SDisable (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_Configuration_Type_Cp15SDisable (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_Configuration_Type_Cp15SDisable2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_Configuration_Type_Cp15SDisable2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_Configuration_Type_ExceptInit (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_Configuration_Type_ExceptInit (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_Configuration_Type_HIVECS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_Configuration_Type_HIVECS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_Configuration_Type_RW (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_Configuration_Type_RW (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_HCR_EL2_Type_RW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SCRType_RW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_SCR_EL3_Type_RW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _set_EDSCR_Type_RW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_RW r v)

def _get_Configuration_Type_disableNIDebug (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_Configuration_Type_disableNIDebug (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_Configuration_Type_disableSPIDebug (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_Configuration_Type_disableSPIDebug (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_Configuration_Type_disableSPNIDebug (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_Configuration_Type_disableSPNIDebug (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def undefined_DormantCtl_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DormantCtl_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_DormantCtl_Type_Dbgnopwrdwn (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_DormantCtl_Type_Dbgnopwrdwn (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_DormantCtl_Type_PowerDownStatusSupport (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_DormantCtl_Type_PowerDownStatusSupport (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_DormantCtl_Type_ResetCatchStatus (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_DormantCtl_Type_ResetCatchStatus (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_DormantCtl_Type_TestResetCatch (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_DormantCtl_Type_TestResetCatch (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_DormantCtl_Type_dbgpwrupreq (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_DormantCtl_Type_dbgpwrupreq (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_DormantCtl_Type_dbgrstreq (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_DormantCtl_Type_dbgrstreq (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_DormantCtl_Type_etmpwrdwnreq (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_DormantCtl_Type_etmpwrdwnreq (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_DormantCtl_Type_etmpwrupreq (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_DormantCtl_Type_etmpwrupreq (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_DormantCtl_Type_nDbgpwrdwnreq (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_DormantCtl_Type_nDbgpwrdwnreq (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_DormantCtl_Type_nPU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_DormantCtl_Type_nPU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_DormantCtl_Type_standbywfe (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_DormantCtl_Type_standbywfe (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_DormantCtl_Type_standbywfi (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_DormantCtl_Type_standbywfi (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def undefined_Feature (_ : Unit) : SailM Feature := do
  (internal_pick [FEAT_AA32EL0, FEAT_AA32EL1, FEAT_AA32EL2, FEAT_AA32EL3, FEAT_AA64EL0, FEAT_AA64EL1, FEAT_AA64EL2, FEAT_AA64EL3, FEAT_EL0, FEAT_EL1, FEAT_EL2, FEAT_EL3, FEAT_AES, FEAT_AdvSIMD, FEAT_CSV2_1p1, FEAT_CSV2_1p2, FEAT_CSV2_2, FEAT_CSV2_3, FEAT_DoubleLock, FEAT_ETMv4, FEAT_ETMv4p1, FEAT_ETMv4p2, FEAT_ETMv4p3, FEAT_ETMv4p4, FEAT_ETMv4p5, FEAT_ETMv4p6, FEAT_ETS2, FEAT_FP, FEAT_GICv3, FEAT_GICv3_LEGACY, FEAT_GICv3_TDIR, FEAT_GICv3p1, FEAT_GICv4, FEAT_GICv4p1, FEAT_IVIPT, FEAT_PCSRv8, FEAT_PMULL, FEAT_PMUv3, FEAT_PMUv3_EXT, FEAT_PMUv3_EXT32, FEAT_SHA1, FEAT_SHA256, FEAT_TRC_EXT, FEAT_TRC_SR, FEAT_nTLBPA, FEAT_CRC32, FEAT_Debugv8p1, FEAT_HAFDBS, FEAT_HPDS, FEAT_LOR, FEAT_LSE, FEAT_PAN, FEAT_PMUv3p1, FEAT_RDM, FEAT_VHE, FEAT_VMID16, FEAT_AA32BF16, FEAT_AA32HPD, FEAT_AA32I8MM, FEAT_ASMv8p2, FEAT_DPB, FEAT_Debugv8p2, FEAT_EDHSR, FEAT_F32MM, FEAT_F64MM, FEAT_FP16, FEAT_HPDS2, FEAT_I8MM, FEAT_IESB, FEAT_LPA, FEAT_LSMAOC, FEAT_LVA, FEAT_MPAM, FEAT_PAN2, FEAT_PCSRv8p2, FEAT_RAS, FEAT_SHA3, FEAT_SHA512, FEAT_SM3, FEAT_SM4, FEAT_SPE, FEAT_SVE, FEAT_TTCNP, FEAT_UAO, FEAT_VPIPT, FEAT_XNX, FEAT_CCIDX, FEAT_CONSTPACFIELD, FEAT_EPAC, FEAT_FCMA, FEAT_FPAC, FEAT_FPACCOMBINE, FEAT_JSCVT, FEAT_LRCPC, FEAT_NV, FEAT_PACIMP, FEAT_PACQARMA3, FEAT_PACQARMA5, FEAT_PAuth, FEAT_SPEv1p1, FEAT_AMUv1, FEAT_BBM, FEAT_CNTSC, FEAT_DIT, FEAT_Debugv8p4, FEAT_DotProd, FEAT_DoubleFault, FEAT_FHM, FEAT_FlagM, FEAT_IDST, FEAT_LRCPC2, FEAT_LSE2, FEAT_NV2, FEAT_PMUv3p4, FEAT_RASSAv1p1, FEAT_RASv1p1, FEAT_S2FWB, FEAT_SEL2, FEAT_TLBIOS, FEAT_TLBIRANGE, FEAT_TRF, FEAT_TTL, FEAT_TTST, FEAT_BTI, FEAT_CSV2, FEAT_CSV3, FEAT_DPB2, FEAT_E0PD, FEAT_EVT, FEAT_ExS, FEAT_FRINTTS, FEAT_FlagM2, FEAT_GTG, FEAT_MTE, FEAT_MTE2, FEAT_PMUv3p5, FEAT_RNG, FEAT_RNG_TRAP, FEAT_SB, FEAT_SPECRES, FEAT_SSBS, FEAT_SSBS2, FEAT_AMUv1p1, FEAT_BF16, FEAT_DGH, FEAT_ECV, FEAT_FGT, FEAT_HPMN0, FEAT_MPAMv0p1, FEAT_MPAMv1p1, FEAT_MTPMU, FEAT_PAuth2, FEAT_TWED, FEAT_AFP, FEAT_EBF16, FEAT_HCX, FEAT_LPA2, FEAT_LS64, FEAT_LS64_ACCDATA, FEAT_LS64_V, FEAT_MTE3, FEAT_PAN3, FEAT_PMUv3p7, FEAT_RPRES, FEAT_SPEv1p2, FEAT_WFxT, FEAT_XS, FEAT_CMOW, FEAT_Debugv8p8, FEAT_GICv3_NMI, FEAT_HBC, FEAT_MOPS, FEAT_NMI, FEAT_PMUv3_EXT64, FEAT_PMUv3_TH, FEAT_PMUv3p8, FEAT_SCTLR2, FEAT_SPEv1p3, FEAT_TCR2, FEAT_TIDCP1, FEAT_ADERR, FEAT_AIE, FEAT_ANERR, FEAT_CLRBHB, FEAT_CSSC, FEAT_Debugv8p9, FEAT_DoubleFault2, FEAT_ECBHB, FEAT_FGT2, FEAT_HAFT, FEAT_LRCPC3, FEAT_MTE4, FEAT_MTE_ASYM_FAULT, FEAT_MTE_ASYNC, FEAT_MTE_CANONICAL_TAGS, FEAT_MTE_NO_ADDRESS_TAGS, FEAT_MTE_PERM, FEAT_MTE_STORE_ONLY, FEAT_MTE_TAGGED_FAR, FEAT_PCSRv8p9, FEAT_PFAR, FEAT_PMUv3_EDGE, FEAT_PMUv3_ICNTR, FEAT_PMUv3_SS, FEAT_PMUv3p9, FEAT_PRFMSLC, FEAT_RASSAv2, FEAT_RASv2, FEAT_RPRFM, FEAT_S1PIE, FEAT_S1POE, FEAT_S2PIE, FEAT_S2POE, FEAT_SPECRES2, FEAT_SPE_CRR, FEAT_SPE_FDS, FEAT_SPEv1p4, FEAT_SPMU, FEAT_THE, FEAT_DoPD, FEAT_ETE, FEAT_SVE2, FEAT_SVE_AES, FEAT_SVE_BitPerm, FEAT_SVE_PMULL128, FEAT_SVE_SHA3, FEAT_SVE_SM4, FEAT_TME, FEAT_TRBE, FEAT_ETEv1p1, FEAT_BRBE, FEAT_ETEv1p2, FEAT_RME, FEAT_SME, FEAT_SME_F64F64, FEAT_SME_FA64, FEAT_SME_I16I64, FEAT_BRBEv1p1, FEAT_MEC, FEAT_SME2, FEAT_ABLE, FEAT_CHK, FEAT_D128, FEAT_EBEP, FEAT_ETEv1p3, FEAT_GCS, FEAT_ITE, FEAT_LSE128, FEAT_LVA3, FEAT_SEBEP, FEAT_SME2p1, FEAT_SME_F16F16, FEAT_SVE2p1, FEAT_SVE_B16B16, FEAT_SYSINSTR128, FEAT_SYSREG128, FEAT_TRBE_EXT, FEAT_TRBE_MPAM])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 257 -/
def Feature_of_num (arg_ : Nat) : Feature :=
  match arg_ with
  | 0 => FEAT_AA32EL0
  | 1 => FEAT_AA32EL1
  | 2 => FEAT_AA32EL2
  | 3 => FEAT_AA32EL3
  | 4 => FEAT_AA64EL0
  | 5 => FEAT_AA64EL1
  | 6 => FEAT_AA64EL2
  | 7 => FEAT_AA64EL3
  | 8 => FEAT_EL0
  | 9 => FEAT_EL1
  | 10 => FEAT_EL2
  | 11 => FEAT_EL3
  | 12 => FEAT_AES
  | 13 => FEAT_AdvSIMD
  | 14 => FEAT_CSV2_1p1
  | 15 => FEAT_CSV2_1p2
  | 16 => FEAT_CSV2_2
  | 17 => FEAT_CSV2_3
  | 18 => FEAT_DoubleLock
  | 19 => FEAT_ETMv4
  | 20 => FEAT_ETMv4p1
  | 21 => FEAT_ETMv4p2
  | 22 => FEAT_ETMv4p3
  | 23 => FEAT_ETMv4p4
  | 24 => FEAT_ETMv4p5
  | 25 => FEAT_ETMv4p6
  | 26 => FEAT_ETS2
  | 27 => FEAT_FP
  | 28 => FEAT_GICv3
  | 29 => FEAT_GICv3_LEGACY
  | 30 => FEAT_GICv3_TDIR
  | 31 => FEAT_GICv3p1
  | 32 => FEAT_GICv4
  | 33 => FEAT_GICv4p1
  | 34 => FEAT_IVIPT
  | 35 => FEAT_PCSRv8
  | 36 => FEAT_PMULL
  | 37 => FEAT_PMUv3
  | 38 => FEAT_PMUv3_EXT
  | 39 => FEAT_PMUv3_EXT32
  | 40 => FEAT_SHA1
  | 41 => FEAT_SHA256
  | 42 => FEAT_TRC_EXT
  | 43 => FEAT_TRC_SR
  | 44 => FEAT_nTLBPA
  | 45 => FEAT_CRC32
  | 46 => FEAT_Debugv8p1
  | 47 => FEAT_HAFDBS
  | 48 => FEAT_HPDS
  | 49 => FEAT_LOR
  | 50 => FEAT_LSE
  | 51 => FEAT_PAN
  | 52 => FEAT_PMUv3p1
  | 53 => FEAT_RDM
  | 54 => FEAT_VHE
  | 55 => FEAT_VMID16
  | 56 => FEAT_AA32BF16
  | 57 => FEAT_AA32HPD
  | 58 => FEAT_AA32I8MM
  | 59 => FEAT_ASMv8p2
  | 60 => FEAT_DPB
  | 61 => FEAT_Debugv8p2
  | 62 => FEAT_EDHSR
  | 63 => FEAT_F32MM
  | 64 => FEAT_F64MM
  | 65 => FEAT_FP16
  | 66 => FEAT_HPDS2
  | 67 => FEAT_I8MM
  | 68 => FEAT_IESB
  | 69 => FEAT_LPA
  | 70 => FEAT_LSMAOC
  | 71 => FEAT_LVA
  | 72 => FEAT_MPAM
  | 73 => FEAT_PAN2
  | 74 => FEAT_PCSRv8p2
  | 75 => FEAT_RAS
  | 76 => FEAT_SHA3
  | 77 => FEAT_SHA512
  | 78 => FEAT_SM3
  | 79 => FEAT_SM4
  | 80 => FEAT_SPE
  | 81 => FEAT_SVE
  | 82 => FEAT_TTCNP
  | 83 => FEAT_UAO
  | 84 => FEAT_VPIPT
  | 85 => FEAT_XNX
  | 86 => FEAT_CCIDX
  | 87 => FEAT_CONSTPACFIELD
  | 88 => FEAT_EPAC
  | 89 => FEAT_FCMA
  | 90 => FEAT_FPAC
  | 91 => FEAT_FPACCOMBINE
  | 92 => FEAT_JSCVT
  | 93 => FEAT_LRCPC
  | 94 => FEAT_NV
  | 95 => FEAT_PACIMP
  | 96 => FEAT_PACQARMA3
  | 97 => FEAT_PACQARMA5
  | 98 => FEAT_PAuth
  | 99 => FEAT_SPEv1p1
  | 100 => FEAT_AMUv1
  | 101 => FEAT_BBM
  | 102 => FEAT_CNTSC
  | 103 => FEAT_DIT
  | 104 => FEAT_Debugv8p4
  | 105 => FEAT_DotProd
  | 106 => FEAT_DoubleFault
  | 107 => FEAT_FHM
  | 108 => FEAT_FlagM
  | 109 => FEAT_IDST
  | 110 => FEAT_LRCPC2
  | 111 => FEAT_LSE2
  | 112 => FEAT_NV2
  | 113 => FEAT_PMUv3p4
  | 114 => FEAT_RASSAv1p1
  | 115 => FEAT_RASv1p1
  | 116 => FEAT_S2FWB
  | 117 => FEAT_SEL2
  | 118 => FEAT_TLBIOS
  | 119 => FEAT_TLBIRANGE
  | 120 => FEAT_TRF
  | 121 => FEAT_TTL
  | 122 => FEAT_TTST
  | 123 => FEAT_BTI
  | 124 => FEAT_CSV2
  | 125 => FEAT_CSV3
  | 126 => FEAT_DPB2
  | 127 => FEAT_E0PD
  | 128 => FEAT_EVT
  | 129 => FEAT_ExS
  | 130 => FEAT_FRINTTS
  | 131 => FEAT_FlagM2
  | 132 => FEAT_GTG
  | 133 => FEAT_MTE
  | 134 => FEAT_MTE2
  | 135 => FEAT_PMUv3p5
  | 136 => FEAT_RNG
  | 137 => FEAT_RNG_TRAP
  | 138 => FEAT_SB
  | 139 => FEAT_SPECRES
  | 140 => FEAT_SSBS
  | 141 => FEAT_SSBS2
  | 142 => FEAT_AMUv1p1
  | 143 => FEAT_BF16
  | 144 => FEAT_DGH
  | 145 => FEAT_ECV
  | 146 => FEAT_FGT
  | 147 => FEAT_HPMN0
  | 148 => FEAT_MPAMv0p1
  | 149 => FEAT_MPAMv1p1
  | 150 => FEAT_MTPMU
  | 151 => FEAT_PAuth2
  | 152 => FEAT_TWED
  | 153 => FEAT_AFP
  | 154 => FEAT_EBF16
  | 155 => FEAT_HCX
  | 156 => FEAT_LPA2
  | 157 => FEAT_LS64
  | 158 => FEAT_LS64_ACCDATA
  | 159 => FEAT_LS64_V
  | 160 => FEAT_MTE3
  | 161 => FEAT_PAN3
  | 162 => FEAT_PMUv3p7
  | 163 => FEAT_RPRES
  | 164 => FEAT_SPEv1p2
  | 165 => FEAT_WFxT
  | 166 => FEAT_XS
  | 167 => FEAT_CMOW
  | 168 => FEAT_Debugv8p8
  | 169 => FEAT_GICv3_NMI
  | 170 => FEAT_HBC
  | 171 => FEAT_MOPS
  | 172 => FEAT_NMI
  | 173 => FEAT_PMUv3_EXT64
  | 174 => FEAT_PMUv3_TH
  | 175 => FEAT_PMUv3p8
  | 176 => FEAT_SCTLR2
  | 177 => FEAT_SPEv1p3
  | 178 => FEAT_TCR2
  | 179 => FEAT_TIDCP1
  | 180 => FEAT_ADERR
  | 181 => FEAT_AIE
  | 182 => FEAT_ANERR
  | 183 => FEAT_CLRBHB
  | 184 => FEAT_CSSC
  | 185 => FEAT_Debugv8p9
  | 186 => FEAT_DoubleFault2
  | 187 => FEAT_ECBHB
  | 188 => FEAT_FGT2
  | 189 => FEAT_HAFT
  | 190 => FEAT_LRCPC3
  | 191 => FEAT_MTE4
  | 192 => FEAT_MTE_ASYM_FAULT
  | 193 => FEAT_MTE_ASYNC
  | 194 => FEAT_MTE_CANONICAL_TAGS
  | 195 => FEAT_MTE_NO_ADDRESS_TAGS
  | 196 => FEAT_MTE_PERM
  | 197 => FEAT_MTE_STORE_ONLY
  | 198 => FEAT_MTE_TAGGED_FAR
  | 199 => FEAT_PCSRv8p9
  | 200 => FEAT_PFAR
  | 201 => FEAT_PMUv3_EDGE
  | 202 => FEAT_PMUv3_ICNTR
  | 203 => FEAT_PMUv3_SS
  | 204 => FEAT_PMUv3p9
  | 205 => FEAT_PRFMSLC
  | 206 => FEAT_RASSAv2
  | 207 => FEAT_RASv2
  | 208 => FEAT_RPRFM
  | 209 => FEAT_S1PIE
  | 210 => FEAT_S1POE
  | 211 => FEAT_S2PIE
  | 212 => FEAT_S2POE
  | 213 => FEAT_SPECRES2
  | 214 => FEAT_SPE_CRR
  | 215 => FEAT_SPE_FDS
  | 216 => FEAT_SPEv1p4
  | 217 => FEAT_SPMU
  | 218 => FEAT_THE
  | 219 => FEAT_DoPD
  | 220 => FEAT_ETE
  | 221 => FEAT_SVE2
  | 222 => FEAT_SVE_AES
  | 223 => FEAT_SVE_BitPerm
  | 224 => FEAT_SVE_PMULL128
  | 225 => FEAT_SVE_SHA3
  | 226 => FEAT_SVE_SM4
  | 227 => FEAT_TME
  | 228 => FEAT_TRBE
  | 229 => FEAT_ETEv1p1
  | 230 => FEAT_BRBE
  | 231 => FEAT_ETEv1p2
  | 232 => FEAT_RME
  | 233 => FEAT_SME
  | 234 => FEAT_SME_F64F64
  | 235 => FEAT_SME_FA64
  | 236 => FEAT_SME_I16I64
  | 237 => FEAT_BRBEv1p1
  | 238 => FEAT_MEC
  | 239 => FEAT_SME2
  | 240 => FEAT_ABLE
  | 241 => FEAT_CHK
  | 242 => FEAT_D128
  | 243 => FEAT_EBEP
  | 244 => FEAT_ETEv1p3
  | 245 => FEAT_GCS
  | 246 => FEAT_ITE
  | 247 => FEAT_LSE128
  | 248 => FEAT_LVA3
  | 249 => FEAT_SEBEP
  | 250 => FEAT_SME2p1
  | 251 => FEAT_SME_F16F16
  | 252 => FEAT_SVE2p1
  | 253 => FEAT_SVE_B16B16
  | 254 => FEAT_SYSINSTR128
  | 255 => FEAT_SYSREG128
  | 256 => FEAT_TRBE_EXT
  | _ => FEAT_TRBE_MPAM

def undefined_ArchVersion (_ : Unit) : SailM ArchVersion := do
  (internal_pick [v8Ap0, v8Ap1, v8Ap2, v8Ap3, v8Ap4, v8Ap5, v8Ap6, v8Ap7, v8Ap8, v8Ap9, v9Ap0, v9Ap1, v9Ap2, v9Ap3, v9Ap4])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 14 -/
def ArchVersion_of_num (arg_ : Nat) : ArchVersion :=
  match arg_ with
  | 0 => v8Ap0
  | 1 => v8Ap1
  | 2 => v8Ap2
  | 3 => v8Ap3
  | 4 => v8Ap4
  | 5 => v8Ap5
  | 6 => v8Ap6
  | 7 => v8Ap7
  | 8 => v8Ap8
  | 9 => v8Ap9
  | 10 => v9Ap0
  | 11 => v9Ap1
  | 12 => v9Ap2
  | 13 => v9Ap3
  | _ => v9Ap4

def num_of_ArchVersion (arg_ : ArchVersion) : Int :=
  match arg_ with
  | .v8Ap0 => 0
  | .v8Ap1 => 1
  | .v8Ap2 => 2
  | .v8Ap3 => 3
  | .v8Ap4 => 4
  | .v8Ap5 => 5
  | .v8Ap6 => 6
  | .v8Ap7 => 7
  | .v8Ap8 => 8
  | .v8Ap9 => 9
  | .v9Ap0 => 10
  | .v9Ap1 => 11
  | .v9Ap2 => 12
  | .v9Ap3 => 13
  | .v9Ap4 => 14

def InitFeatureImpl (_ : Unit) : SailM Unit := do
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA32EL0) (← readReg FEAT_AA32EL0_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA32EL1) (← readReg FEAT_AA32EL1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA32EL2) (← readReg FEAT_AA32EL2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA32EL3) (← readReg FEAT_AA32EL3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA64EL0) (← readReg FEAT_AA64EL0_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA64EL1) (← readReg FEAT_AA64EL1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA64EL2) (← readReg FEAT_AA64EL2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA64EL3) (← readReg FEAT_AA64EL3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_EL0) (← readReg FEAT_EL0_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_EL1) (← readReg FEAT_EL1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_EL2) (← readReg FEAT_EL2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_EL3) (← readReg FEAT_EL3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AES) (← readReg FEAT_AES_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AdvSIMD) (← readReg FEAT_AdvSIMD_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_CSV2_1p1) (← readReg FEAT_CSV2_1p1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_CSV2_1p2) (← readReg FEAT_CSV2_1p2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_CSV2_2) (← readReg FEAT_CSV2_2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_CSV2_3) (← readReg FEAT_CSV2_3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_DoubleLock) (← readReg FEAT_DoubleLock_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ETMv4) (← readReg FEAT_ETMv4_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ETMv4p1) (← readReg FEAT_ETMv4p1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ETMv4p2) (← readReg FEAT_ETMv4p2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ETMv4p3) (← readReg FEAT_ETMv4p3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ETMv4p4) (← readReg FEAT_ETMv4p4_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ETMv4p5) (← readReg FEAT_ETMv4p5_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ETMv4p6) (← readReg FEAT_ETMv4p6_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ETS2) (← readReg FEAT_ETS2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_FP) (← readReg FEAT_FP_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_GICv3) (← readReg FEAT_GICv3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_GICv3_LEGACY) (← readReg FEAT_GICv3_LEGACY_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_GICv3_TDIR) (← readReg FEAT_GICv3_TDIR_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_GICv3p1) (← readReg FEAT_GICv3p1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_GICv4) (← readReg FEAT_GICv4_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_GICv4p1) (← readReg FEAT_GICv4p1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_IVIPT) (← readReg FEAT_IVIPT_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PCSRv8) (← readReg FEAT_PCSRv8_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PMULL) (← readReg FEAT_PMULL_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PMUv3) (← readReg FEAT_PMUv3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PMUv3_EXT) (← readReg FEAT_PMUv3_EXT_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PMUv3_EXT32) (← readReg FEAT_PMUv3_EXT32_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SHA1) (← readReg FEAT_SHA1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SHA256) (← readReg FEAT_SHA256_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_TRC_EXT) (← readReg FEAT_TRC_EXT_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_TRC_SR) (← readReg FEAT_TRC_SR_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_nTLBPA) (← readReg FEAT_nTLBPA_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_CRC32) (← readReg FEAT_CRC32_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_Debugv8p1) (← readReg FEAT_Debugv8p1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_HAFDBS) (← readReg FEAT_HAFDBS_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_HPDS) (← readReg FEAT_HPDS_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_LOR) (← readReg FEAT_LOR_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_LSE) (← readReg FEAT_LSE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PAN) (← readReg FEAT_PAN_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PMUv3p1) (← readReg FEAT_PMUv3p1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_RDM) (← readReg FEAT_RDM_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_VHE) (← readReg FEAT_VHE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_VMID16) (← readReg FEAT_VMID16_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA32BF16) (← readReg FEAT_AA32BF16_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA32HPD) (← readReg FEAT_AA32HPD_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA32I8MM) (← readReg FEAT_AA32I8MM_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ASMv8p2) (← readReg FEAT_ASMv8p2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_DPB) (← readReg FEAT_DPB_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_Debugv8p2) (← readReg FEAT_Debugv8p2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_EDHSR) (← readReg FEAT_EDHSR_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_F32MM) (← readReg FEAT_F32MM_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_F64MM) (← readReg FEAT_F64MM_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_FP16) (← readReg FEAT_FP16_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_HPDS2) (← readReg FEAT_HPDS2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_I8MM) (← readReg FEAT_I8MM_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_IESB) (← readReg FEAT_IESB_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_LPA) (← readReg FEAT_LPA_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_LSMAOC) (← readReg FEAT_LSMAOC_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_LVA) (← readReg FEAT_LVA_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MPAM) (← readReg FEAT_MPAM_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PAN2) (← readReg FEAT_PAN2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PCSRv8p2) (← readReg FEAT_PCSRv8p2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_RAS) (← readReg FEAT_RAS_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SHA3) (← readReg FEAT_SHA3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SHA512) (← readReg FEAT_SHA512_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SM3) (← readReg FEAT_SM3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SM4) (← readReg FEAT_SM4_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SPE) (← readReg FEAT_SPE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SVE) (← readReg FEAT_SVE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_TTCNP) (← readReg FEAT_TTCNP_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_UAO) (← readReg FEAT_UAO_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_VPIPT) (← readReg FEAT_VPIPT_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_XNX) (← readReg FEAT_XNX_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_CCIDX) (← readReg FEAT_CCIDX_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_CONSTPACFIELD) (← readReg FEAT_CONSTPACFIELD_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_EPAC) (← readReg FEAT_EPAC_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_FCMA) (← readReg FEAT_FCMA_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_FPAC) (← readReg FEAT_FPAC_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_FPACCOMBINE) (← readReg FEAT_FPACCOMBINE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_JSCVT) (← readReg FEAT_JSCVT_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_LRCPC) (← readReg FEAT_LRCPC_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_NV) (← readReg FEAT_NV_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PACIMP) (← readReg FEAT_PACIMP_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PACQARMA3) (← readReg FEAT_PACQARMA3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PACQARMA5) (← readReg FEAT_PACQARMA5_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PAuth) (← readReg FEAT_PAuth_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SPEv1p1) (← readReg FEAT_SPEv1p1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AMUv1) (← readReg FEAT_AMUv1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_BBM) (← readReg FEAT_BBM_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_CNTSC) (← readReg FEAT_CNTSC_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_DIT) (← readReg FEAT_DIT_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_Debugv8p4) (← readReg FEAT_Debugv8p4_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_DotProd) (← readReg FEAT_DotProd_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_DoubleFault) (← readReg FEAT_DoubleFault_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_FHM) (← readReg FEAT_FHM_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_FlagM) (← readReg FEAT_FlagM_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_IDST) (← readReg FEAT_IDST_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_LRCPC2) (← readReg FEAT_LRCPC2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_LSE2) (← readReg FEAT_LSE2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_NV2) (← readReg FEAT_NV2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PMUv3p4) (← readReg FEAT_PMUv3p4_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_RASSAv1p1) (← readReg FEAT_RASSAv1p1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_RASv1p1) (← readReg FEAT_RASv1p1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_S2FWB) (← readReg FEAT_S2FWB_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SEL2) (← readReg FEAT_SEL2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_TLBIOS) (← readReg FEAT_TLBIOS_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_TLBIRANGE) (← readReg FEAT_TLBIRANGE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_TRF) (← readReg FEAT_TRF_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_TTL) (← readReg FEAT_TTL_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_TTST) (← readReg FEAT_TTST_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_BTI) (← readReg FEAT_BTI_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_CSV2) (← readReg FEAT_CSV2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_CSV3) (← readReg FEAT_CSV3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_DPB2) (← readReg FEAT_DPB2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_E0PD) (← readReg FEAT_E0PD_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_EVT) (← readReg FEAT_EVT_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ExS) (← readReg FEAT_ExS_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_FRINTTS) (← readReg FEAT_FRINTTS_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_FlagM2) (← readReg FEAT_FlagM2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_GTG) (← readReg FEAT_GTG_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MTE) (← readReg FEAT_MTE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MTE2) (← readReg FEAT_MTE2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PMUv3p5) (← readReg FEAT_PMUv3p5_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_RNG) (← readReg FEAT_RNG_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_RNG_TRAP) (← readReg FEAT_RNG_TRAP_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SB) (← readReg FEAT_SB_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SPECRES) (← readReg FEAT_SPECRES_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SSBS) (← readReg FEAT_SSBS_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SSBS2) (← readReg FEAT_SSBS2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AMUv1p1) (← readReg FEAT_AMUv1p1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_BF16) (← readReg FEAT_BF16_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_DGH) (← readReg FEAT_DGH_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ECV) (← readReg FEAT_ECV_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_FGT) (← readReg FEAT_FGT_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_HPMN0) (← readReg FEAT_HPMN0_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MPAMv0p1) (← readReg FEAT_MPAMv0p1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MPAMv1p1) (← readReg FEAT_MPAMv1p1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MTPMU) (← readReg FEAT_MTPMU_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PAuth2) (← readReg FEAT_PAuth2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_TWED) (← readReg FEAT_TWED_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AFP) (← readReg FEAT_AFP_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_EBF16) (← readReg FEAT_EBF16_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_HCX) (← readReg FEAT_HCX_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_LPA2) (← readReg FEAT_LPA2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_LS64) (← readReg FEAT_LS64_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_LS64_ACCDATA) (← readReg FEAT_LS64_ACCDATA_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_LS64_V) (← readReg FEAT_LS64_V_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MTE3) (← readReg FEAT_MTE3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PAN3) (← readReg FEAT_PAN3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PMUv3p7) (← readReg FEAT_PMUv3p7_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_RPRES) (← readReg FEAT_RPRES_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SPEv1p2) (← readReg FEAT_SPEv1p2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_WFxT) (← readReg FEAT_WFxT_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_XS) (← readReg FEAT_XS_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_CMOW) (← readReg FEAT_CMOW_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_Debugv8p8) (← readReg FEAT_Debugv8p8_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_GICv3_NMI) (← readReg FEAT_GICv3_NMI_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_HBC) (← readReg FEAT_HBC_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MOPS) (← readReg FEAT_MOPS_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_NMI) (← readReg FEAT_NMI_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PMUv3_EXT64) (← readReg FEAT_PMUv3_EXT64_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PMUv3_TH) (← readReg FEAT_PMUv3_TH_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PMUv3p8) (← readReg FEAT_PMUv3p8_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SCTLR2) (← readReg FEAT_SCTLR2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SPEv1p3) (← readReg FEAT_SPEv1p3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_TCR2) (← readReg FEAT_TCR2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_TIDCP1) (← readReg FEAT_TIDCP1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ADERR) (← readReg FEAT_ADERR_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AIE) (← readReg FEAT_AIE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ANERR) (← readReg FEAT_ANERR_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_CLRBHB) (← readReg FEAT_CLRBHB_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_CSSC) (← readReg FEAT_CSSC_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_Debugv8p9) (← readReg FEAT_Debugv8p9_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_DoubleFault2) (← readReg FEAT_DoubleFault2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ECBHB) (← readReg FEAT_ECBHB_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_FGT2) (← readReg FEAT_FGT2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_HAFT) (← readReg FEAT_HAFT_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_LRCPC3) (← readReg FEAT_LRCPC3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MTE4) (← readReg FEAT_MTE4_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MTE_ASYM_FAULT) (← readReg FEAT_MTE_ASYM_FAULT_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MTE_ASYNC) (← readReg FEAT_MTE_ASYNC_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MTE_CANONICAL_TAGS) (← readReg FEAT_MTE_CANONICAL_TAGS_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MTE_NO_ADDRESS_TAGS) (← readReg FEAT_MTE_NO_ADDRESS_TAGS_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MTE_PERM) (← readReg FEAT_MTE_PERM_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MTE_STORE_ONLY) (← readReg FEAT_MTE_STORE_ONLY_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MTE_TAGGED_FAR) (← readReg FEAT_MTE_TAGGED_FAR_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PCSRv8p9) (← readReg FEAT_PCSRv8p9_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PFAR) (← readReg FEAT_PFAR_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PMUv3_EDGE) (← readReg FEAT_PMUv3_EDGE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PMUv3_ICNTR) (← readReg FEAT_PMUv3_ICNTR_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PMUv3_SS) (← readReg FEAT_PMUv3_SS_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PMUv3p9) (← readReg FEAT_PMUv3p9_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_PRFMSLC) (← readReg FEAT_PRFMSLC_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_RASSAv2) (← readReg FEAT_RASSAv2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_RASv2) (← readReg FEAT_RASv2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_RPRFM) (← readReg FEAT_RPRFM_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_S1PIE) (← readReg FEAT_S1PIE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_S1POE) (← readReg FEAT_S1POE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_S2PIE) (← readReg FEAT_S2PIE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_S2POE) (← readReg FEAT_S2POE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SPECRES2) (← readReg FEAT_SPECRES2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SPE_CRR) (← readReg FEAT_SPE_CRR_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SPE_FDS) (← readReg FEAT_SPE_FDS_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SPEv1p4) (← readReg FEAT_SPEv1p4_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SPMU) (← readReg FEAT_SPMU_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_THE) (← readReg FEAT_THE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_DoPD) (← readReg FEAT_DoPD_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ETE) (← readReg FEAT_ETE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SVE2) (← readReg FEAT_SVE2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SVE_AES) (← readReg FEAT_SVE_AES_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SVE_BitPerm) (← readReg FEAT_SVE_BitPerm_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SVE_PMULL128) (← readReg FEAT_SVE_PMULL128_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SVE_SHA3) (← readReg FEAT_SVE_SHA3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SVE_SM4) (← readReg FEAT_SVE_SM4_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_TME) (← readReg FEAT_TME_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_TRBE) (← readReg FEAT_TRBE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ETEv1p1) (← readReg FEAT_ETEv1p1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_BRBE) (← readReg FEAT_BRBE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ETEv1p2) (← readReg FEAT_ETEv1p2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_RME) (← readReg FEAT_RME_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SME) (← readReg FEAT_SME_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SME_F64F64) (← readReg FEAT_SME_F64F64_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SME_FA64) (← readReg FEAT_SME_FA64_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SME_I16I64) (← readReg FEAT_SME_I16I64_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_BRBEv1p1) (← readReg FEAT_BRBEv1p1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_MEC) (← readReg FEAT_MEC_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SME2) (← readReg FEAT_SME2_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ABLE) (← readReg FEAT_ABLE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_CHK) (← readReg FEAT_CHK_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_D128) (← readReg FEAT_D128_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_EBEP) (← readReg FEAT_EBEP_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ETEv1p3) (← readReg FEAT_ETEv1p3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_GCS) (← readReg FEAT_GCS_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_ITE) (← readReg FEAT_ITE_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_LSE128) (← readReg FEAT_LSE128_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_LVA3) (← readReg FEAT_LVA3_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SEBEP) (← readReg FEAT_SEBEP_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SME2p1) (← readReg FEAT_SME2p1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SME_F16F16) (← readReg FEAT_SME_F16F16_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SVE2p1) (← readReg FEAT_SVE2p1_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SVE_B16B16) (← readReg FEAT_SVE_B16B16_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SYSINSTR128) (← readReg FEAT_SYSINSTR128_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_SYSREG128) (← readReg FEAT_SYSREG128_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_TRBE_EXT) (← readReg FEAT_TRBE_EXT_IMPLEMENTED))
  writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_TRBE_MPAM) (← readReg FEAT_TRBE_MPAM_IMPLEMENTED))

def undefined_SCRType (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _update_SCRType_AW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SCR_Type_AW (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SCRType_EA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_DISR_EL1_Type_EA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_DISR_Type_EA (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_LOREA_EL1_Type_EA (v : (BitVec 64)) (x : (BitVec 40)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 55 52 (Sail.BitVec.extractLsb x (40 -i 1) (((40 -i 1) -i ((55 -i 52) +i 1)) +i 1))) 51 48 (Sail.BitVec.extractLsb x ((40 -i 1) -i ((55 -i 52) +i 1)) ((((40 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) +i 1))) 47 16 (Sail.BitVec.extractLsb x (((40 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) (((((40 -i 1) -i ((55 -i 52) +i 1)) -i ((51 -i 48) +i 1)) -i ((47 -i 16) +i 1)) +i 1)))

def _update_PMBIDR_EL1_Type_EA (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_PMBSR_EL1_Type_EA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_SCR_EL3_Type_EA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_SCR_Type_EA (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_DISR_EL1_Type_EA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_DISR_Type_EA (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_LOREA_EL1_Type_EA (v : (BitVec 64)) : (BitVec 40) :=
  ((Sail.BitVec.extractLsb v 55 52) +++ ((Sail.BitVec.extractLsb v 51 48) +++ (Sail.BitVec.extractLsb v 47 16)))

def _get_PMBIDR_EL1_Type_EA (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_SCRType_FIQ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_SCR_EL3_Type_FIQ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_SCR_Type_FIQ (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_SCRType_FW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_SCR_Type_FW (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_SCRType_HCE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_SCR_EL3_Type_HCE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_SCR_Type_HCE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_SCR_Type_HCE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_SCRType_IRQ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_SCR_EL3_Type_IRQ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_SCR_Type_IRQ (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_SCRType_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_DBGDSCRext_Type_NS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_DBGDSCRint_Type_NS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_EDPCSR_Type_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_EDVIDSR_Type_NS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_HPFAR_EL2_Type_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_MFAR_EL3_Type_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_PAR_EL1_Type_NS (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PAR_Type_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PFAR_EL1_Type_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_PFAR_EL2_Type_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_PMPCSR_Type_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_SCR_EL3_Type_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_SCR_Type_NS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_DBGDSCRext_Type_NS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_DBGDSCRint_Type_NS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_EDPCSR_Type_NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_EDVIDSR_Type_NS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_HPFAR_EL2_Type_NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_MFAR_EL3_Type_NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_PAR_EL1_Type_NS (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PAR_Type_NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PFAR_EL1_Type_NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_PFAR_EL2_Type_NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_PMPCSR_Type_NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _set_EDSCR_Type_NS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_NS r v)

def _update_SCRType_SCD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SCR_Type_SCD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_SCR_Type_SCD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_SCRType_SIF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SCR_EL3_Type_SIF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SCR_Type_SIF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SCRType_SMD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SCR_EL3_Type_SMD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SCRType_ST (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_ID_AA64MMFR2_EL1_Type_ST (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_PMSFCR_EL1_Type_ST (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_SCR_EL3_Type_ST (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_ID_AA64MMFR2_EL1_Type_ST (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_PMSFCR_EL1_Type_ST (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_SCRType_TWE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_HCR_EL2_Type_TWE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_HCR_Type_TWE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_SCR_EL3_Type_TWE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_SCR_Type_TWE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_HCR_Type_TWE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_SCR_Type_TWE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_SCRType_TWI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_HCR_EL2_Type_TWI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_HCR_Type_TWI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_SCR_EL3_Type_TWI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_SCR_Type_TWI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_HCR_Type_TWI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_SCR_Type_TWI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_SCRType_nET (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SCR_Type_nET (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_SCR_Type_nET (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def undefined_SCTLRType (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _update_SCTLRType_A (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_DISR_EL1_Type_A (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_DISR_Type_A (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_DSPSR_EL0_Type_A (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_DSPSR_Type_A (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_EDSCR_Type_A (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_HSCTLR_Type_A (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ISR_EL1_Type_A (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_ISR_Type_A (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_SCTLR_EL1_Type_A (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_SCTLR_EL2_Type_A (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_SCTLR_EL3_Type_A (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_SCTLR_Type_A (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_SPSR_EL1_Type_A (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_SPSR_EL2_Type_A (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_SPSR_EL3_Type_A (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_SPSR_abt_Type_A (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_SPSR_fiq_Type_A (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_SPSR_hyp_Type_A (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_SPSR_irq_Type_A (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_SPSR_mon_Type_A (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_SPSR_svc_Type_A (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_SPSR_und_Type_A (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_VDISR_EL2_Type_A (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_VDISR_Type_A (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_DISR_EL1_Type_A (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_DISR_Type_A (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_DSPSR_EL0_Type_A (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_DSPSR_Type_A (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_ISR_EL1_Type_A (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_ISR_Type_A (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_SPSR_EL1_Type_A (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_SPSR_EL2_Type_A (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_SPSR_EL3_Type_A (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_SPSR_abt_Type_A (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_SPSR_fiq_Type_A (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_SPSR_hyp_Type_A (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_SPSR_irq_Type_A (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_SPSR_mon_Type_A (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_SPSR_svc_Type_A (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_SPSR_und_Type_A (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_VDISR_EL2_Type_A (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_VDISR_Type_A (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_SCTLRType_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_DSPSR_EL0_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_DSPSR_Type_C (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_FPSCR_Type_C (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_FPSR_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_HSCTLR_Type_C (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMCNTENCLR_EL0_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMCNTENCLR_Type_C (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMCNTENSET_EL0_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMCNTENSET_Type_C (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMCNTEN_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMCR_EL0_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMCR_Type_C (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PMINTENCLR_EL1_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMINTENCLR_Type_C (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMINTENSET_EL1_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMINTENSET_Type_C (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMINTEN_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMOVSCLR_EL0_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMOVSSET_EL0_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMOVS_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMUACR_EL1_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMZR_EL0_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SCTLR_EL1_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_SCTLR_EL2_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_SCTLR_EL3_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_SCTLR_Type_C (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_SPSR_EL1_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_SPSR_EL2_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_SPSR_EL3_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_SPSR_abt_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_SPSR_fiq_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_SPSR_hyp_Type_C (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_SPSR_irq_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_SPSR_mon_Type_C (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_SPSR_svc_Type_C (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_SPSR_und_Type_C (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_DSPSR_EL0_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_DSPSR_Type_C (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_FPSCR_Type_C (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_FPSR_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMCNTENCLR_EL0_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMCNTENCLR_Type_C (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMCNTEN_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMCR_Type_C (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMINTENCLR_EL1_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMINTENCLR_Type_C (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMINTENSET_EL1_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMINTENSET_Type_C (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMINTEN_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMOVSCLR_EL0_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMOVSR_Type_C (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMOVSSET_EL0_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMOVSSET_Type_C (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMOVS_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMUACR_EL1_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMZR_EL0_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_SPSR_EL1_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_SPSR_EL2_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_SPSR_EL3_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_SPSR_abt_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_SPSR_fiq_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_SPSR_hyp_Type_C (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_SPSR_irq_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_SPSR_mon_Type_C (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_SPSR_svc_Type_C (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_SPSR_und_Type_C (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _set_PMOVSR_Type_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSR_Type_C r v)

def _set_PMOVSSET_Type_C (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_PMOVSSET_Type_C r v)

def _update_SCTLRType_CP15BEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_HSCTLR_Type_CP15BEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SCTLR_EL1_Type_CP15BEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SCTLR_EL2_Type_CP15BEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SCTLR_Type_CP15BEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_HSCTLR_Type_CP15BEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_SCTLR_EL1_Type_CP15BEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_SCTLR_EL2_Type_CP15BEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_SCTLR_Type_CP15BEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_SCTLRType_DSSBS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_HSCTLR_Type_DSSBS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SCTLR_EL1_Type_DSSBS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_SCTLR_EL2_Type_DSSBS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_SCTLR_EL3_Type_DSSBS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_SCTLR_Type_DSSBS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_SCTLR_EL1_Type_DSSBS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)

def _get_SCTLR_EL2_Type_DSSBS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)

def _update_SCTLRType_DZE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_FPCRType_DZE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_FPCR_Type_DZE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_FPSCR_Type_DZE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SCTLR_EL1_Type_DZE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_SCTLR_EL2_Type_DZE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_FPCRType_DZE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_FPCR_Type_DZE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_FPSCR_Type_DZE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_SCTLR_EL1_Type_DZE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_SCTLR_EL2_Type_DZE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_SCTLRType_E0E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_SCTLR_EL1_Type_E0E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_SCTLR_EL2_Type_E0E (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_SCTLR_EL1_Type_E0E (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_SCTLR_EL2_Type_E0E (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_SCTLRType_EE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_HSCTLR_Type_EE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_SCTLR_EL1_Type_EE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_SCTLR_EL2_Type_EE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_SCTLR_EL3_Type_EE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_SCTLR_Type_EE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_SCTLRType_EPAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _update_SCTLR_EL1_Type_EPAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _update_SCTLR_EL2_Type_EPAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _update_SCTLRType_I (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_DBGVCR32_EL2_Type_I (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_DBGVCR_Type_I (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_DSPSR_EL0_Type_I (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_DSPSR_Type_I (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_HSCTLR_Type_I (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_ISR_EL1_Type_I (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_ISR_Type_I (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SCTLR_EL1_Type_I (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_SCTLR_EL2_Type_I (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_SCTLR_EL3_Type_I (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_SCTLR_Type_I (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_SPSR_EL1_Type_I (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SPSR_EL2_Type_I (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SPSR_EL3_Type_I (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SPSR_abt_Type_I (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SPSR_fiq_Type_I (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SPSR_hyp_Type_I (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SPSR_irq_Type_I (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SPSR_mon_Type_I (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SPSR_svc_Type_I (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SPSR_und_Type_I (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_DBGVCR32_EL2_Type_I (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_DBGVCR_Type_I (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_DSPSR_EL0_Type_I (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_DSPSR_Type_I (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_ISR_EL1_Type_I (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_ISR_Type_I (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SPSR_EL1_Type_I (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SPSR_EL2_Type_I (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SPSR_EL3_Type_I (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SPSR_abt_Type_I (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SPSR_fiq_Type_I (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SPSR_hyp_Type_I (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SPSR_irq_Type_I (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SPSR_mon_Type_I (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SPSR_svc_Type_I (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SPSR_und_Type_I (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_SCTLRType_IESB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_ID_AA64MMFR2_EL1_Type_IESB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_SCTLR_EL1_Type_IESB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_SCTLR_EL2_Type_IESB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_SCTLR_EL3_Type_IESB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_ID_AA64MMFR2_EL1_Type_IESB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_SCTLR_EL1_Type_IESB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_SCTLR_EL2_Type_IESB (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_SCTLRType_ITD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_HSCTLR_Type_ITD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SCTLR_EL1_Type_ITD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SCTLR_EL2_Type_ITD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_SCTLR_Type_ITD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_HSCTLR_Type_ITD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SCTLR_EL1_Type_ITD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SCTLR_EL2_Type_ITD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_SCTLR_Type_ITD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_SCTLRType_M (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_DSPSR_Type_M (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _update_HSCTLR_Type_M (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_MPIDR_Type_M (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMCCFILTR_EL0_Type_M (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMEVTYPER_EL0_Type_M (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMICFILTR_EL0_Type_M (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_SCTLR_EL1_Type_M (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_SCTLR_EL2_Type_M (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_SCTLR_EL3_Type_M (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_SCTLR_Type_M (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_SPSR_abt_Type_M (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _update_SPSR_fiq_Type_M (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _update_SPSR_hyp_Type_M (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _update_SPSR_irq_Type_M (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _update_SPSR_mon_Type_M (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _update_SPSR_svc_Type_M (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _update_SPSR_und_Type_M (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def _update_VMPIDR_Type_M (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_DSPSR_Type_M (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _get_MPIDR_Type_M (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMCCFILTR_EL0_Type_M (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMEVTYPER_EL0_Type_M (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMICFILTR_EL0_Type_M (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_SPSR_abt_Type_M (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _get_SPSR_fiq_Type_M (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _get_SPSR_hyp_Type_M (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _get_SPSR_irq_Type_M (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _get_SPSR_mon_Type_M (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _get_SPSR_svc_Type_M (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _get_SPSR_und_Type_M (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _get_VMPIDR_Type_M (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_SCTLRType_NMI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_GICD_TYPER_Type_NMI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_ICC_AP1R_EL1_Type_NMI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_ICC_RPR_EL1_Type_NMI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_ICH_AP1R_EL2_Type_NMI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_ICH_LR_EL2_Type_NMI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_ICV_AP1R_EL1_Type_NMI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_ICV_RPR_EL1_Type_NMI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_ID_AA64PFR1_EL1_Type_NMI (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_SCTLR_EL1_Type_NMI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_SCTLR_EL2_Type_NMI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_SCTLR_EL3_Type_NMI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _get_GICD_TYPER_Type_NMI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_ICC_AP1R_EL1_Type_NMI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_ICC_RPR_EL1_Type_NMI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_ICH_AP1R_EL2_Type_NMI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_ICH_LR_EL2_Type_NMI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _get_ICV_AP1R_EL1_Type_NMI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_ICV_RPR_EL1_Type_NMI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_ID_AA64PFR1_EL1_Type_NMI (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_SCTLR_EL1_Type_NMI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _get_SCTLR_EL2_Type_NMI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _update_SCTLRType_SA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_LORSA_EL1_Type_SA (v : (BitVec 64)) (x : (BitVec 40)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 16 x)

def _update_SCTLR_EL1_Type_SA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_SCTLR_EL2_Type_SA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_SCTLR_EL3_Type_SA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_VSTCR_EL2_Type_SA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_LORSA_EL1_Type_SA (v : (BitVec 64)) : (BitVec 40) :=
  (Sail.BitVec.extractLsb v 55 16)

def _get_SCTLR_EL1_Type_SA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_SCTLR_EL2_Type_SA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_SCTLRType_SA0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_SCTLR_EL1_Type_SA0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_SCTLR_EL2_Type_SA0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_SCTLR_EL1_Type_SA0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_SCTLR_EL2_Type_SA0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_SCTLRType_SED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_HSCTLR_Type_SED (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_SCTLR_EL1_Type_SED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_SCTLR_EL2_Type_SED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_SCTLR_Type_SED (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_HSCTLR_Type_SED (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_SCTLR_EL1_Type_SED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_SCTLR_EL2_Type_SED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_SCTLR_Type_SED (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_SCTLRType_SPAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_SCTLR_EL1_Type_SPAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_SCTLR_EL2_Type_SPAN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_SCTLR_Type_SPAN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_SCTLR_EL1_Type_SPAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_SCTLR_EL2_Type_SPAN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_SCTLRType_SPINTMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_SCTLR_EL1_Type_SPINTMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_SCTLR_EL2_Type_SPINTMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_SCTLR_EL3_Type_SPINTMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _get_SCTLR_EL1_Type_SPINTMASK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _get_SCTLR_EL2_Type_SPINTMASK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _update_SCTLRType_TIDCP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_HCR_EL2_Type_TIDCP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_HCR_Type_TIDCP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_SCTLR_EL1_Type_TIDCP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_SCTLR_EL2_Type_TIDCP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _get_HCR_Type_TIDCP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_SCTLR_EL1_Type_TIDCP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_SCTLR_EL2_Type_TIDCP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _update_SCTLRType_TME (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _update_HCR_EL2_Type_TME (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)

def _update_ID_AA64ISAR0_EL1_Type_TME (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_SCR_EL3_Type_TME (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _update_SCTLR_EL1_Type_TME (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _update_SCTLR_EL2_Type_TME (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _update_SCTLR_EL3_Type_TME (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _get_ID_AA64ISAR0_EL1_Type_TME (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_SCTLR_EL1_Type_TME (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)

def _get_SCTLR_EL2_Type_TME (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)

def _update_SCTLRType_TME0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _update_SCTLR_EL1_Type_TME0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _update_SCTLR_EL2_Type_TME0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _get_SCTLR_EL1_Type_TME0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)

def _get_SCTLR_EL2_Type_TME0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)

def _update_SCTLRType_TMT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)

def _update_SCTLR_EL1_Type_TMT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)

def _update_SCTLR_EL2_Type_TMT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)

def _update_SCTLR_EL3_Type_TMT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)

def _get_SCTLR_EL1_Type_TMT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 51 51)

def _get_SCTLR_EL2_Type_TMT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 51 51)

def _update_SCTLRType_TMT0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _update_SCTLR_EL1_Type_TMT0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _update_SCTLR_EL2_Type_TMT0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _get_SCTLR_EL1_Type_TMT0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)

def _get_SCTLR_EL2_Type_TMT0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)

def _update_SCTLRType_TSCXT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_SCTLR_EL1_Type_TSCXT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_SCTLR_EL2_Type_TSCXT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_SCTLR_EL1_Type_TSCXT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_SCTLR_EL2_Type_TSCXT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_SCTLRType_UCI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_SCTLR_EL1_Type_UCI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_SCTLR_EL2_Type_UCI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_SCTLR_EL1_Type_UCI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_SCTLR_EL2_Type_UCI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_SCTLRType_UCT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_SCTLR_EL1_Type_UCT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_SCTLR_EL2_Type_UCT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_SCTLR_EL1_Type_UCT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_SCTLR_EL2_Type_UCT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_SCTLRType_UMA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_SCTLR_EL1_Type_UMA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_SCTLR_EL1_Type_UMA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_SCTLRType_WXN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_HSCTLR_Type_WXN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_SCTLR_EL1_Type_WXN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_SCTLR_EL2_Type_WXN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_SCTLR_EL3_Type_WXN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_SCTLR_Type_WXN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_SCTLRType_nAA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SCTLR_EL1_Type_nAA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SCTLR_EL2_Type_nAA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SCTLR_EL3_Type_nAA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_SCTLR_EL1_Type_nAA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_SCTLR_EL2_Type_nAA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_SCTLRType_nTWE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_SCTLR_EL1_Type_nTWE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_SCTLR_EL2_Type_nTWE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_SCTLR_Type_nTWE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_SCTLR_EL1_Type_nTWE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_SCTLR_EL2_Type_nTWE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_SCTLR_Type_nTWE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_SCTLRType_nTWI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_SCTLR_EL1_Type_nTWI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_SCTLR_EL2_Type_nTWI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_SCTLR_Type_nTWI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_SCTLR_EL1_Type_nTWI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_SCTLR_EL2_Type_nTWI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_SCTLR_Type_nTWI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_MAIRType_Attr0 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_HMAIR0_Type_Attr0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_MAIR0_Type_Attr0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_MAIR2_EL1_Type_Attr0 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_MAIR2_EL2_Type_Attr0 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_MAIR2_EL3_Type_Attr0 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_MAIR_EL1_Type_Attr0 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_MAIR_EL2_Type_Attr0 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_MAIR_EL3_Type_Attr0 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _get_HMAIR0_Type_Attr0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_MAIR0_Type_Attr0 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_MAIR2_EL1_Type_Attr0 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_MAIR2_EL2_Type_Attr0 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_MAIR2_EL3_Type_Attr0 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_MAIR_EL1_Type_Attr0 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_MAIR_EL2_Type_Attr0 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_MAIR_EL3_Type_Attr0 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _update_MAIRType_Attr1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_HMAIR0_Type_Attr1 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_MAIR0_Type_Attr1 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_MAIR2_EL1_Type_Attr1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_MAIR2_EL2_Type_Attr1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_MAIR2_EL3_Type_Attr1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_MAIR_EL1_Type_Attr1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_MAIR_EL2_Type_Attr1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_MAIR_EL3_Type_Attr1 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _get_HMAIR0_Type_Attr1 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_MAIR0_Type_Attr1 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_MAIR2_EL1_Type_Attr1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_MAIR2_EL2_Type_Attr1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_MAIR2_EL3_Type_Attr1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_MAIR_EL1_Type_Attr1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_MAIR_EL2_Type_Attr1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_MAIR_EL3_Type_Attr1 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _update_MAIRType_Attr2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_HMAIR0_Type_Attr2 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_MAIR0_Type_Attr2 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_MAIR2_EL1_Type_Attr2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_MAIR2_EL2_Type_Attr2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_MAIR2_EL3_Type_Attr2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_MAIR_EL1_Type_Attr2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_MAIR_EL2_Type_Attr2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_MAIR_EL3_Type_Attr2 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _get_HMAIR0_Type_Attr2 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_MAIR0_Type_Attr2 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_MAIR2_EL1_Type_Attr2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_MAIR2_EL2_Type_Attr2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_MAIR2_EL3_Type_Attr2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_MAIR_EL1_Type_Attr2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_MAIR_EL2_Type_Attr2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_MAIR_EL3_Type_Attr2 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _update_MAIRType_Attr3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_HMAIR0_Type_Attr3 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_MAIR0_Type_Attr3 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_MAIR2_EL1_Type_Attr3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_MAIR2_EL2_Type_Attr3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_MAIR2_EL3_Type_Attr3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_MAIR_EL1_Type_Attr3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_MAIR_EL2_Type_Attr3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_MAIR_EL3_Type_Attr3 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _get_HMAIR0_Type_Attr3 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_MAIR0_Type_Attr3 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_MAIR2_EL1_Type_Attr3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_MAIR2_EL2_Type_Attr3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_MAIR2_EL3_Type_Attr3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_MAIR_EL1_Type_Attr3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_MAIR_EL2_Type_Attr3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_MAIR_EL3_Type_Attr3 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _update_MAIRType_Attr4 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _update_HMAIR1_Type_Attr4 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_MAIR1_Type_Attr4 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_MAIR2_EL1_Type_Attr4 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _update_MAIR2_EL2_Type_Attr4 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _update_MAIR2_EL3_Type_Attr4 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _update_MAIR_EL1_Type_Attr4 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _update_MAIR_EL2_Type_Attr4 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _update_MAIR_EL3_Type_Attr4 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)

def _get_HMAIR1_Type_Attr4 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_MAIR1_Type_Attr4 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_MAIR2_EL1_Type_Attr4 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)

def _get_MAIR2_EL2_Type_Attr4 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)

def _get_MAIR2_EL3_Type_Attr4 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)

def _get_MAIR_EL1_Type_Attr4 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)

def _get_MAIR_EL2_Type_Attr4 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)

def _get_MAIR_EL3_Type_Attr4 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)

def _update_MAIRType_Attr5 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)

def _update_HMAIR1_Type_Attr5 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_MAIR1_Type_Attr5 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_MAIR2_EL1_Type_Attr5 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)

def _update_MAIR2_EL2_Type_Attr5 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)

def _update_MAIR2_EL3_Type_Attr5 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)

def _update_MAIR_EL1_Type_Attr5 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)

def _update_MAIR_EL2_Type_Attr5 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)

def _update_MAIR_EL3_Type_Attr5 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)

def _get_HMAIR1_Type_Attr5 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_MAIR1_Type_Attr5 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 15 8)

def _get_MAIR2_EL1_Type_Attr5 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 47 40)

def _get_MAIR2_EL2_Type_Attr5 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 47 40)

def _get_MAIR2_EL3_Type_Attr5 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 47 40)

def _get_MAIR_EL1_Type_Attr5 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 47 40)

def _get_MAIR_EL2_Type_Attr5 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 47 40)

def _get_MAIR_EL3_Type_Attr5 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 47 40)

def _update_MAIRType_Attr6 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _update_HMAIR1_Type_Attr6 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_MAIR1_Type_Attr6 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_MAIR2_EL1_Type_Attr6 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _update_MAIR2_EL2_Type_Attr6 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _update_MAIR2_EL3_Type_Attr6 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _update_MAIR_EL1_Type_Attr6 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _update_MAIR_EL2_Type_Attr6 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _update_MAIR_EL3_Type_Attr6 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _get_HMAIR1_Type_Attr6 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_MAIR1_Type_Attr6 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_MAIR2_EL1_Type_Attr6 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _get_MAIR2_EL2_Type_Attr6 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _get_MAIR2_EL3_Type_Attr6 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _get_MAIR_EL1_Type_Attr6 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _get_MAIR_EL2_Type_Attr6 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _get_MAIR_EL3_Type_Attr6 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _update_MAIRType_Attr7 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 56 x)

def _update_HMAIR1_Type_Attr7 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_MAIR1_Type_Attr7 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_MAIR2_EL1_Type_Attr7 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 56 x)

def _update_MAIR2_EL2_Type_Attr7 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 56 x)

def _update_MAIR2_EL3_Type_Attr7 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 56 x)

def _update_MAIR_EL1_Type_Attr7 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 56 x)

def _update_MAIR_EL2_Type_Attr7 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 56 x)

def _update_MAIR_EL3_Type_Attr7 (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 56 x)

def _get_HMAIR1_Type_Attr7 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_MAIR1_Type_Attr7 (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 31 24)

def _get_MAIR2_EL1_Type_Attr7 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)

def _get_MAIR2_EL2_Type_Attr7 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)

def _get_MAIR2_EL3_Type_Attr7 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)

def _get_MAIR_EL1_Type_Attr7 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)

def _get_MAIR_EL2_Type_Attr7 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)

def _get_MAIR_EL3_Type_Attr7 (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)

def _get_S1PIRType_Perm0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_S1PIRType_Perm0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_PIRE0_EL1_Type_Perm0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_PIRE0_EL2_Type_Perm0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_PIR_EL1_Type_Perm0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_PIR_EL2_Type_Perm0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_PIR_EL3_Type_Perm0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_POR_EL0_Type_Perm0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_POR_EL1_Type_Perm0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_POR_EL2_Type_Perm0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_POR_EL3_Type_Perm0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_S1PORType_Perm0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_S2PIRType_Perm0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_S2PIR_EL2_Type_Perm0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_S2POR_EL1_Type_Perm0 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_PIRE0_EL1_Type_Perm0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_PIRE0_EL2_Type_Perm0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_PIR_EL1_Type_Perm0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_PIR_EL2_Type_Perm0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_PIR_EL3_Type_Perm0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_POR_EL0_Type_Perm0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_POR_EL1_Type_Perm0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_POR_EL2_Type_Perm0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_POR_EL3_Type_Perm0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_S1PORType_Perm0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_S2PIRType_Perm0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_S2PIR_EL2_Type_Perm0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_S2POR_EL1_Type_Perm0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_S1PIRType_Perm1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_S1PIRType_Perm1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_PIRE0_EL1_Type_Perm1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_PIRE0_EL2_Type_Perm1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_PIR_EL1_Type_Perm1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_PIR_EL2_Type_Perm1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_PIR_EL3_Type_Perm1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_POR_EL0_Type_Perm1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_POR_EL1_Type_Perm1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_POR_EL2_Type_Perm1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_POR_EL3_Type_Perm1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_S1PORType_Perm1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_S2PIRType_Perm1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_S2PIR_EL2_Type_Perm1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_S2POR_EL1_Type_Perm1 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_PIRE0_EL1_Type_Perm1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_PIRE0_EL2_Type_Perm1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_PIR_EL1_Type_Perm1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_PIR_EL2_Type_Perm1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_PIR_EL3_Type_Perm1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_POR_EL0_Type_Perm1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_POR_EL1_Type_Perm1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_POR_EL2_Type_Perm1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_POR_EL3_Type_Perm1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_S1PORType_Perm1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_S2PIRType_Perm1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_S2PIR_EL2_Type_Perm1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_S2POR_EL1_Type_Perm1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_S1PIRType_Perm10 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _update_S1PIRType_Perm10 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_PIRE0_EL1_Type_Perm10 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_PIRE0_EL2_Type_Perm10 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_PIR_EL1_Type_Perm10 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_PIR_EL2_Type_Perm10 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_PIR_EL3_Type_Perm10 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_POR_EL0_Type_Perm10 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_POR_EL1_Type_Perm10 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_POR_EL2_Type_Perm10 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_POR_EL3_Type_Perm10 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_S1PORType_Perm10 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_S2PIRType_Perm10 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_S2PIR_EL2_Type_Perm10 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _update_S2POR_EL1_Type_Perm10 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _get_PIRE0_EL1_Type_Perm10 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_PIRE0_EL2_Type_Perm10 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_PIR_EL1_Type_Perm10 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_PIR_EL2_Type_Perm10 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_PIR_EL3_Type_Perm10 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_POR_EL0_Type_Perm10 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_POR_EL1_Type_Perm10 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_POR_EL2_Type_Perm10 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_POR_EL3_Type_Perm10 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_S1PORType_Perm10 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_S2PIRType_Perm10 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_S2PIR_EL2_Type_Perm10 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_S2POR_EL1_Type_Perm10 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_S1PIRType_Perm11 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _update_S1PIRType_Perm11 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_PIRE0_EL1_Type_Perm11 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_PIRE0_EL2_Type_Perm11 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_PIR_EL1_Type_Perm11 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_PIR_EL2_Type_Perm11 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_PIR_EL3_Type_Perm11 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_POR_EL0_Type_Perm11 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_POR_EL1_Type_Perm11 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_POR_EL2_Type_Perm11 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_POR_EL3_Type_Perm11 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_S1PORType_Perm11 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_S2PIRType_Perm11 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_S2PIR_EL2_Type_Perm11 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _update_S2POR_EL1_Type_Perm11 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 44 x)

def _get_PIRE0_EL1_Type_Perm11 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_PIRE0_EL2_Type_Perm11 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_PIR_EL1_Type_Perm11 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_PIR_EL2_Type_Perm11 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_PIR_EL3_Type_Perm11 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_POR_EL0_Type_Perm11 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_POR_EL1_Type_Perm11 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_POR_EL2_Type_Perm11 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_POR_EL3_Type_Perm11 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_S1PORType_Perm11 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_S2PIRType_Perm11 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_S2PIR_EL2_Type_Perm11 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_S2POR_EL1_Type_Perm11 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 47 44)

def _get_S1PIRType_Perm12 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _update_S1PIRType_Perm12 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_PIRE0_EL1_Type_Perm12 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_PIRE0_EL2_Type_Perm12 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_PIR_EL1_Type_Perm12 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_PIR_EL2_Type_Perm12 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_PIR_EL3_Type_Perm12 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_POR_EL0_Type_Perm12 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_POR_EL1_Type_Perm12 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_POR_EL2_Type_Perm12 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_POR_EL3_Type_Perm12 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_S1PORType_Perm12 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_S2PIRType_Perm12 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_S2PIR_EL2_Type_Perm12 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _update_S2POR_EL1_Type_Perm12 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _get_PIRE0_EL1_Type_Perm12 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_PIRE0_EL2_Type_Perm12 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_PIR_EL1_Type_Perm12 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_PIR_EL2_Type_Perm12 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_PIR_EL3_Type_Perm12 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_POR_EL0_Type_Perm12 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_POR_EL1_Type_Perm12 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_POR_EL2_Type_Perm12 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_POR_EL3_Type_Perm12 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_S1PORType_Perm12 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_S2PIRType_Perm12 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_S2PIR_EL2_Type_Perm12 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_S2POR_EL1_Type_Perm12 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _get_S1PIRType_Perm13 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _update_S1PIRType_Perm13 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_PIRE0_EL1_Type_Perm13 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_PIRE0_EL2_Type_Perm13 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_PIR_EL1_Type_Perm13 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_PIR_EL2_Type_Perm13 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_PIR_EL3_Type_Perm13 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_POR_EL0_Type_Perm13 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_POR_EL1_Type_Perm13 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_POR_EL2_Type_Perm13 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_POR_EL3_Type_Perm13 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_S1PORType_Perm13 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_S2PIRType_Perm13 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_S2PIR_EL2_Type_Perm13 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _update_S2POR_EL1_Type_Perm13 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _get_PIRE0_EL1_Type_Perm13 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _get_PIRE0_EL2_Type_Perm13 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _get_PIR_EL1_Type_Perm13 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _get_PIR_EL2_Type_Perm13 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _get_PIR_EL3_Type_Perm13 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _get_POR_EL0_Type_Perm13 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _get_POR_EL1_Type_Perm13 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _get_POR_EL2_Type_Perm13 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _get_POR_EL3_Type_Perm13 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _get_S1PORType_Perm13 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _get_S2PIRType_Perm13 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _get_S2PIR_EL2_Type_Perm13 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _get_S2POR_EL1_Type_Perm13 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _get_S1PIRType_Perm14 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _update_S1PIRType_Perm14 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_PIRE0_EL1_Type_Perm14 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_PIRE0_EL2_Type_Perm14 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_PIR_EL1_Type_Perm14 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_PIR_EL2_Type_Perm14 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_PIR_EL3_Type_Perm14 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_POR_EL0_Type_Perm14 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_POR_EL1_Type_Perm14 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_POR_EL2_Type_Perm14 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_POR_EL3_Type_Perm14 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_S1PORType_Perm14 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_S2PIRType_Perm14 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_S2PIR_EL2_Type_Perm14 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_S2POR_EL1_Type_Perm14 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _get_PIRE0_EL1_Type_Perm14 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_PIRE0_EL2_Type_Perm14 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_PIR_EL1_Type_Perm14 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_PIR_EL2_Type_Perm14 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_PIR_EL3_Type_Perm14 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_POR_EL0_Type_Perm14 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_POR_EL1_Type_Perm14 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_POR_EL2_Type_Perm14 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_POR_EL3_Type_Perm14 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_S1PORType_Perm14 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_S2PIRType_Perm14 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_S2PIR_EL2_Type_Perm14 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_S2POR_EL1_Type_Perm14 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_S1PIRType_Perm15 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _update_S1PIRType_Perm15 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_PIRE0_EL1_Type_Perm15 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_PIRE0_EL2_Type_Perm15 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_PIR_EL1_Type_Perm15 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_PIR_EL2_Type_Perm15 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_PIR_EL3_Type_Perm15 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_POR_EL0_Type_Perm15 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_POR_EL1_Type_Perm15 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_POR_EL2_Type_Perm15 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_POR_EL3_Type_Perm15 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_S1PORType_Perm15 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_S2PIRType_Perm15 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_S2PIR_EL2_Type_Perm15 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_S2POR_EL1_Type_Perm15 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _get_PIRE0_EL1_Type_Perm15 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _get_PIRE0_EL2_Type_Perm15 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _get_PIR_EL1_Type_Perm15 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _get_PIR_EL2_Type_Perm15 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _get_PIR_EL3_Type_Perm15 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _get_POR_EL0_Type_Perm15 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _get_POR_EL1_Type_Perm15 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _get_POR_EL2_Type_Perm15 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _get_POR_EL3_Type_Perm15 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _get_S1PORType_Perm15 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _get_S2PIRType_Perm15 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _get_S2PIR_EL2_Type_Perm15 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _get_S2POR_EL1_Type_Perm15 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _get_S1PIRType_Perm2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_S1PIRType_Perm2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_PIRE0_EL1_Type_Perm2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_PIRE0_EL2_Type_Perm2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_PIR_EL1_Type_Perm2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_PIR_EL2_Type_Perm2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_PIR_EL3_Type_Perm2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_POR_EL0_Type_Perm2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_POR_EL1_Type_Perm2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_POR_EL2_Type_Perm2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_POR_EL3_Type_Perm2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_S1PORType_Perm2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_S2PIRType_Perm2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_S2PIR_EL2_Type_Perm2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_S2POR_EL1_Type_Perm2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_PIRE0_EL1_Type_Perm2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_PIRE0_EL2_Type_Perm2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_PIR_EL1_Type_Perm2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_PIR_EL2_Type_Perm2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_PIR_EL3_Type_Perm2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_POR_EL0_Type_Perm2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_POR_EL1_Type_Perm2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_POR_EL2_Type_Perm2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_POR_EL3_Type_Perm2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_S1PORType_Perm2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_S2PIRType_Perm2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_S2PIR_EL2_Type_Perm2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_S2POR_EL1_Type_Perm2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_S1PIRType_Perm3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_S1PIRType_Perm3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_PIRE0_EL1_Type_Perm3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_PIRE0_EL2_Type_Perm3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_PIR_EL1_Type_Perm3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_PIR_EL2_Type_Perm3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_PIR_EL3_Type_Perm3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_POR_EL0_Type_Perm3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_POR_EL1_Type_Perm3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_POR_EL2_Type_Perm3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_POR_EL3_Type_Perm3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_S1PORType_Perm3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_S2PIRType_Perm3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_S2PIR_EL2_Type_Perm3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_S2POR_EL1_Type_Perm3 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_PIRE0_EL1_Type_Perm3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_PIRE0_EL2_Type_Perm3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_PIR_EL1_Type_Perm3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_PIR_EL2_Type_Perm3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_PIR_EL3_Type_Perm3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_POR_EL0_Type_Perm3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_POR_EL1_Type_Perm3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_POR_EL2_Type_Perm3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_POR_EL3_Type_Perm3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_S1PORType_Perm3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_S2PIRType_Perm3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_S2PIR_EL2_Type_Perm3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_S2POR_EL1_Type_Perm3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_S1PIRType_Perm4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_S1PIRType_Perm4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_PIRE0_EL1_Type_Perm4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_PIRE0_EL2_Type_Perm4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_PIR_EL1_Type_Perm4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_PIR_EL2_Type_Perm4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_PIR_EL3_Type_Perm4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_POR_EL0_Type_Perm4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_POR_EL1_Type_Perm4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_POR_EL2_Type_Perm4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_POR_EL3_Type_Perm4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_S1PORType_Perm4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_S2PIRType_Perm4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_S2PIR_EL2_Type_Perm4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_S2POR_EL1_Type_Perm4 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_PIRE0_EL1_Type_Perm4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_PIRE0_EL2_Type_Perm4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_PIR_EL1_Type_Perm4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_PIR_EL2_Type_Perm4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_PIR_EL3_Type_Perm4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_POR_EL0_Type_Perm4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_POR_EL1_Type_Perm4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_POR_EL2_Type_Perm4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_POR_EL3_Type_Perm4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_S1PORType_Perm4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_S2PIRType_Perm4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_S2PIR_EL2_Type_Perm4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_S2POR_EL1_Type_Perm4 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_S1PIRType_Perm5 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_S1PIRType_Perm5 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_PIRE0_EL1_Type_Perm5 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_PIRE0_EL2_Type_Perm5 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_PIR_EL1_Type_Perm5 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_PIR_EL2_Type_Perm5 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_PIR_EL3_Type_Perm5 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_POR_EL0_Type_Perm5 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_POR_EL1_Type_Perm5 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_POR_EL2_Type_Perm5 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_POR_EL3_Type_Perm5 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_S1PORType_Perm5 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_S2PIRType_Perm5 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_S2PIR_EL2_Type_Perm5 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_S2POR_EL1_Type_Perm5 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_PIRE0_EL1_Type_Perm5 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_PIRE0_EL2_Type_Perm5 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_PIR_EL1_Type_Perm5 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_PIR_EL2_Type_Perm5 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_PIR_EL3_Type_Perm5 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_POR_EL0_Type_Perm5 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_POR_EL1_Type_Perm5 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_POR_EL2_Type_Perm5 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_POR_EL3_Type_Perm5 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_S1PORType_Perm5 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_S2PIRType_Perm5 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_S2PIR_EL2_Type_Perm5 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_S2POR_EL1_Type_Perm5 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_S1PIRType_Perm6 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_S1PIRType_Perm6 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_PIRE0_EL1_Type_Perm6 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_PIRE0_EL2_Type_Perm6 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_PIR_EL1_Type_Perm6 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_PIR_EL2_Type_Perm6 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_PIR_EL3_Type_Perm6 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_POR_EL0_Type_Perm6 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_POR_EL1_Type_Perm6 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_POR_EL2_Type_Perm6 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_POR_EL3_Type_Perm6 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_S1PORType_Perm6 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_S2PIRType_Perm6 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_S2PIR_EL2_Type_Perm6 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_S2POR_EL1_Type_Perm6 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_PIRE0_EL1_Type_Perm6 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_PIRE0_EL2_Type_Perm6 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_PIR_EL1_Type_Perm6 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_PIR_EL2_Type_Perm6 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_PIR_EL3_Type_Perm6 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_POR_EL0_Type_Perm6 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_POR_EL1_Type_Perm6 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_POR_EL2_Type_Perm6 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_POR_EL3_Type_Perm6 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_S1PORType_Perm6 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_S2PIRType_Perm6 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_S2PIR_EL2_Type_Perm6 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_S2POR_EL1_Type_Perm6 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_S1PIRType_Perm7 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_S1PIRType_Perm7 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_PIRE0_EL1_Type_Perm7 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_PIRE0_EL2_Type_Perm7 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_PIR_EL1_Type_Perm7 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_PIR_EL2_Type_Perm7 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_PIR_EL3_Type_Perm7 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_POR_EL0_Type_Perm7 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_POR_EL1_Type_Perm7 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_POR_EL2_Type_Perm7 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_POR_EL3_Type_Perm7 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_S1PORType_Perm7 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_S2PIRType_Perm7 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_S2PIR_EL2_Type_Perm7 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_S2POR_EL1_Type_Perm7 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_PIRE0_EL1_Type_Perm7 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_PIRE0_EL2_Type_Perm7 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_PIR_EL1_Type_Perm7 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_PIR_EL2_Type_Perm7 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_PIR_EL3_Type_Perm7 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_POR_EL0_Type_Perm7 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_POR_EL1_Type_Perm7 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_POR_EL2_Type_Perm7 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_POR_EL3_Type_Perm7 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_S1PORType_Perm7 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_S2PIRType_Perm7 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_S2PIR_EL2_Type_Perm7 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_S2POR_EL1_Type_Perm7 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_S1PIRType_Perm8 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _update_S1PIRType_Perm8 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_PIRE0_EL1_Type_Perm8 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_PIRE0_EL2_Type_Perm8 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_PIR_EL1_Type_Perm8 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_PIR_EL2_Type_Perm8 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_PIR_EL3_Type_Perm8 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_POR_EL0_Type_Perm8 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_POR_EL1_Type_Perm8 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_POR_EL2_Type_Perm8 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_POR_EL3_Type_Perm8 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_S1PORType_Perm8 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_S2PIRType_Perm8 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_S2PIR_EL2_Type_Perm8 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _update_S2POR_EL1_Type_Perm8 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _get_PIRE0_EL1_Type_Perm8 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_PIRE0_EL2_Type_Perm8 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_PIR_EL1_Type_Perm8 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_PIR_EL2_Type_Perm8 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_PIR_EL3_Type_Perm8 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_POR_EL0_Type_Perm8 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_POR_EL1_Type_Perm8 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_POR_EL2_Type_Perm8 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_POR_EL3_Type_Perm8 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_S1PORType_Perm8 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_S2PIRType_Perm8 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_S2PIR_EL2_Type_Perm8 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_S2POR_EL1_Type_Perm8 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _get_S1PIRType_Perm9 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _update_S1PIRType_Perm9 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_PIRE0_EL1_Type_Perm9 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_PIRE0_EL2_Type_Perm9 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_PIR_EL1_Type_Perm9 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_PIR_EL2_Type_Perm9 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_PIR_EL3_Type_Perm9 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_POR_EL0_Type_Perm9 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_POR_EL1_Type_Perm9 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_POR_EL2_Type_Perm9 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_POR_EL3_Type_Perm9 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_S1PORType_Perm9 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_S2PIRType_Perm9 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_S2PIR_EL2_Type_Perm9 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_S2POR_EL1_Type_Perm9 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _get_PIRE0_EL1_Type_Perm9 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_PIRE0_EL2_Type_Perm9 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_PIR_EL1_Type_Perm9 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_PIR_EL2_Type_Perm9 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_PIR_EL3_Type_Perm9 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_POR_EL0_Type_Perm9 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_POR_EL1_Type_Perm9 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_POR_EL2_Type_Perm9 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_POR_EL3_Type_Perm9 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_S1PORType_Perm9 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_S2PIRType_Perm9 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_S2PIR_EL2_Type_Perm9 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_S2POR_EL1_Type_Perm9 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def undefined_ESRType (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _get_ESRType_EC (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 31 26)

def _update_ESRType_EC (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 26 x)

def _update_EDESR_Type_EC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ESR_EL1_Type_EC (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 26 x)

def _update_ESR_EL2_Type_EC (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 26 x)

def _update_ESR_EL3_Type_EC (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 26 x)

def _update_HSR_Type_EC (v : (BitVec 32)) (x : (BitVec 6)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 26 x)

def _update_PMBSR_EL1_Type_EC (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 26 x)

def _get_ESR_EL1_Type_EC (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 31 26)

def _get_ESR_EL2_Type_EC (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 31 26)

def _get_ESR_EL3_Type_EC (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 31 26)

def _get_HSR_Type_EC (v : (BitVec 32)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 31 26)

def _get_ESRType_IL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_ESRType_IL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_DSPSR_EL0_Type_IL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_DSPSR_Type_IL (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_ESR_EL1_Type_IL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_ESR_EL2_Type_IL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_ESR_EL3_Type_IL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_HSR_Type_IL (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_SPSR_EL1_Type_IL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_SPSR_EL2_Type_IL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_SPSR_EL3_Type_IL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_SPSR_abt_Type_IL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_SPSR_fiq_Type_IL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_SPSR_hyp_Type_IL (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_SPSR_irq_Type_IL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_SPSR_mon_Type_IL (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_SPSR_svc_Type_IL (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_SPSR_und_Type_IL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_DSPSR_EL0_Type_IL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_DSPSR_Type_IL (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_ESR_EL1_Type_IL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_ESR_EL2_Type_IL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_ESR_EL3_Type_IL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_HSR_Type_IL (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_SPSR_EL1_Type_IL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_SPSR_EL2_Type_IL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_SPSR_EL3_Type_IL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_SPSR_abt_Type_IL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_SPSR_fiq_Type_IL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_SPSR_hyp_Type_IL (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_SPSR_irq_Type_IL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_SPSR_mon_Type_IL (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_SPSR_svc_Type_IL (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_SPSR_und_Type_IL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_ESRType_ISS (v : (BitVec 64)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)

def _update_ESRType_ISS (v : (BitVec 64)) (x : (BitVec 25)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 0 x)

def _update_DISR_EL1_Type_ISS (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ESR_EL1_Type_ISS (v : (BitVec 64)) (x : (BitVec 25)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 0 x)

def _update_ESR_EL2_Type_ISS (v : (BitVec 64)) (x : (BitVec 25)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 0 x)

def _update_ESR_EL3_Type_ISS (v : (BitVec 64)) (x : (BitVec 25)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 0 x)

def _update_HSR_Type_ISS (v : (BitVec 32)) (x : (BitVec 25)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 0 x)

def _update_VDISR_EL2_Type_ISS (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_VSESR_EL2_Type_ISS (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _get_DISR_EL1_Type_ISS (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_ESR_EL1_Type_ISS (v : (BitVec 64)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)

def _get_ESR_EL2_Type_ISS (v : (BitVec 64)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)

def _get_ESR_EL3_Type_ISS (v : (BitVec 64)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)

def _get_HSR_Type_ISS (v : (BitVec 32)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 24 0)

def _get_VDISR_EL2_Type_ISS (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def undefined_FPCRType (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_FPCRType (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_FPCRType_AH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_FPCRType_AH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_FPCR_Type_AH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_FPCR_Type_AH (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_FPCRType_AHP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_FPCRType_AHP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_FPCR_Type_AHP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_FPSCR_Type_AHP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_FPCR_Type_AHP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_FPSCR_Type_AHP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_FPCRType_DN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_FPCRType_DN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_FPCR_Type_DN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_FPSCR_Type_DN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_FPCR_Type_DN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_FPSCR_Type_DN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_FPCRType_DZC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _update_FPCRType_DZC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _update_FPSCR_Type_DZC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_FPSR_Type_DZC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_FPSCR_Type_DZC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_FPSR_Type_DZC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_FPCRType_EBF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_FPCRType_EBF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_FPCR_Type_EBF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_FPCR_Type_EBF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_FPCRType_FIZ (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_FPCRType_FIZ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_FPCR_Type_FIZ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_FPCR_Type_FIZ (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_FPCRType_FZ (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_FPCRType_FZ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_FPCR_Type_FZ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_FPSCR_Type_FZ (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_FPCR_Type_FZ (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_FPSCR_Type_FZ (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_FPCRType_FZ16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_FPCRType_FZ16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_FPCR_Type_FZ16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_FPSCR_Type_FZ16 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_FPCR_Type_FZ16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_FPSCR_Type_FZ16 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_FPCRType_IDE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_FPCRType_IDE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_FPCR_Type_IDE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_FPSCR_Type_IDE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_FPCR_Type_IDE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_FPSCR_Type_IDE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_FPCRType_IOC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _update_FPCRType_IOC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_FPSCR_Type_IOC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_FPSR_Type_IOC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_FPSCR_Type_IOC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_FPSR_Type_IOC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_FPCRType_IOE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_FPCRType_IOE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_FPCR_Type_IOE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_FPSCR_Type_IOE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_FPCR_Type_IOE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_FPSCR_Type_IOE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_FPCRType_IXE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_FPCRType_IXE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_FPCR_Type_IXE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_FPSCR_Type_IXE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_FPCR_Type_IXE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_FPSCR_Type_IXE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_FPCRType_NEP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_FPCRType_NEP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_FPCR_Type_NEP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_FPCR_Type_NEP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_FPCRType_OFC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)

def _update_FPCRType_OFC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _update_FPSCR_Type_OFC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_FPSR_Type_OFC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_FPSCR_Type_OFC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_FPSR_Type_OFC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_FPCRType_OFE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_FPCRType_OFE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_FPCR_Type_OFE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_FPSCR_Type_OFE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_FPCR_Type_OFE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_FPSCR_Type_OFE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_FPCRType_RMode (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)

def _update_FPCRType_RMode (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 22 x)

def _update_FPCR_Type_RMode (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 22 x)

def _update_FPSCR_Type_RMode (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 22 x)

def _get_FPCR_Type_RMode (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)

def _get_FPSCR_Type_RMode (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)

def _get_FPCRType_Stride (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)

def _update_FPCRType_Stride (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 20 x)

def _update_FPCR_Type_Stride (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 20 x)

def _update_FPSCR_Type_Stride (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 20 x)

def _get_FPCR_Type_Stride (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)

def _get_FPSCR_Type_Stride (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)

def _get_FPCRType_UFE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_FPCRType_UFE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_FPCR_Type_UFE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_FPSCR_Type_UFE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_FPCR_Type_UFE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_FPSCR_Type_UFE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_FPCRType_length (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 18 16)

def _update_FPCRType_length (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 16 x)

def _update_FPCR_Type_length (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 16 x)

def _update_FPSCR_Type_length (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 16 x)

def _get_FPCR_Type_length (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 18 16)

def _get_FPSCR_Type_length (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 18 16)

def undefined_BRBSRCType (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _get_BRBSRCType_ADDRESS (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _update_BRBSRCType_ADDRESS (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_BRBSRCINJ_EL1_Type_ADDRESS (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_BRBSRC_EL1_Type_ADDRESS (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_BRBTGTINJ_EL1_Type_ADDRESS (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_BRBTGTType_ADDRESS (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_BRBTGT_EL1_Type_ADDRESS (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_PMIAR_EL1_Type_ADDRESS (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _get_BRBSRCINJ_EL1_Type_ADDRESS (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_BRBSRC_EL1_Type_ADDRESS (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_BRBTGTINJ_EL1_Type_ADDRESS (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_BRBTGTType_ADDRESS (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_BRBTGT_EL1_Type_ADDRESS (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_PMIAR_EL1_Type_ADDRESS (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def undefined_BRBTGTType (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_BRBINFType (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_BRBINFType (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_BRBINFType_CC (v : (BitVec 64)) : (BitVec 14) :=
  (Sail.BitVec.extractLsb v 45 32)

def _update_BRBINFType_CC (v : (BitVec 64)) (x : (BitVec 14)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 32 x)

def _update_BRBCR_EL1_Type_CC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_BRBCR_EL2_Type_CC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_BRBIDR0_EL1_Type_CC (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_BRBINFINJ_EL1_Type_CC (v : (BitVec 64)) (x : (BitVec 14)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 32 x)

def _update_BRBINF_EL1_Type_CC (v : (BitVec 64)) (x : (BitVec 14)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 32 x)

def _update_PMCFGR_Type_CC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_BRBIDR0_EL1_Type_CC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_BRBINFINJ_EL1_Type_CC (v : (BitVec 64)) : (BitVec 14) :=
  (Sail.BitVec.extractLsb v 45 32)

def _get_BRBINF_EL1_Type_CC (v : (BitVec 64)) : (BitVec 14) :=
  (Sail.BitVec.extractLsb v 45 32)

def _get_PMCFGR_Type_CC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_BRBINFType_CCU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)

def _update_BRBINFType_CCU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _update_BRBINFINJ_EL1_Type_CCU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _update_BRBINF_EL1_Type_CCU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _get_BRBINFINJ_EL1_Type_CCU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)

def _get_BRBINF_EL1_Type_CCU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)

def _get_BRBINFType_EL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def _update_BRBINFType_EL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _update_BRBINFINJ_EL1_Type_EL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _update_BRBINF_EL1_Type_EL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _update_EDPCSR_Type_EL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 61 x)

def _update_PMPCSR_Type_EL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 61 x)

def _get_BRBINFINJ_EL1_Type_EL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def _get_BRBINF_EL1_Type_EL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def _get_EDPCSR_Type_EL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 62 61)

def _get_PMPCSR_Type_EL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 62 61)

def _set_EDSCR_Type_EL (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_EDSCR_Type_EL r v)

def _get_BRBINFType_LASTFAILED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_BRBINFType_LASTFAILED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_BRBFCR_EL1_Type_LASTFAILED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_BRBINFINJ_EL1_Type_LASTFAILED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_BRBINF_EL1_Type_LASTFAILED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_BRBINFINJ_EL1_Type_LASTFAILED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_BRBINF_EL1_Type_LASTFAILED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_BRBINFType_MPRED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_BRBINFType_MPRED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_BRBCR_EL1_Type_MPRED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_BRBCR_EL2_Type_MPRED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_BRBINFINJ_EL1_Type_MPRED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_BRBINF_EL1_Type_MPRED (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_BRBINFINJ_EL1_Type_MPRED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_BRBINF_EL1_Type_MPRED (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_BRBINFType_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_BRBINFType_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_BRBINFINJ_EL1_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_BRBINF_EL1_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_DSPSR_EL0_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_DSPSR_Type_T (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMCCFILTR_EL0_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMEVTYPER_EL0_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMICFILTR_EL0_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMPCSR_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _update_SPSR_EL1_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SPSR_EL2_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SPSR_EL3_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SPSR_abt_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SPSR_fiq_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SPSR_hyp_Type_T (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SPSR_irq_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SPSR_mon_Type_T (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SPSR_svc_Type_T (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SPSR_und_Type_T (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_BRBINFINJ_EL1_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_BRBINF_EL1_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_DSPSR_EL0_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_DSPSR_Type_T (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMCCFILTR_EL0_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMEVTYPER_EL0_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMICFILTR_EL0_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMPCSR_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _get_SPSR_EL1_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_SPSR_EL2_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_SPSR_EL3_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_SPSR_abt_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_SPSR_fiq_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_SPSR_hyp_Type_T (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_SPSR_irq_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_SPSR_mon_Type_T (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_SPSR_svc_Type_T (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_SPSR_und_Type_T (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_BRBINFType_TYPE (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 13 8)

def _update_BRBINFType_TYPE (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 8 x)

def _update_BRBINFINJ_EL1_Type_TYPE (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 8 x)

def _update_BRBINF_EL1_Type_TYPE (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 8 x)

def _get_BRBINFINJ_EL1_Type_TYPE (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 13 8)

def _get_BRBINF_EL1_Type_TYPE (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 13 8)

def _get_BRBINFType_VALID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _update_BRBINFType_VALID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _update_BRBINFINJ_EL1_Type_VALID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _update_BRBINF_EL1_Type_VALID (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _get_BRBINFINJ_EL1_Type_VALID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _get_BRBINF_EL1_Type_VALID (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def undefined_Signal (_ : Unit) : SailM Signal := do
  (internal_pick [Signal_Low, Signal_High])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def Signal_of_num (arg_ : Nat) : Signal :=
  match arg_ with
  | 0 => Signal_Low
  | _ => Signal_High

def num_of_Signal (arg_ : Signal) : Int :=
  match arg_ with
  | .Signal_Low => 0
  | .Signal_High => 1

def PMU_EVENT_SW_INCR : (BitVec 16) := 0x0000#16

def PMU_EVENT_INST_SPEC : (BitVec 16) := 0x001B#16

def PMU_EVENT_SAMPLE_POP : (BitVec 16) := 0x4000#16

def PMU_EVENT_SAMPLE_FEED : (BitVec 16) := 0x4001#16

def PMU_EVENT_SAMPLE_FILTRATE : (BitVec 16) := 0x4002#16

def PMU_EVENT_SAMPLE_COLLISION : (BitVec 16) := 0x4003#16

def PMU_EVENT_SAMPLE_WRAP : (BitVec 16) := 0x8123#16

def PMU_EVENT_SAMPLE_FEED_BR : (BitVec 16) := 0x812A#16

def PMU_EVENT_SAMPLE_FEED_LD : (BitVec 16) := 0x812B#16

def PMU_EVENT_SAMPLE_FEED_ST : (BitVec 16) := 0x812C#16

def PMU_EVENT_SAMPLE_FEED_OP : (BitVec 16) := 0x812D#16

def PMU_EVENT_SAMPLE_FEED_EVENT : (BitVec 16) := 0x812E#16

def PMU_EVENT_SAMPLE_FEED_LAT : (BitVec 16) := 0x812F#16

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def SecurityState_of_num (arg_ : Nat) : SecurityState :=
  match arg_ with
  | 0 => SS_NonSecure
  | 1 => SS_Root
  | 2 => SS_Realm
  | _ => SS_Secure

def num_of_SecurityState (arg_ : SecurityState) : Int :=
  match arg_ with
  | .SS_NonSecure => 0
  | .SS_Root => 1
  | .SS_Realm => 2
  | .SS_Secure => 3

def undefined_ProcState (_ : Unit) : SailM ProcState := do
  (pure { N := ← (do (undefined_bitvector 1))
          Z := ← (do (undefined_bitvector 1))
          C := ← (do (undefined_bitvector 1))
          V := ← (do (undefined_bitvector 1))
          D := ← (do (undefined_bitvector 1))
          A := ← (do (undefined_bitvector 1))
          I := ← (do (undefined_bitvector 1))
          F := ← (do (undefined_bitvector 1))
          EXLOCK := ← (do (undefined_bitvector 1))
          PAN := ← (do (undefined_bitvector 1))
          UAO := ← (do (undefined_bitvector 1))
          DIT := ← (do (undefined_bitvector 1))
          TCO := ← (do (undefined_bitvector 1))
          PM := ← (do (undefined_bitvector 1))
          PPEND := ← (do (undefined_bitvector 1))
          BTYPE := ← (do (undefined_bitvector 2))
          ZA := ← (do (undefined_bitvector 1))
          SM := ← (do (undefined_bitvector 1))
          ALLINT := ← (do (undefined_bitvector 1))
          SS := ← (do (undefined_bitvector 1))
          IL := ← (do (undefined_bitvector 1))
          EL := ← (do (undefined_bitvector 2))
          nRW := ← (do (undefined_bitvector 1))
          SP := ← (do (undefined_bitvector 1))
          Q := ← (do (undefined_bitvector 1))
          GE := ← (do (undefined_bitvector 4))
          SSBS := ← (do (undefined_bitvector 1))
          IT := ← (do (undefined_bitvector 8))
          J := ← (do (undefined_bitvector 1))
          T := ← (do (undefined_bitvector 1))
          E := ← (do (undefined_bitvector 1))
          M := ← (do (undefined_bitvector 5)) })

def undefined_PrivilegeLevel (_ : Unit) : SailM PrivilegeLevel := do
  (internal_pick [PL3, PL2, PL1, PL0])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def PrivilegeLevel_of_num (arg_ : Nat) : PrivilegeLevel :=
  match arg_ with
  | 0 => PL3
  | 1 => PL2
  | 2 => PL1
  | _ => PL0

def num_of_PrivilegeLevel (arg_ : PrivilegeLevel) : Int :=
  match arg_ with
  | .PL3 => 0
  | .PL2 => 1
  | .PL1 => 2
  | .PL0 => 3

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def InstrSet_of_num (arg_ : Nat) : InstrSet :=
  match arg_ with
  | 0 => InstrSet_A64
  | 1 => InstrSet_A32
  | _ => InstrSet_T32

def num_of_InstrSet (arg_ : InstrSet) : Int :=
  match arg_ with
  | .InstrSet_A64 => 0
  | .InstrSet_A32 => 1
  | .InstrSet_T32 => 2

def undefined_DSBAlias (_ : Unit) : SailM DSBAlias := do
  (internal_pick [DSBAlias_SSBB, DSBAlias_PSSBB, DSBAlias_DSB])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def DSBAlias_of_num (arg_ : Nat) : DSBAlias :=
  match arg_ with
  | 0 => DSBAlias_SSBB
  | 1 => DSBAlias_PSSBB
  | _ => DSBAlias_DSB

def num_of_DSBAlias (arg_ : DSBAlias) : Int :=
  match arg_ with
  | .DSBAlias_SSBB => 0
  | .DSBAlias_PSSBB => 1
  | .DSBAlias_DSB => 2

def undefined_WFxType (_ : Unit) : SailM WFxType := do
  (internal_pick [WFxType_WFE, WFxType_WFI, WFxType_WFET, WFxType_WFIT])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def WFxType_of_num (arg_ : Nat) : WFxType :=
  match arg_ with
  | 0 => WFxType_WFE
  | 1 => WFxType_WFI
  | 2 => WFxType_WFET
  | _ => WFxType_WFIT

def num_of_WFxType (arg_ : WFxType) : Int :=
  match arg_ with
  | .WFxType_WFE => 0
  | .WFxType_WFI => 1
  | .WFxType_WFET => 2
  | .WFxType_WFIT => 3

def undefined_ExceptionalOccurrenceTargetState (_ : Unit) : SailM ExceptionalOccurrenceTargetState := do
  (internal_pick [AArch32_NonDebugState, AArch64_NonDebugState, DebugState])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def ExceptionalOccurrenceTargetState_of_num (arg_ : Nat) : ExceptionalOccurrenceTargetState :=
  match arg_ with
  | 0 => AArch32_NonDebugState
  | 1 => AArch64_NonDebugState
  | _ => DebugState

def num_of_ExceptionalOccurrenceTargetState (arg_ : ExceptionalOccurrenceTargetState) : Int :=
  match arg_ with
  | .AArch32_NonDebugState => 0
  | .AArch64_NonDebugState => 1
  | .DebugState => 2

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def PARTIDspaceType_of_num (arg_ : Nat) : PARTIDspaceType :=
  match arg_ with
  | 0 => PIdSpace_Secure
  | 1 => PIdSpace_Root
  | 2 => PIdSpace_Realm
  | _ => PIdSpace_NonSecure

def num_of_PARTIDspaceType (arg_ : PARTIDspaceType) : Int :=
  match arg_ with
  | .PIdSpace_Secure => 0
  | .PIdSpace_Root => 1
  | .PIdSpace_Realm => 2
  | .PIdSpace_NonSecure => 3

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 13 -/
def AccessType_of_num (arg_ : Nat) : AccessType :=
  match arg_ with
  | 0 => AccessType_IFETCH
  | 1 => AccessType_GPR
  | 2 => AccessType_ASIMD
  | 3 => AccessType_SVE
  | 4 => AccessType_SME
  | 5 => AccessType_IC
  | 6 => AccessType_DC
  | 7 => AccessType_DCZero
  | 8 => AccessType_AT
  | 9 => AccessType_NV2
  | 10 => AccessType_SPE
  | 11 => AccessType_GCS
  | 12 => AccessType_GPTW
  | _ => AccessType_TTW

def num_of_AccessType (arg_ : AccessType) : Int :=
  match arg_ with
  | .AccessType_IFETCH => 0
  | .AccessType_GPR => 1
  | .AccessType_ASIMD => 2
  | .AccessType_SVE => 3
  | .AccessType_SME => 4
  | .AccessType_IC => 5
  | .AccessType_DC => 6
  | .AccessType_DCZero => 7
  | .AccessType_AT => 8
  | .AccessType_NV2 => 9
  | .AccessType_SPE => 10
  | .AccessType_GCS => 11
  | .AccessType_GPTW => 12
  | .AccessType_TTW => 13

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def MemOp_of_num (arg_ : Nat) : MemOp :=
  match arg_ with
  | 0 => MemOp_LOAD
  | 1 => MemOp_STORE
  | _ => MemOp_PREFETCH

def num_of_MemOp (arg_ : MemOp) : Int :=
  match arg_ with
  | .MemOp_LOAD => 0
  | .MemOp_STORE => 1
  | .MemOp_PREFETCH => 2

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def VARange_of_num (arg_ : Nat) : VARange :=
  match arg_ with
  | 0 => VARange_LOWER
  | _ => VARange_UPPER

def num_of_VARange (arg_ : VARange) : Int :=
  match arg_ with
  | .VARange_LOWER => 0
  | .VARange_UPPER => 1

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 10 -/
def MemAtomicOp_of_num (arg_ : Nat) : MemAtomicOp :=
  match arg_ with
  | 0 => MemAtomicOp_GCSSS1
  | 1 => MemAtomicOp_ADD
  | 2 => MemAtomicOp_BIC
  | 3 => MemAtomicOp_EOR
  | 4 => MemAtomicOp_ORR
  | 5 => MemAtomicOp_SMAX
  | 6 => MemAtomicOp_SMIN
  | 7 => MemAtomicOp_UMAX
  | 8 => MemAtomicOp_UMIN
  | 9 => MemAtomicOp_SWP
  | _ => MemAtomicOp_CAS

def num_of_MemAtomicOp (arg_ : MemAtomicOp) : Int :=
  match arg_ with
  | .MemAtomicOp_GCSSS1 => 0
  | .MemAtomicOp_ADD => 1
  | .MemAtomicOp_BIC => 2
  | .MemAtomicOp_EOR => 3
  | .MemAtomicOp_ORR => 4
  | .MemAtomicOp_SMAX => 5
  | .MemAtomicOp_SMIN => 6
  | .MemAtomicOp_UMAX => 7
  | .MemAtomicOp_UMIN => 8
  | .MemAtomicOp_SWP => 9
  | .MemAtomicOp_CAS => 10

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def CacheOp_of_num (arg_ : Nat) : CacheOp :=
  match arg_ with
  | 0 => CacheOp_Clean
  | 1 => CacheOp_Invalidate
  | _ => CacheOp_CleanInvalidate

def num_of_CacheOp (arg_ : CacheOp) : Int :=
  match arg_ with
  | .CacheOp_Clean => 0
  | .CacheOp_Invalidate => 1
  | .CacheOp_CleanInvalidate => 2

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 8 -/
def CacheOpScope_of_num (arg_ : Nat) : CacheOpScope :=
  match arg_ with
  | 0 => CacheOpScope_SetWay
  | 1 => CacheOpScope_PoU
  | 2 => CacheOpScope_PoC
  | 3 => CacheOpScope_PoE
  | 4 => CacheOpScope_PoP
  | 5 => CacheOpScope_PoDP
  | 6 => CacheOpScope_PoPA
  | 7 => CacheOpScope_ALLU
  | _ => CacheOpScope_ALLUIS

def num_of_CacheOpScope (arg_ : CacheOpScope) : Int :=
  match arg_ with
  | .CacheOpScope_SetWay => 0
  | .CacheOpScope_PoU => 1
  | .CacheOpScope_PoC => 2
  | .CacheOpScope_PoE => 3
  | .CacheOpScope_PoP => 4
  | .CacheOpScope_PoDP => 5
  | .CacheOpScope_PoPA => 6
  | .CacheOpScope_ALLU => 7
  | .CacheOpScope_ALLUIS => 8

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def CacheType_of_num (arg_ : Nat) : CacheType :=
  match arg_ with
  | 0 => CacheType_Data
  | 1 => CacheType_Tag
  | 2 => CacheType_Data_Tag
  | _ => CacheType_Instruction

def num_of_CacheType (arg_ : CacheType) : Int :=
  match arg_ with
  | .CacheType_Data => 0
  | .CacheType_Tag => 1
  | .CacheType_Data_Tag => 2
  | .CacheType_Instruction => 3

def undefined_CachePASpace (_ : Unit) : SailM CachePASpace := do
  (internal_pick [CPAS_NonSecure, CPAS_Any, CPAS_RealmNonSecure, CPAS_Realm, CPAS_Root, CPAS_SecureNonSecure, CPAS_Secure])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def CachePASpace_of_num (arg_ : Nat) : CachePASpace :=
  match arg_ with
  | 0 => CPAS_NonSecure
  | 1 => CPAS_Any
  | 2 => CPAS_RealmNonSecure
  | 3 => CPAS_Realm
  | 4 => CPAS_Root
  | 5 => CPAS_SecureNonSecure
  | _ => CPAS_Secure

def num_of_CachePASpace (arg_ : CachePASpace) : Int :=
  match arg_ with
  | .CPAS_NonSecure => 0
  | .CPAS_Any => 1
  | .CPAS_RealmNonSecure => 2
  | .CPAS_Realm => 3
  | .CPAS_Root => 4
  | .CPAS_SecureNonSecure => 5
  | .CPAS_Secure => 6

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def MemType_of_num (arg_ : Nat) : MemType :=
  match arg_ with
  | 0 => MemType_Normal
  | _ => MemType_Device

def num_of_MemType (arg_ : MemType) : Int :=
  match arg_ with
  | .MemType_Normal => 0
  | .MemType_Device => 1

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def DeviceType_of_num (arg_ : Nat) : DeviceType :=
  match arg_ with
  | 0 => DeviceType_GRE
  | 1 => DeviceType_nGRE
  | 2 => DeviceType_nGnRE
  | _ => DeviceType_nGnRnE

def num_of_DeviceType (arg_ : DeviceType) : Int :=
  match arg_ with
  | .DeviceType_GRE => 0
  | .DeviceType_nGRE => 1
  | .DeviceType_nGnRE => 2
  | .DeviceType_nGnRnE => 3

def LOG2_TAG_GRANULE : Nat := 4

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Shareability_of_num (arg_ : Nat) : Shareability :=
  match arg_ with
  | 0 => Shareability_NSH
  | 1 => Shareability_ISH
  | _ => Shareability_OSH

def num_of_Shareability (arg_ : Shareability) : Int :=
  match arg_ with
  | .Shareability_NSH => 0
  | .Shareability_ISH => 1
  | .Shareability_OSH => 2

def __UNKNOWN_Shareability (_ : Unit) : SailM Shareability := do
  (undefined_Shareability ())

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def MemTagType_of_num (arg_ : Nat) : MemTagType :=
  match arg_ with
  | 0 => MemTag_Untagged
  | 1 => MemTag_AllocationTagged
  | _ => MemTag_CanonicallyTagged

def num_of_MemTagType (arg_ : MemTagType) : Int :=
  match arg_ with
  | .MemTag_Untagged => 0
  | .MemTag_AllocationTagged => 1
  | .MemTag_CanonicallyTagged => 2

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def PASpace_of_num (arg_ : Nat) : PASpace :=
  match arg_ with
  | 0 => PAS_NonSecure
  | 1 => PAS_Secure
  | 2 => PAS_Root
  | _ => PAS_Realm

def num_of_PASpace (arg_ : PASpace) : Int :=
  match arg_ with
  | .PAS_NonSecure => 0
  | .PAS_Secure => 1
  | .PAS_Root => 2
  | .PAS_Realm => 3

def __UNKNOWN_FullAddress (_ : Unit) : SailM FullAddress := do
  (undefined_FullAddress ())

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def GPCF_of_num (arg_ : Nat) : GPCF :=
  match arg_ with
  | 0 => GPCF_None
  | 1 => GPCF_AddressSize
  | 2 => GPCF_Walk
  | 3 => GPCF_EABT
  | _ => GPCF_Fail

def num_of_GPCF (arg_ : GPCF) : Int :=
  match arg_ with
  | .GPCF_None => 0
  | .GPCF_AddressSize => 1
  | .GPCF_Walk => 2
  | .GPCF_EABT => 3
  | .GPCF_Fail => 4

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 23 -/
def Fault_of_num (arg_ : Nat) : Fault :=
  match arg_ with
  | 0 => Fault_None
  | 1 => Fault_AccessFlag
  | 2 => Fault_Alignment
  | 3 => Fault_Background
  | 4 => Fault_Domain
  | 5 => Fault_Permission
  | 6 => Fault_Translation
  | 7 => Fault_AddressSize
  | 8 => Fault_SyncExternal
  | 9 => Fault_SyncExternalOnWalk
  | 10 => Fault_SyncParity
  | 11 => Fault_SyncParityOnWalk
  | 12 => Fault_GPCFOnWalk
  | 13 => Fault_GPCFOnOutput
  | 14 => Fault_AsyncParity
  | 15 => Fault_AsyncExternal
  | 16 => Fault_TagCheck
  | 17 => Fault_Debug
  | 18 => Fault_TLBConflict
  | 19 => Fault_BranchTarget
  | 20 => Fault_HWUpdateAccessFlag
  | 21 => Fault_Lockdown
  | 22 => Fault_Exclusive
  | _ => Fault_ICacheMaint

def num_of_Fault (arg_ : Fault) : Int :=
  match arg_ with
  | .Fault_None => 0
  | .Fault_AccessFlag => 1
  | .Fault_Alignment => 2
  | .Fault_Background => 3
  | .Fault_Domain => 4
  | .Fault_Permission => 5
  | .Fault_Translation => 6
  | .Fault_AddressSize => 7
  | .Fault_SyncExternal => 8
  | .Fault_SyncExternalOnWalk => 9
  | .Fault_SyncParity => 10
  | .Fault_SyncParityOnWalk => 11
  | .Fault_GPCFOnWalk => 12
  | .Fault_GPCFOnOutput => 13
  | .Fault_AsyncParity => 14
  | .Fault_AsyncExternal => 15
  | .Fault_TagCheck => 16
  | .Fault_Debug => 17
  | .Fault_TLBConflict => 18
  | .Fault_BranchTarget => 19
  | .Fault_HWUpdateAccessFlag => 20
  | .Fault_Lockdown => 21
  | .Fault_Exclusive => 22
  | .Fault_ICacheMaint => 23

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def ErrorState_of_num (arg_ : Nat) : ErrorState :=
  match arg_ with
  | 0 => ErrorState_UC
  | 1 => ErrorState_UEU
  | 2 => ErrorState_UEO
  | 3 => ErrorState_UER
  | 4 => ErrorState_CE
  | 5 => ErrorState_Uncategorized
  | _ => ErrorState_IMPDEF

def num_of_ErrorState (arg_ : ErrorState) : Int :=
  match arg_ with
  | .ErrorState_UC => 0
  | .ErrorState_UEU => 1
  | .ErrorState_UEO => 2
  | .ErrorState_UER => 3
  | .ErrorState_CE => 4
  | .ErrorState_Uncategorized => 5
  | .ErrorState_IMPDEF => 6

def __UNKNOWN_PhysMemRetStatus (_ : Unit) : SailM PhysMemRetStatus := do
  (undefined_PhysMemRetStatus ())

def undefined_MBReqDomain (_ : Unit) : SailM MBReqDomain := do
  (internal_pick [MBReqDomain_Nonshareable, MBReqDomain_InnerShareable, MBReqDomain_OuterShareable, MBReqDomain_FullSystem])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def MBReqDomain_of_num (arg_ : Nat) : MBReqDomain :=
  match arg_ with
  | 0 => MBReqDomain_Nonshareable
  | 1 => MBReqDomain_InnerShareable
  | 2 => MBReqDomain_OuterShareable
  | _ => MBReqDomain_FullSystem

def num_of_MBReqDomain (arg_ : MBReqDomain) : Int :=
  match arg_ with
  | .MBReqDomain_Nonshareable => 0
  | .MBReqDomain_InnerShareable => 1
  | .MBReqDomain_OuterShareable => 2
  | .MBReqDomain_FullSystem => 3

def undefined_MBReqTypes (_ : Unit) : SailM MBReqTypes := do
  (internal_pick [MBReqTypes_Reads, MBReqTypes_Writes, MBReqTypes_All])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def MBReqTypes_of_num (arg_ : Nat) : MBReqTypes :=
  match arg_ with
  | 0 => MBReqTypes_Reads
  | 1 => MBReqTypes_Writes
  | _ => MBReqTypes_All

def num_of_MBReqTypes (arg_ : MBReqTypes) : Int :=
  match arg_ with
  | .MBReqTypes_Reads => 0
  | .MBReqTypes_Writes => 1
  | .MBReqTypes_All => 2

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def PrefetchHint_of_num (arg_ : Nat) : PrefetchHint :=
  match arg_ with
  | 0 => Prefetch_READ
  | 1 => Prefetch_WRITE
  | _ => Prefetch_EXEC

def num_of_PrefetchHint (arg_ : PrefetchHint) : Int :=
  match arg_ with
  | .Prefetch_READ => 0
  | .Prefetch_WRITE => 1
  | .Prefetch_EXEC => 2

def undefined_Unpredictable (_ : Unit) : SailM Unpredictable := do
  (internal_pick [Unpredictable_VMSR, Unpredictable_WBOVERLAPLD, Unpredictable_WBOVERLAPST, Unpredictable_LDPOVERLAP, Unpredictable_BASEOVERLAP, Unpredictable_DATAOVERLAP, Unpredictable_DEVPAGE2, Unpredictable_INSTRDEVICE, Unpredictable_RESCPACR, Unpredictable_RESMAIR, Unpredictable_S1CTAGGED, Unpredictable_S2RESMEMATTR, Unpredictable_RESTEXCB, Unpredictable_RESPRRR, Unpredictable_RESDACR, Unpredictable_RESVTCRS, Unpredictable_RESTnSZ, Unpredictable_RESTCF, Unpredictable_DEVICETAGSTORE, Unpredictable_OORTnSZ, Unpredictable_LARGEIPA, Unpredictable_ESRCONDPASS, Unpredictable_ILZEROIT, Unpredictable_ILZEROT, Unpredictable_BPVECTORCATCHPRI, Unpredictable_VCMATCHHALF, Unpredictable_VCMATCHDAPA, Unpredictable_WPMASKANDBAS, Unpredictable_WPBASCONTIGUOUS, Unpredictable_RESWPMASK, Unpredictable_WPMASKEDBITS, Unpredictable_RESBPWPCTRL, Unpredictable_BPNOTIMPL, Unpredictable_RESBPTYPE, Unpredictable_RESMDSELR, Unpredictable_BPNOTCTXCMP, Unpredictable_BPMATCHHALF, Unpredictable_BPMISMATCHHALF, Unpredictable_BPLINKINGDISABLED, Unpredictable_RESBPMASK, Unpredictable_BPMASK, Unpredictable_BPMASKEDBITS, Unpredictable_BPLINKEDADDRMATCH, Unpredictable_RESTARTALIGNPC, Unpredictable_RESTARTZEROUPPERPC, Unpredictable_ZEROUPPER, Unpredictable_ERETZEROUPPERPC, Unpredictable_A32FORCEALIGNPC, Unpredictable_SMD, Unpredictable_NONFAULT, Unpredictable_SVEZEROUPPER, Unpredictable_SVELDNFDATA, Unpredictable_SVELDNFZERO, Unpredictable_CHECKSPNONEACTIVE, Unpredictable_SMEZEROUPPER, Unpredictable_NVNV1, Unpredictable_Shareability, Unpredictable_AFUPDATE, Unpredictable_DBUPDATE, Unpredictable_IESBinDebug, Unpredictable_BADPMSFCR, Unpredictable_ZEROBTYPE, Unpredictable_EL2TIMESTAMP, Unpredictable_EL1TIMESTAMP, Unpredictable_RESERVEDNSxB, Unpredictable_WFxTDEBUG, Unpredictable_LS64UNSUPPORTED, Unpredictable_MISALIGNEDATOMIC, Unpredictable_CLEARERRITEZERO, Unpredictable_ALUEXCEPTIONRETURN, Unpredictable_IGNORETRAPINDEBUG, Unpredictable_DBGxVR_RESS, Unpredictable_PMUEVENTCOUNTER, Unpredictable_PMSCR_PCT, Unpredictable_CounterReservedForEL2, Unpredictable_BRBFILTRATE, Unpredictable_MOPSOVERLAP31, Unpredictable_STOREONLYTAGCHECKEDCAS, Unpredictable_RESTC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 78 -/
def Unpredictable_of_num (arg_ : Nat) : Unpredictable :=
  match arg_ with
  | 0 => Unpredictable_VMSR
  | 1 => Unpredictable_WBOVERLAPLD
  | 2 => Unpredictable_WBOVERLAPST
  | 3 => Unpredictable_LDPOVERLAP
  | 4 => Unpredictable_BASEOVERLAP
  | 5 => Unpredictable_DATAOVERLAP
  | 6 => Unpredictable_DEVPAGE2
  | 7 => Unpredictable_INSTRDEVICE
  | 8 => Unpredictable_RESCPACR
  | 9 => Unpredictable_RESMAIR
  | 10 => Unpredictable_S1CTAGGED
  | 11 => Unpredictable_S2RESMEMATTR
  | 12 => Unpredictable_RESTEXCB
  | 13 => Unpredictable_RESPRRR
  | 14 => Unpredictable_RESDACR
  | 15 => Unpredictable_RESVTCRS
  | 16 => Unpredictable_RESTnSZ
  | 17 => Unpredictable_RESTCF
  | 18 => Unpredictable_DEVICETAGSTORE
  | 19 => Unpredictable_OORTnSZ
  | 20 => Unpredictable_LARGEIPA
  | 21 => Unpredictable_ESRCONDPASS
  | 22 => Unpredictable_ILZEROIT
  | 23 => Unpredictable_ILZEROT
  | 24 => Unpredictable_BPVECTORCATCHPRI
  | 25 => Unpredictable_VCMATCHHALF
  | 26 => Unpredictable_VCMATCHDAPA
  | 27 => Unpredictable_WPMASKANDBAS
  | 28 => Unpredictable_WPBASCONTIGUOUS
  | 29 => Unpredictable_RESWPMASK
  | 30 => Unpredictable_WPMASKEDBITS
  | 31 => Unpredictable_RESBPWPCTRL
  | 32 => Unpredictable_BPNOTIMPL
  | 33 => Unpredictable_RESBPTYPE
  | 34 => Unpredictable_RESMDSELR
  | 35 => Unpredictable_BPNOTCTXCMP
  | 36 => Unpredictable_BPMATCHHALF
  | 37 => Unpredictable_BPMISMATCHHALF
  | 38 => Unpredictable_BPLINKINGDISABLED
  | 39 => Unpredictable_RESBPMASK
  | 40 => Unpredictable_BPMASK
  | 41 => Unpredictable_BPMASKEDBITS
  | 42 => Unpredictable_BPLINKEDADDRMATCH
  | 43 => Unpredictable_RESTARTALIGNPC
  | 44 => Unpredictable_RESTARTZEROUPPERPC
  | 45 => Unpredictable_ZEROUPPER
  | 46 => Unpredictable_ERETZEROUPPERPC
  | 47 => Unpredictable_A32FORCEALIGNPC
  | 48 => Unpredictable_SMD
  | 49 => Unpredictable_NONFAULT
  | 50 => Unpredictable_SVEZEROUPPER
  | 51 => Unpredictable_SVELDNFDATA
  | 52 => Unpredictable_SVELDNFZERO
  | 53 => Unpredictable_CHECKSPNONEACTIVE
  | 54 => Unpredictable_SMEZEROUPPER
  | 55 => Unpredictable_NVNV1
  | 56 => Unpredictable_Shareability
  | 57 => Unpredictable_AFUPDATE
  | 58 => Unpredictable_DBUPDATE
  | 59 => Unpredictable_IESBinDebug
  | 60 => Unpredictable_BADPMSFCR
  | 61 => Unpredictable_ZEROBTYPE
  | 62 => Unpredictable_EL2TIMESTAMP
  | 63 => Unpredictable_EL1TIMESTAMP
  | 64 => Unpredictable_RESERVEDNSxB
  | 65 => Unpredictable_WFxTDEBUG
  | 66 => Unpredictable_LS64UNSUPPORTED
  | 67 => Unpredictable_MISALIGNEDATOMIC
  | 68 => Unpredictable_CLEARERRITEZERO
  | 69 => Unpredictable_ALUEXCEPTIONRETURN
  | 70 => Unpredictable_IGNORETRAPINDEBUG
  | 71 => Unpredictable_DBGxVR_RESS
  | 72 => Unpredictable_PMUEVENTCOUNTER
  | 73 => Unpredictable_PMSCR_PCT
  | 74 => Unpredictable_CounterReservedForEL2
  | 75 => Unpredictable_BRBFILTRATE
  | 76 => Unpredictable_MOPSOVERLAP31
  | 77 => Unpredictable_STOREONLYTAGCHECKEDCAS
  | _ => Unpredictable_RESTC

def num_of_Unpredictable (arg_ : Unpredictable) : Int :=
  match arg_ with
  | .Unpredictable_VMSR => 0
  | .Unpredictable_WBOVERLAPLD => 1
  | .Unpredictable_WBOVERLAPST => 2
  | .Unpredictable_LDPOVERLAP => 3
  | .Unpredictable_BASEOVERLAP => 4
  | .Unpredictable_DATAOVERLAP => 5
  | .Unpredictable_DEVPAGE2 => 6
  | .Unpredictable_INSTRDEVICE => 7
  | .Unpredictable_RESCPACR => 8
  | .Unpredictable_RESMAIR => 9
  | .Unpredictable_S1CTAGGED => 10
  | .Unpredictable_S2RESMEMATTR => 11
  | .Unpredictable_RESTEXCB => 12
  | .Unpredictable_RESPRRR => 13
  | .Unpredictable_RESDACR => 14
  | .Unpredictable_RESVTCRS => 15
  | .Unpredictable_RESTnSZ => 16
  | .Unpredictable_RESTCF => 17
  | .Unpredictable_DEVICETAGSTORE => 18
  | .Unpredictable_OORTnSZ => 19
  | .Unpredictable_LARGEIPA => 20
  | .Unpredictable_ESRCONDPASS => 21
  | .Unpredictable_ILZEROIT => 22
  | .Unpredictable_ILZEROT => 23
  | .Unpredictable_BPVECTORCATCHPRI => 24
  | .Unpredictable_VCMATCHHALF => 25
  | .Unpredictable_VCMATCHDAPA => 26
  | .Unpredictable_WPMASKANDBAS => 27
  | .Unpredictable_WPBASCONTIGUOUS => 28
  | .Unpredictable_RESWPMASK => 29
  | .Unpredictable_WPMASKEDBITS => 30
  | .Unpredictable_RESBPWPCTRL => 31
  | .Unpredictable_BPNOTIMPL => 32
  | .Unpredictable_RESBPTYPE => 33
  | .Unpredictable_RESMDSELR => 34
  | .Unpredictable_BPNOTCTXCMP => 35
  | .Unpredictable_BPMATCHHALF => 36
  | .Unpredictable_BPMISMATCHHALF => 37
  | .Unpredictable_BPLINKINGDISABLED => 38
  | .Unpredictable_RESBPMASK => 39
  | .Unpredictable_BPMASK => 40
  | .Unpredictable_BPMASKEDBITS => 41
  | .Unpredictable_BPLINKEDADDRMATCH => 42
  | .Unpredictable_RESTARTALIGNPC => 43
  | .Unpredictable_RESTARTZEROUPPERPC => 44
  | .Unpredictable_ZEROUPPER => 45
  | .Unpredictable_ERETZEROUPPERPC => 46
  | .Unpredictable_A32FORCEALIGNPC => 47
  | .Unpredictable_SMD => 48
  | .Unpredictable_NONFAULT => 49
  | .Unpredictable_SVEZEROUPPER => 50
  | .Unpredictable_SVELDNFDATA => 51
  | .Unpredictable_SVELDNFZERO => 52
  | .Unpredictable_CHECKSPNONEACTIVE => 53
  | .Unpredictable_SMEZEROUPPER => 54
  | .Unpredictable_NVNV1 => 55
  | .Unpredictable_Shareability => 56
  | .Unpredictable_AFUPDATE => 57
  | .Unpredictable_DBUPDATE => 58
  | .Unpredictable_IESBinDebug => 59
  | .Unpredictable_BADPMSFCR => 60
  | .Unpredictable_ZEROBTYPE => 61
  | .Unpredictable_EL2TIMESTAMP => 62
  | .Unpredictable_EL1TIMESTAMP => 63
  | .Unpredictable_RESERVEDNSxB => 64
  | .Unpredictable_WFxTDEBUG => 65
  | .Unpredictable_LS64UNSUPPORTED => 66
  | .Unpredictable_MISALIGNEDATOMIC => 67
  | .Unpredictable_CLEARERRITEZERO => 68
  | .Unpredictable_ALUEXCEPTIONRETURN => 69
  | .Unpredictable_IGNORETRAPINDEBUG => 70
  | .Unpredictable_DBGxVR_RESS => 71
  | .Unpredictable_PMUEVENTCOUNTER => 72
  | .Unpredictable_PMSCR_PCT => 73
  | .Unpredictable_CounterReservedForEL2 => 74
  | .Unpredictable_BRBFILTRATE => 75
  | .Unpredictable_MOPSOVERLAP31 => 76
  | .Unpredictable_STOREONLYTAGCHECKEDCAS => 77
  | .Unpredictable_RESTC => 78

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 28 -/
def Constraint_of_num (arg_ : Nat) : Constraint :=
  match arg_ with
  | 0 => Constraint_NONE
  | 1 => Constraint_UNKNOWN
  | 2 => Constraint_UNDEF
  | 3 => Constraint_UNDEFEL0
  | 4 => Constraint_NOP
  | 5 => Constraint_TRUE
  | 6 => Constraint_FALSE
  | 7 => Constraint_DISABLED
  | 8 => Constraint_UNCOND
  | 9 => Constraint_COND
  | 10 => Constraint_ADDITIONAL_DECODE
  | 11 => Constraint_WBSUPPRESS
  | 12 => Constraint_FAULT
  | 13 => Constraint_LIMITED_ATOMICITY
  | 14 => Constraint_NVNV1_00
  | 15 => Constraint_NVNV1_01
  | 16 => Constraint_NVNV1_11
  | 17 => Constraint_EL1TIMESTAMP
  | 18 => Constraint_EL2TIMESTAMP
  | 19 => Constraint_OSH
  | 20 => Constraint_ISH
  | 21 => Constraint_NSH
  | 22 => Constraint_NC
  | 23 => Constraint_WT
  | 24 => Constraint_WB
  | 25 => Constraint_FORCE
  | 26 => Constraint_FORCENOSLCHECK
  | 27 => Constraint_MAPTOALLOCATED
  | _ => Constraint_PMSCR_PCT_VIRT

def num_of_Constraint (arg_ : Constraint) : Int :=
  match arg_ with
  | .Constraint_NONE => 0
  | .Constraint_UNKNOWN => 1
  | .Constraint_UNDEF => 2
  | .Constraint_UNDEFEL0 => 3
  | .Constraint_NOP => 4
  | .Constraint_TRUE => 5
  | .Constraint_FALSE => 6
  | .Constraint_DISABLED => 7
  | .Constraint_UNCOND => 8
  | .Constraint_COND => 9
  | .Constraint_ADDITIONAL_DECODE => 10
  | .Constraint_WBSUPPRESS => 11
  | .Constraint_FAULT => 12
  | .Constraint_LIMITED_ATOMICITY => 13
  | .Constraint_NVNV1_00 => 14
  | .Constraint_NVNV1_01 => 15
  | .Constraint_NVNV1_11 => 16
  | .Constraint_EL1TIMESTAMP => 17
  | .Constraint_EL2TIMESTAMP => 18
  | .Constraint_OSH => 19
  | .Constraint_ISH => 20
  | .Constraint_NSH => 21
  | .Constraint_NC => 22
  | .Constraint_WT => 23
  | .Constraint_WB => 24
  | .Constraint_FORCE => 25
  | .Constraint_FORCENOSLCHECK => 26
  | .Constraint_MAPTOALLOCATED => 27
  | .Constraint_PMSCR_PCT_VIRT => 28

def undefined_RestrictType (_ : Unit) : SailM RestrictType := do
  (internal_pick [RestrictType_DataValue, RestrictType_ControlFlow, RestrictType_CachePrefetch, RestrictType_Other])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def RestrictType_of_num (arg_ : Nat) : RestrictType :=
  match arg_ with
  | 0 => RestrictType_DataValue
  | 1 => RestrictType_ControlFlow
  | 2 => RestrictType_CachePrefetch
  | _ => RestrictType_Other

def num_of_RestrictType (arg_ : RestrictType) : Int :=
  match arg_ with
  | .RestrictType_DataValue => 0
  | .RestrictType_ControlFlow => 1
  | .RestrictType_CachePrefetch => 2
  | .RestrictType_Other => 3

def undefined_FPExc (_ : Unit) : SailM FPExc := do
  (internal_pick [FPExc_InvalidOp, FPExc_DivideByZero, FPExc_Overflow, FPExc_Underflow, FPExc_Inexact, FPExc_InputDenorm])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def FPExc_of_num (arg_ : Nat) : FPExc :=
  match arg_ with
  | 0 => FPExc_InvalidOp
  | 1 => FPExc_DivideByZero
  | 2 => FPExc_Overflow
  | 3 => FPExc_Underflow
  | 4 => FPExc_Inexact
  | _ => FPExc_InputDenorm

def num_of_FPExc (arg_ : FPExc) : Int :=
  match arg_ with
  | .FPExc_InvalidOp => 0
  | .FPExc_DivideByZero => 1
  | .FPExc_Overflow => 2
  | .FPExc_Underflow => 3
  | .FPExc_Inexact => 4
  | .FPExc_InputDenorm => 5

def undefined_FPRounding (_ : Unit) : SailM FPRounding := do
  (internal_pick [FPRounding_TIEEVEN, FPRounding_POSINF, FPRounding_NEGINF, FPRounding_ZERO, FPRounding_TIEAWAY, FPRounding_ODD])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def FPRounding_of_num (arg_ : Nat) : FPRounding :=
  match arg_ with
  | 0 => FPRounding_TIEEVEN
  | 1 => FPRounding_POSINF
  | 2 => FPRounding_NEGINF
  | 3 => FPRounding_ZERO
  | 4 => FPRounding_TIEAWAY
  | _ => FPRounding_ODD

def num_of_FPRounding (arg_ : FPRounding) : Int :=
  match arg_ with
  | .FPRounding_TIEEVEN => 0
  | .FPRounding_POSINF => 1
  | .FPRounding_NEGINF => 2
  | .FPRounding_ZERO => 3
  | .FPRounding_TIEAWAY => 4
  | .FPRounding_ODD => 5

def undefined_FPType (_ : Unit) : SailM FPType := do
  (internal_pick [FPType_Zero, FPType_Denormal, FPType_Nonzero, FPType_Infinity, FPType_QNaN, FPType_SNaN])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def FPType_of_num (arg_ : Nat) : FPType :=
  match arg_ with
  | 0 => FPType_Zero
  | 1 => FPType_Denormal
  | 2 => FPType_Nonzero
  | 3 => FPType_Infinity
  | 4 => FPType_QNaN
  | _ => FPType_SNaN

def num_of_FPType (arg_ : FPType) : Int :=
  match arg_ with
  | .FPType_Zero => 0
  | .FPType_Denormal => 1
  | .FPType_Nonzero => 2
  | .FPType_Infinity => 3
  | .FPType_QNaN => 4
  | .FPType_SNaN => 5

/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 30 -/
def register_ref (n : Nat) : (RegisterRef (BitVec 64)) :=
  match n with
  | 0 => (.Reg R0)
  | 1 => (.Reg R1)
  | 2 => (.Reg R2)
  | 3 => (.Reg R3)
  | 4 => (.Reg R4)
  | 5 => (.Reg R5)
  | 6 => (.Reg R6)
  | 7 => (.Reg R7)
  | 8 => (.Reg R8)
  | 9 => (.Reg R9)
  | 10 => (.Reg R10)
  | 11 => (.Reg R11)
  | 12 => (.Reg R12)
  | 13 => (.Reg R13)
  | 14 => (.Reg R14)
  | 15 => (.Reg R15)
  | 16 => (.Reg R16)
  | 17 => (.Reg R17)
  | 18 => (.Reg R18)
  | 19 => (.Reg R19)
  | 20 => (.Reg R20)
  | 21 => (.Reg R21)
  | 22 => (.Reg R22)
  | 23 => (.Reg R23)
  | 24 => (.Reg R24)
  | 25 => (.Reg R25)
  | 26 => (.Reg R26)
  | 27 => (.Reg R27)
  | 28 => (.Reg R28)
  | 29 => (.Reg R29)
  | _ => (.Reg R30)

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 10 -/
def BranchType_of_num (arg_ : Nat) : BranchType :=
  match arg_ with
  | 0 => BranchType_DIRCALL
  | 1 => BranchType_INDCALL
  | 2 => BranchType_ERET
  | 3 => BranchType_DBGEXIT
  | 4 => BranchType_RET
  | 5 => BranchType_DIR
  | 6 => BranchType_INDIR
  | 7 => BranchType_EXCEPTION
  | 8 => BranchType_TMFAIL
  | 9 => BranchType_RESET
  | _ => BranchType_UNKNOWN

def num_of_BranchType (arg_ : BranchType) : Int :=
  match arg_ with
  | .BranchType_DIRCALL => 0
  | .BranchType_INDCALL => 1
  | .BranchType_ERET => 2
  | .BranchType_DBGEXIT => 3
  | .BranchType_RET => 4
  | .BranchType_DIR => 5
  | .BranchType_INDIR => 6
  | .BranchType_EXCEPTION => 7
  | .BranchType_TMFAIL => 8
  | .BranchType_RESET => 9
  | .BranchType_UNKNOWN => 10

def undefined_InterruptID (_ : Unit) : SailM InterruptID := do
  (internal_pick [InterruptID_PMUIRQ, InterruptID_COMMIRQ, InterruptID_CTIIRQ, InterruptID_COMMRX, InterruptID_COMMTX, InterruptID_CNTP, InterruptID_CNTHP, InterruptID_CNTHPS, InterruptID_CNTPS, InterruptID_CNTV, InterruptID_CNTHV, InterruptID_CNTHVS, InterruptID_PMBIRQ])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 12 -/
def InterruptID_of_num (arg_ : Nat) : InterruptID :=
  match arg_ with
  | 0 => InterruptID_PMUIRQ
  | 1 => InterruptID_COMMIRQ
  | 2 => InterruptID_CTIIRQ
  | 3 => InterruptID_COMMRX
  | 4 => InterruptID_COMMTX
  | 5 => InterruptID_CNTP
  | 6 => InterruptID_CNTHP
  | 7 => InterruptID_CNTHPS
  | 8 => InterruptID_CNTPS
  | 9 => InterruptID_CNTV
  | 10 => InterruptID_CNTHV
  | 11 => InterruptID_CNTHVS
  | _ => InterruptID_PMBIRQ

def num_of_InterruptID (arg_ : InterruptID) : Int :=
  match arg_ with
  | .InterruptID_PMUIRQ => 0
  | .InterruptID_COMMIRQ => 1
  | .InterruptID_CTIIRQ => 2
  | .InterruptID_COMMRX => 3
  | .InterruptID_COMMTX => 4
  | .InterruptID_CNTP => 5
  | .InterruptID_CNTHP => 6
  | .InterruptID_CNTHPS => 7
  | .InterruptID_CNTPS => 8
  | .InterruptID_CNTV => 9
  | .InterruptID_CNTHV => 10
  | .InterruptID_CNTHVS => 11
  | .InterruptID_PMBIRQ => 12

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 40 -/
def Exception_of_num (arg_ : Nat) : Exception :=
  match arg_ with
  | 0 => Exception_Uncategorized
  | 1 => Exception_WFxTrap
  | 2 => Exception_CP15RTTrap
  | 3 => Exception_CP15RRTTrap
  | 4 => Exception_CP14RTTrap
  | 5 => Exception_CP14DTTrap
  | 6 => Exception_CP14RRTTrap
  | 7 => Exception_AdvSIMDFPAccessTrap
  | 8 => Exception_FPIDTrap
  | 9 => Exception_LDST64BTrap
  | 10 => Exception_PACTrap
  | 11 => Exception_IllegalState
  | 12 => Exception_SupervisorCall
  | 13 => Exception_HypervisorCall
  | 14 => Exception_MonitorCall
  | 15 => Exception_SystemRegisterTrap
  | 16 => Exception_ERetTrap
  | 17 => Exception_InstructionAbort
  | 18 => Exception_PCAlignment
  | 19 => Exception_DataAbort
  | 20 => Exception_NV2DataAbort
  | 21 => Exception_PACFail
  | 22 => Exception_SPAlignment
  | 23 => Exception_FPTrappedException
  | 24 => Exception_SError
  | 25 => Exception_Breakpoint
  | 26 => Exception_SoftwareStep
  | 27 => Exception_Watchpoint
  | 28 => Exception_NV2Watchpoint
  | 29 => Exception_SoftwareBreakpoint
  | 30 => Exception_VectorCatch
  | 31 => Exception_IRQ
  | 32 => Exception_SVEAccessTrap
  | 33 => Exception_SMEAccessTrap
  | 34 => Exception_TSTARTAccessTrap
  | 35 => Exception_GPC
  | 36 => Exception_BranchTarget
  | 37 => Exception_MemCpyMemSet
  | 38 => Exception_GCSFail
  | 39 => Exception_SystemRegister128Trap
  | _ => Exception_FIQ

def num_of_Exception (arg_ : Exception) : Int :=
  match arg_ with
  | .Exception_Uncategorized => 0
  | .Exception_WFxTrap => 1
  | .Exception_CP15RTTrap => 2
  | .Exception_CP15RRTTrap => 3
  | .Exception_CP14RTTrap => 4
  | .Exception_CP14DTTrap => 5
  | .Exception_CP14RRTTrap => 6
  | .Exception_AdvSIMDFPAccessTrap => 7
  | .Exception_FPIDTrap => 8
  | .Exception_LDST64BTrap => 9
  | .Exception_PACTrap => 10
  | .Exception_IllegalState => 11
  | .Exception_SupervisorCall => 12
  | .Exception_HypervisorCall => 13
  | .Exception_MonitorCall => 14
  | .Exception_SystemRegisterTrap => 15
  | .Exception_ERetTrap => 16
  | .Exception_InstructionAbort => 17
  | .Exception_PCAlignment => 18
  | .Exception_DataAbort => 19
  | .Exception_NV2DataAbort => 20
  | .Exception_PACFail => 21
  | .Exception_SPAlignment => 22
  | .Exception_FPTrappedException => 23
  | .Exception_SError => 24
  | .Exception_Breakpoint => 25
  | .Exception_SoftwareStep => 26
  | .Exception_Watchpoint => 27
  | .Exception_NV2Watchpoint => 28
  | .Exception_SoftwareBreakpoint => 29
  | .Exception_VectorCatch => 30
  | .Exception_IRQ => 31
  | .Exception_SVEAccessTrap => 32
  | .Exception_SMEAccessTrap => 33
  | .Exception_TSTARTAccessTrap => 34
  | .Exception_GPC => 35
  | .Exception_BranchTarget => 36
  | .Exception_MemCpyMemSet => 37
  | .Exception_GCSFail => 38
  | .Exception_SystemRegister128Trap => 39
  | .Exception_FIQ => 40

def undefined_TranslationStage (_ : Unit) : SailM TranslationStage := do
  (internal_pick [TranslationStage_1, TranslationStage_12])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def TranslationStage_of_num (arg_ : Nat) : TranslationStage :=
  match arg_ with
  | 0 => TranslationStage_1
  | _ => TranslationStage_12

def num_of_TranslationStage (arg_ : TranslationStage) : Int :=
  match arg_ with
  | .TranslationStage_1 => 0
  | .TranslationStage_12 => 1

def undefined_ATAccess (_ : Unit) : SailM ATAccess := do
  (internal_pick [ATAccess_Read, ATAccess_Write, ATAccess_ReadPAN, ATAccess_WritePAN])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def ATAccess_of_num (arg_ : Nat) : ATAccess :=
  match arg_ with
  | 0 => ATAccess_Read
  | 1 => ATAccess_Write
  | 2 => ATAccess_ReadPAN
  | _ => ATAccess_WritePAN

def num_of_ATAccess (arg_ : ATAccess) : Int :=
  match arg_ with
  | .ATAccess_Read => 0
  | .ATAccess_Write => 1
  | .ATAccess_ReadPAN => 2
  | .ATAccess_WritePAN => 3

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def Regime_of_num (arg_ : Nat) : Regime :=
  match arg_ with
  | 0 => Regime_EL3
  | 1 => Regime_EL30
  | 2 => Regime_EL2
  | 3 => Regime_EL20
  | _ => Regime_EL10

def num_of_Regime (arg_ : Regime) : Int :=
  match arg_ with
  | .Regime_EL3 => 0
  | .Regime_EL30 => 1
  | .Regime_EL2 => 2
  | .Regime_EL20 => 3
  | .Regime_EL10 => 4

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def TGx_of_num (arg_ : Nat) : TGx :=
  match arg_ with
  | 0 => TGx_4KB
  | 1 => TGx_16KB
  | _ => TGx_64KB

def num_of_TGx (arg_ : TGx) : Int :=
  match arg_ with
  | .TGx_4KB => 0
  | .TGx_16KB => 1
  | .TGx_64KB => 2

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def DescriptorType_of_num (arg_ : Nat) : DescriptorType :=
  match arg_ with
  | 0 => DescriptorType_Table
  | 1 => DescriptorType_Leaf
  | _ => DescriptorType_Invalid

def num_of_DescriptorType (arg_ : DescriptorType) : Int :=
  match arg_ with
  | .DescriptorType_Table => 0
  | .DescriptorType_Leaf => 1
  | .DescriptorType_Invalid => 2

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def SDFType_of_num (arg_ : Nat) : SDFType :=
  match arg_ with
  | 0 => SDFType_Table
  | 1 => SDFType_Invalid
  | 2 => SDFType_Supersection
  | 3 => SDFType_Section
  | 4 => SDFType_LargePage
  | _ => SDFType_SmallPage

def num_of_SDFType (arg_ : SDFType) : Int :=
  match arg_ with
  | .SDFType_Table => 0
  | .SDFType_Invalid => 1
  | .SDFType_Supersection => 2
  | .SDFType_Section => 3
  | .SDFType_LargePage => 4
  | .SDFType_SmallPage => 5

def undefined_TranslationStartInfo (_ : Unit) : SailM TranslationStartInfo := do
  (pure { ss := ← (do (undefined_SecurityState ()))
          regime := ← (do (undefined_Regime ()))
          vmid := ← (do (undefined_bitvector 16))
          asid := ← (do (undefined_bitvector 16))
          va := ← (do (undefined_bitvector 64))
          cnp := ← (do (undefined_bitvector 1))
          accdesc := ← (do (undefined_AccessDescriptor ()))
          size := ← (do (undefined_int ())) })

def undefined_SVECmp (_ : Unit) : SailM SVECmp := do
  (internal_pick [Cmp_EQ, Cmp_NE, Cmp_GE, Cmp_GT, Cmp_LT, Cmp_LE, Cmp_UN])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def SVECmp_of_num (arg_ : Nat) : SVECmp :=
  match arg_ with
  | 0 => Cmp_EQ
  | 1 => Cmp_NE
  | 2 => Cmp_GE
  | 3 => Cmp_GT
  | 4 => Cmp_LT
  | 5 => Cmp_LE
  | _ => Cmp_UN

def num_of_SVECmp (arg_ : SVECmp) : Int :=
  match arg_ with
  | .Cmp_EQ => 0
  | .Cmp_NE => 1
  | .Cmp_GE => 2
  | .Cmp_GT => 3
  | .Cmp_LT => 4
  | .Cmp_LE => 5
  | .Cmp_UN => 6

def ZT0_LEN : Nat := 512

def undefined_SMEExceptionType (_ : Unit) : SailM SMEExceptionType := do
  (internal_pick [SMEExceptionType_AccessTrap, SMEExceptionType_Streaming, SMEExceptionType_NotStreaming, SMEExceptionType_InactiveZA, SMEExceptionType_InaccessibleZT0])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def SMEExceptionType_of_num (arg_ : Nat) : SMEExceptionType :=
  match arg_ with
  | 0 => SMEExceptionType_AccessTrap
  | 1 => SMEExceptionType_Streaming
  | 2 => SMEExceptionType_NotStreaming
  | 3 => SMEExceptionType_InactiveZA
  | _ => SMEExceptionType_InaccessibleZT0

def num_of_SMEExceptionType (arg_ : SMEExceptionType) : Int :=
  match arg_ with
  | .SMEExceptionType_AccessTrap => 0
  | .SMEExceptionType_Streaming => 1
  | .SMEExceptionType_NotStreaming => 2
  | .SMEExceptionType_InactiveZA => 3
  | .SMEExceptionType_InaccessibleZT0 => 4

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 7 -/
def GCSInstruction_of_num (arg_ : Nat) : GCSInstruction :=
  match arg_ with
  | 0 => GCSInstType_PRET
  | 1 => GCSInstType_POPM
  | 2 => GCSInstType_PRETAA
  | 3 => GCSInstType_PRETAB
  | 4 => GCSInstType_SS1
  | 5 => GCSInstType_SS2
  | 6 => GCSInstType_POPCX
  | _ => GCSInstType_POPX

def num_of_GCSInstruction (arg_ : GCSInstruction) : Int :=
  match arg_ with
  | .GCSInstType_PRET => 0
  | .GCSInstType_POPM => 1
  | .GCSInstType_PRETAA => 2
  | .GCSInstType_PRETAB => 3
  | .GCSInstType_SS1 => 4
  | .GCSInstType_SS2 => 5
  | .GCSInstType_POPCX => 6
  | .GCSInstType_POPX => 7

def undefined_MOPSStage (_ : Unit) : SailM MOPSStage := do
  (internal_pick [MOPSStage_Prologue, MOPSStage_Main, MOPSStage_Epilogue])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def MOPSStage_of_num (arg_ : Nat) : MOPSStage :=
  match arg_ with
  | 0 => MOPSStage_Prologue
  | 1 => MOPSStage_Main
  | _ => MOPSStage_Epilogue

def num_of_MOPSStage (arg_ : MOPSStage) : Int :=
  match arg_ with
  | .MOPSStage_Prologue => 0
  | .MOPSStage_Main => 1
  | .MOPSStage_Epilogue => 2

def undefined_FPCR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_FPSR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _get_FPSR_Type_IDC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_FPSR_Type_IDC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_CTR_EL0_Type_IDC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_CTR_Type_IDC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_FPSCR_Type_IDC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_CTR_EL0_Type_IDC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_CTR_Type_IDC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_FPSCR_Type_IDC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_FPSR_Type_IXC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_FPSR_Type_IXC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_FPSCR_Type_IXC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_FPSCR_Type_IXC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_FPSR_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_FPSR_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_AMCFGR_EL0_Type_N (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_AMCFGR_Type_N (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_DSPSR_EL0_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_DSPSR_Type_N (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_FPSCR_Type_N (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMCFGR_Type_N (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_PMCR_EL0_Type_N (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 11 x)

def _update_PMCR_Type_N (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 11 x)

def _update_SPSR_EL1_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SPSR_EL2_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SPSR_EL3_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SPSR_abt_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SPSR_fiq_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SPSR_hyp_Type_N (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SPSR_irq_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SPSR_mon_Type_N (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SPSR_svc_Type_N (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_SPSR_und_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_TTBCR_Type_N (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _get_AMCFGR_EL0_Type_N (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_AMCFGR_Type_N (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_DSPSR_EL0_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_DSPSR_Type_N (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_FPSCR_Type_N (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMCFGR_Type_N (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_PMCR_Type_N (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 15 11)

def _get_SPSR_EL1_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_SPSR_EL2_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_SPSR_EL3_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_SPSR_abt_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_SPSR_fiq_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_SPSR_hyp_Type_N (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_SPSR_irq_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_SPSR_mon_Type_N (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_SPSR_svc_Type_N (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_SPSR_und_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_FPSR_Type_QC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_FPSR_Type_QC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_FPSCR_Type_QC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_FPSCR_Type_QC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_FPSR_Type_UFC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_FPSR_Type_UFC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_FPSCR_Type_UFC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_FPSCR_Type_UFC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_FPSR_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_FPSR_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_DSPSR_EL0_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_DSPSR_Type_V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_FPSCR_Type_V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_GICR_INVALLR_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_GICR_INVLPIR_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_SCTLR_Type_V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_SPSR_EL1_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_SPSR_EL2_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_SPSR_EL3_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_SPSR_abt_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_SPSR_fiq_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_SPSR_hyp_Type_V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_SPSR_irq_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_SPSR_mon_Type_V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_SPSR_svc_Type_V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_SPSR_und_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_DSPSR_EL0_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_DSPSR_Type_V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_FPSCR_Type_V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_GICR_INVALLR_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_GICR_INVLPIR_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_SPSR_EL1_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_SPSR_EL2_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_SPSR_EL3_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_SPSR_abt_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_SPSR_fiq_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_SPSR_hyp_Type_V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_SPSR_irq_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_SPSR_mon_Type_V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_SPSR_svc_Type_V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_SPSR_und_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_FPSR_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_FPSR_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_DSPSR_EL0_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_DSPSR_Type_Z (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_FPSCR_Type_Z (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_GICR_VPROPBASER_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _update_SPSR_EL1_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_SPSR_EL2_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_SPSR_EL3_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_SPSR_abt_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_SPSR_fiq_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_SPSR_hyp_Type_Z (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_SPSR_irq_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_SPSR_mon_Type_Z (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_SPSR_svc_Type_Z (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_SPSR_und_Type_Z (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_DSPSR_EL0_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_DSPSR_Type_Z (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_FPSCR_Type_Z (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_GICR_VPROPBASER_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)

def _get_SPSR_EL1_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_SPSR_EL2_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_SPSR_EL3_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_SPSR_abt_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_SPSR_fiq_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_SPSR_hyp_Type_Z (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_SPSR_irq_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_SPSR_mon_Type_Z (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_SPSR_svc_Type_Z (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_SPSR_und_Type_Z (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def undefined_ICC_PMR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _get_ICC_PMR_EL1_Type_Priority (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _update_ICC_PMR_EL1_Type_Priority (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_GICC_PMR_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_GICC_RPR_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_GICV_PMR_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_GICV_RPR_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_ICC_PMR_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_ICC_RPR_EL1_Type_Priority (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_ICC_RPR_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_ICH_LRC_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_ICH_LR_EL2_Type_Priority (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _update_ICV_PMR_EL1_Type_Priority (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_ICV_PMR_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_ICV_RPR_EL1_Type_Priority (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_ICV_RPR_Type_Priority (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_SMPRI_EL1_Type_Priority (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_GICC_PMR_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_GICC_RPR_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_GICV_PMR_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_GICV_RPR_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_ICC_PMR_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_ICC_RPR_EL1_Type_Priority (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_ICC_RPR_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_ICH_LRC_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def _get_ICH_LR_EL2_Type_Priority (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)

def _get_ICV_PMR_EL1_Type_Priority (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_ICV_PMR_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_ICV_RPR_EL1_Type_Priority (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_ICV_RPR_Type_Priority (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)

def _get_SMPRI_EL1_Type_Priority (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def undefined_TMState (_ : Unit) : SailM TMState := do
  (pure { depth := ← (do (undefined_int ()))
          Rt := ← (do (undefined_int ()))
          nPC := ← (do (undefined_bitvector 64))
          X := ← (do (undefined_vector 31 (← (undefined_bitvector 64))))
          Z := ← (do (undefined_vector 32 (← (undefined_bitvector 2048))))
          P := ← (do (undefined_vector 16 (← (undefined_bitvector 256))))
          FFR := ← (do (undefined_bitvector 256))
          SP := ← (do (undefined_bitvector 64))
          FPCR := ← (do (undefined_bitvector 64))
          FPSR := ← (do (undefined_bitvector 64))
          ICC_PMR_EL1 := ← (do (undefined_bitvector 64))
          GCSPR_ELx := ← (do (undefined_bitvector 64))
          nzcv := ← (do (undefined_bitvector 4))
          D := ← (do (undefined_bitvector 1))
          A := ← (do (undefined_bitvector 1))
          I := ← (do (undefined_bitvector 1))
          F := ← (do (undefined_bitvector 1)) })

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 7 -/
def TMFailure_of_num (arg_ : Nat) : TMFailure :=
  match arg_ with
  | 0 => TMFailure_CNCL
  | 1 => TMFailure_DBG
  | 2 => TMFailure_ERR
  | 3 => TMFailure_NEST
  | 4 => TMFailure_SIZE
  | 5 => TMFailure_MEM
  | 6 => TMFailure_TRIVIAL
  | _ => TMFailure_IMP

def num_of_TMFailure (arg_ : TMFailure) : Int :=
  match arg_ with
  | .TMFailure_CNCL => 0
  | .TMFailure_DBG => 1
  | .TMFailure_ERR => 2
  | .TMFailure_NEST => 3
  | .TMFailure_SIZE => 4
  | .TMFailure_MEM => 5
  | .TMFailure_TRIVIAL => 6
  | .TMFailure_IMP => 7

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def PGSe_of_num (arg_ : Nat) : PGSe :=
  match arg_ with
  | 0 => PGS_4KB
  | 1 => PGS_16KB
  | _ => PGS_64KB

def num_of_PGSe (arg_ : PGSe) : Int :=
  match arg_ with
  | .PGS_4KB => 0
  | .PGS_16KB => 1
  | .PGS_64KB => 2

def SPEMaxAddrs : Nat := 32

def SPEMaxRecordSize : Nat := 64

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def TimeStamp_of_num (arg_ : Nat) : TimeStamp :=
  match arg_ with
  | 0 => TimeStamp_None
  | 1 => TimeStamp_CoreSight
  | 2 => TimeStamp_Physical
  | 3 => TimeStamp_OffsetPhysical
  | _ => TimeStamp_Virtual

def num_of_TimeStamp (arg_ : TimeStamp) : Int :=
  match arg_ with
  | .TimeStamp_None => 0
  | .TimeStamp_CoreSight => 1
  | .TimeStamp_Physical => 2
  | .TimeStamp_OffsetPhysical => 3
  | .TimeStamp_Virtual => 4

def undefined_OpType (_ : Unit) : SailM OpType := do
  (internal_pick [OpType_Load, OpType_Store, OpType_LoadAtomic, OpType_Branch, OpType_Other])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def OpType_of_num (arg_ : Nat) : OpType :=
  match arg_ with
  | 0 => OpType_Load
  | 1 => OpType_Store
  | 2 => OpType_LoadAtomic
  | 3 => OpType_Branch
  | _ => OpType_Other

def num_of_OpType (arg_ : OpType) : Int :=
  match arg_ with
  | .OpType_Load => 0
  | .OpType_Store => 1
  | .OpType_LoadAtomic => 2
  | .OpType_Branch => 3
  | .OpType_Other => 4

def SPEAddrPosPCVirtual : Nat := 0

def SPECounterPosTotalLatency : Nat := 0

def SPECounterPosIssueLatency : Nat := 1

def undefined_CountOp (_ : Unit) : SailM CountOp := do
  (internal_pick [CountOp_CLZ, CountOp_CLS, CountOp_CNT])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def CountOp_of_num (arg_ : Nat) : CountOp :=
  match arg_ with
  | 0 => CountOp_CLZ
  | 1 => CountOp_CLS
  | _ => CountOp_CNT

def num_of_CountOp (arg_ : CountOp) : Int :=
  match arg_ with
  | .CountOp_CLZ => 0
  | .CountOp_CLS => 1
  | .CountOp_CNT => 2

def undefined_ExtendType (_ : Unit) : SailM ExtendType := do
  (internal_pick [ExtendType_SXTB, ExtendType_SXTH, ExtendType_SXTW, ExtendType_SXTX, ExtendType_UXTB, ExtendType_UXTH, ExtendType_UXTW, ExtendType_UXTX])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 7 -/
def ExtendType_of_num (arg_ : Nat) : ExtendType :=
  match arg_ with
  | 0 => ExtendType_SXTB
  | 1 => ExtendType_SXTH
  | 2 => ExtendType_SXTW
  | 3 => ExtendType_SXTX
  | 4 => ExtendType_UXTB
  | 5 => ExtendType_UXTH
  | 6 => ExtendType_UXTW
  | _ => ExtendType_UXTX

def num_of_ExtendType (arg_ : ExtendType) : Int :=
  match arg_ with
  | .ExtendType_SXTB => 0
  | .ExtendType_SXTH => 1
  | .ExtendType_SXTW => 2
  | .ExtendType_SXTX => 3
  | .ExtendType_UXTB => 4
  | .ExtendType_UXTH => 5
  | .ExtendType_UXTW => 6
  | .ExtendType_UXTX => 7

def undefined_FPMaxMinOp (_ : Unit) : SailM FPMaxMinOp := do
  (internal_pick [FPMaxMinOp_MAX, FPMaxMinOp_MIN, FPMaxMinOp_MAXNUM, FPMaxMinOp_MINNUM])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def FPMaxMinOp_of_num (arg_ : Nat) : FPMaxMinOp :=
  match arg_ with
  | 0 => FPMaxMinOp_MAX
  | 1 => FPMaxMinOp_MIN
  | 2 => FPMaxMinOp_MAXNUM
  | _ => FPMaxMinOp_MINNUM

def num_of_FPMaxMinOp (arg_ : FPMaxMinOp) : Int :=
  match arg_ with
  | .FPMaxMinOp_MAX => 0
  | .FPMaxMinOp_MIN => 1
  | .FPMaxMinOp_MAXNUM => 2
  | .FPMaxMinOp_MINNUM => 3

def undefined_FPUnaryOp (_ : Unit) : SailM FPUnaryOp := do
  (internal_pick [FPUnaryOp_ABS, FPUnaryOp_MOV, FPUnaryOp_NEG, FPUnaryOp_SQRT])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def FPUnaryOp_of_num (arg_ : Nat) : FPUnaryOp :=
  match arg_ with
  | 0 => FPUnaryOp_ABS
  | 1 => FPUnaryOp_MOV
  | 2 => FPUnaryOp_NEG
  | _ => FPUnaryOp_SQRT

def num_of_FPUnaryOp (arg_ : FPUnaryOp) : Int :=
  match arg_ with
  | .FPUnaryOp_ABS => 0
  | .FPUnaryOp_MOV => 1
  | .FPUnaryOp_NEG => 2
  | .FPUnaryOp_SQRT => 3

def undefined_FPConvOp (_ : Unit) : SailM FPConvOp := do
  (internal_pick [FPConvOp_CVT_FtoI, FPConvOp_CVT_ItoF, FPConvOp_MOV_FtoI, FPConvOp_MOV_ItoF, FPConvOp_CVT_FtoI_JS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def FPConvOp_of_num (arg_ : Nat) : FPConvOp :=
  match arg_ with
  | 0 => FPConvOp_CVT_FtoI
  | 1 => FPConvOp_CVT_ItoF
  | 2 => FPConvOp_MOV_FtoI
  | 3 => FPConvOp_MOV_ItoF
  | _ => FPConvOp_CVT_FtoI_JS

def num_of_FPConvOp (arg_ : FPConvOp) : Int :=
  match arg_ with
  | .FPConvOp_CVT_FtoI => 0
  | .FPConvOp_CVT_ItoF => 1
  | .FPConvOp_MOV_FtoI => 2
  | .FPConvOp_MOV_ItoF => 3
  | .FPConvOp_CVT_FtoI_JS => 4

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def MoveWideOp_of_num (arg_ : Nat) : MoveWideOp :=
  match arg_ with
  | 0 => MoveWideOp_N
  | 1 => MoveWideOp_Z
  | _ => MoveWideOp_K

def num_of_MoveWideOp (arg_ : MoveWideOp) : Int :=
  match arg_ with
  | .MoveWideOp_N => 0
  | .MoveWideOp_Z => 1
  | .MoveWideOp_K => 2

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def ShiftType_of_num (arg_ : Nat) : ShiftType :=
  match arg_ with
  | 0 => ShiftType_LSL
  | 1 => ShiftType_LSR
  | 2 => ShiftType_ASR
  | _ => ShiftType_ROR

def num_of_ShiftType (arg_ : ShiftType) : Int :=
  match arg_ with
  | .ShiftType_LSL => 0
  | .ShiftType_LSR => 1
  | .ShiftType_ASR => 2
  | .ShiftType_ROR => 3

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def LogicalOp_of_num (arg_ : Nat) : LogicalOp :=
  match arg_ with
  | 0 => LogicalOp_AND
  | 1 => LogicalOp_EOR
  | _ => LogicalOp_ORR

def num_of_LogicalOp (arg_ : LogicalOp) : Int :=
  match arg_ with
  | .LogicalOp_AND => 0
  | .LogicalOp_EOR => 1
  | .LogicalOp_ORR => 2

def undefined_SystemHintOp (_ : Unit) : SailM SystemHintOp := do
  (internal_pick [SystemHintOp_NOP, SystemHintOp_YIELD, SystemHintOp_WFE, SystemHintOp_WFI, SystemHintOp_SEV, SystemHintOp_SEVL, SystemHintOp_DGH, SystemHintOp_ESB, SystemHintOp_PSB, SystemHintOp_TSB, SystemHintOp_BTI, SystemHintOp_WFET, SystemHintOp_WFIT, SystemHintOp_CLRBHB, SystemHintOp_GCSB, SystemHintOp_CHKFEAT, SystemHintOp_CSDB])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 16 -/
def SystemHintOp_of_num (arg_ : Nat) : SystemHintOp :=
  match arg_ with
  | 0 => SystemHintOp_NOP
  | 1 => SystemHintOp_YIELD
  | 2 => SystemHintOp_WFE
  | 3 => SystemHintOp_WFI
  | 4 => SystemHintOp_SEV
  | 5 => SystemHintOp_SEVL
  | 6 => SystemHintOp_DGH
  | 7 => SystemHintOp_ESB
  | 8 => SystemHintOp_PSB
  | 9 => SystemHintOp_TSB
  | 10 => SystemHintOp_BTI
  | 11 => SystemHintOp_WFET
  | 12 => SystemHintOp_WFIT
  | 13 => SystemHintOp_CLRBHB
  | 14 => SystemHintOp_GCSB
  | 15 => SystemHintOp_CHKFEAT
  | _ => SystemHintOp_CSDB

def num_of_SystemHintOp (arg_ : SystemHintOp) : Int :=
  match arg_ with
  | .SystemHintOp_NOP => 0
  | .SystemHintOp_YIELD => 1
  | .SystemHintOp_WFE => 2
  | .SystemHintOp_WFI => 3
  | .SystemHintOp_SEV => 4
  | .SystemHintOp_SEVL => 5
  | .SystemHintOp_DGH => 6
  | .SystemHintOp_ESB => 7
  | .SystemHintOp_PSB => 8
  | .SystemHintOp_TSB => 9
  | .SystemHintOp_BTI => 10
  | .SystemHintOp_WFET => 11
  | .SystemHintOp_WFIT => 12
  | .SystemHintOp_CLRBHB => 13
  | .SystemHintOp_GCSB => 14
  | .SystemHintOp_CHKFEAT => 15
  | .SystemHintOp_CSDB => 16

def undefined_PSTATEField (_ : Unit) : SailM PSTATEField := do
  (internal_pick [PSTATEField_DAIFSet, PSTATEField_DAIFClr, PSTATEField_PAN, PSTATEField_UAO, PSTATEField_DIT, PSTATEField_SSBS, PSTATEField_TCO, PSTATEField_SVCRSM, PSTATEField_SVCRZA, PSTATEField_SVCRSMZA, PSTATEField_ALLINT, PSTATEField_PM, PSTATEField_SP])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 12 -/
def PSTATEField_of_num (arg_ : Nat) : PSTATEField :=
  match arg_ with
  | 0 => PSTATEField_DAIFSet
  | 1 => PSTATEField_DAIFClr
  | 2 => PSTATEField_PAN
  | 3 => PSTATEField_UAO
  | 4 => PSTATEField_DIT
  | 5 => PSTATEField_SSBS
  | 6 => PSTATEField_TCO
  | 7 => PSTATEField_SVCRSM
  | 8 => PSTATEField_SVCRZA
  | 9 => PSTATEField_SVCRSMZA
  | 10 => PSTATEField_ALLINT
  | 11 => PSTATEField_PM
  | _ => PSTATEField_SP

def num_of_PSTATEField (arg_ : PSTATEField) : Int :=
  match arg_ with
  | .PSTATEField_DAIFSet => 0
  | .PSTATEField_DAIFClr => 1
  | .PSTATEField_PAN => 2
  | .PSTATEField_UAO => 3
  | .PSTATEField_DIT => 4
  | .PSTATEField_SSBS => 5
  | .PSTATEField_TCO => 6
  | .PSTATEField_SVCRSM => 7
  | .PSTATEField_SVCRZA => 8
  | .PSTATEField_SVCRSMZA => 9
  | .PSTATEField_ALLINT => 10
  | .PSTATEField_PM => 11
  | .PSTATEField_SP => 12

def undefined_TLBILevel (_ : Unit) : SailM TLBILevel := do
  (internal_pick [TLBILevel_Any, TLBILevel_Last])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def TLBILevel_of_num (arg_ : Nat) : TLBILevel :=
  match arg_ with
  | 0 => TLBILevel_Any
  | _ => TLBILevel_Last

def num_of_TLBILevel (arg_ : TLBILevel) : Int :=
  match arg_ with
  | .TLBILevel_Any => 0
  | .TLBILevel_Last => 1

def undefined_TLBIOp (_ : Unit) : SailM TLBIOp := do
  (internal_pick [TLBIOp_DALL, TLBIOp_DASID, TLBIOp_DVA, TLBIOp_IALL, TLBIOp_IASID, TLBIOp_IVA, TLBIOp_ALL, TLBIOp_ASID, TLBIOp_IPAS2, TLBIPOp_IPAS2, TLBIOp_VAA, TLBIOp_VA, TLBIPOp_VAA, TLBIPOp_VA, TLBIOp_VMALL, TLBIOp_VMALLS12, TLBIOp_RIPAS2, TLBIPOp_RIPAS2, TLBIOp_RVAA, TLBIOp_RVA, TLBIPOp_RVAA, TLBIPOp_RVA, TLBIOp_RPA, TLBIOp_PAALL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 23 -/
def TLBIOp_of_num (arg_ : Nat) : TLBIOp :=
  match arg_ with
  | 0 => TLBIOp_DALL
  | 1 => TLBIOp_DASID
  | 2 => TLBIOp_DVA
  | 3 => TLBIOp_IALL
  | 4 => TLBIOp_IASID
  | 5 => TLBIOp_IVA
  | 6 => TLBIOp_ALL
  | 7 => TLBIOp_ASID
  | 8 => TLBIOp_IPAS2
  | 9 => TLBIPOp_IPAS2
  | 10 => TLBIOp_VAA
  | 11 => TLBIOp_VA
  | 12 => TLBIPOp_VAA
  | 13 => TLBIPOp_VA
  | 14 => TLBIOp_VMALL
  | 15 => TLBIOp_VMALLS12
  | 16 => TLBIOp_RIPAS2
  | 17 => TLBIPOp_RIPAS2
  | 18 => TLBIOp_RVAA
  | 19 => TLBIOp_RVA
  | 20 => TLBIPOp_RVAA
  | 21 => TLBIPOp_RVA
  | 22 => TLBIOp_RPA
  | _ => TLBIOp_PAALL

def num_of_TLBIOp (arg_ : TLBIOp) : Int :=
  match arg_ with
  | .TLBIOp_DALL => 0
  | .TLBIOp_DASID => 1
  | .TLBIOp_DVA => 2
  | .TLBIOp_IALL => 3
  | .TLBIOp_IASID => 4
  | .TLBIOp_IVA => 5
  | .TLBIOp_ALL => 6
  | .TLBIOp_ASID => 7
  | .TLBIOp_IPAS2 => 8
  | .TLBIPOp_IPAS2 => 9
  | .TLBIOp_VAA => 10
  | .TLBIOp_VA => 11
  | .TLBIPOp_VAA => 12
  | .TLBIPOp_VA => 13
  | .TLBIOp_VMALL => 14
  | .TLBIOp_VMALLS12 => 15
  | .TLBIOp_RIPAS2 => 16
  | .TLBIPOp_RIPAS2 => 17
  | .TLBIOp_RVAA => 18
  | .TLBIOp_RVA => 19
  | .TLBIPOp_RVAA => 20
  | .TLBIPOp_RVA => 21
  | .TLBIOp_RPA => 22
  | .TLBIOp_PAALL => 23

def undefined_TLBIMemAttr (_ : Unit) : SailM TLBIMemAttr := do
  (internal_pick [TLBI_AllAttr, TLBI_ExcludeXS])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def TLBIMemAttr_of_num (arg_ : Nat) : TLBIMemAttr :=
  match arg_ with
  | 0 => TLBI_AllAttr
  | _ => TLBI_ExcludeXS

def num_of_TLBIMemAttr (arg_ : TLBIMemAttr) : Int :=
  match arg_ with
  | .TLBI_AllAttr => 0
  | .TLBI_ExcludeXS => 1

def MAX_ZERO_BLOCK_SIZE : Nat := 2048

def undefined_VBitOp (_ : Unit) : SailM VBitOp := do
  (internal_pick [VBitOp_VBIF, VBitOp_VBIT, VBitOp_VBSL, VBitOp_VEOR])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def VBitOp_of_num (arg_ : Nat) : VBitOp :=
  match arg_ with
  | 0 => VBitOp_VBIF
  | 1 => VBitOp_VBIT
  | 2 => VBitOp_VBSL
  | _ => VBitOp_VEOR

def num_of_VBitOp (arg_ : VBitOp) : Int :=
  match arg_ with
  | .VBitOp_VBIF => 0
  | .VBitOp_VBIT => 1
  | .VBitOp_VBSL => 2
  | .VBitOp_VEOR => 3

def undefined_CompareOp (_ : Unit) : SailM CompareOp := do
  (internal_pick [CompareOp_GT, CompareOp_GE, CompareOp_EQ, CompareOp_LE, CompareOp_LT])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def CompareOp_of_num (arg_ : Nat) : CompareOp :=
  match arg_ with
  | 0 => CompareOp_GT
  | 1 => CompareOp_GE
  | 2 => CompareOp_EQ
  | 3 => CompareOp_LE
  | _ => CompareOp_LT

def num_of_CompareOp (arg_ : CompareOp) : Int :=
  match arg_ with
  | .CompareOp_GT => 0
  | .CompareOp_GE => 1
  | .CompareOp_EQ => 2
  | .CompareOp_LE => 3
  | .CompareOp_LT => 4

def undefined_ImmediateOp (_ : Unit) : SailM ImmediateOp := do
  (internal_pick [ImmediateOp_MOVI, ImmediateOp_MVNI, ImmediateOp_ORR, ImmediateOp_BIC])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def ImmediateOp_of_num (arg_ : Nat) : ImmediateOp :=
  match arg_ with
  | 0 => ImmediateOp_MOVI
  | 1 => ImmediateOp_MVNI
  | 2 => ImmediateOp_ORR
  | _ => ImmediateOp_BIC

def num_of_ImmediateOp (arg_ : ImmediateOp) : Int :=
  match arg_ with
  | .ImmediateOp_MOVI => 0
  | .ImmediateOp_MVNI => 1
  | .ImmediateOp_ORR => 2
  | .ImmediateOp_BIC => 3

def undefined_ReduceOp (_ : Unit) : SailM ReduceOp := do
  (internal_pick [ReduceOp_FMINNUM, ReduceOp_FMAXNUM, ReduceOp_FMIN, ReduceOp_FMAX, ReduceOp_FADD, ReduceOp_ADD])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def ReduceOp_of_num (arg_ : Nat) : ReduceOp :=
  match arg_ with
  | 0 => ReduceOp_FMINNUM
  | 1 => ReduceOp_FMAXNUM
  | 2 => ReduceOp_FMIN
  | 3 => ReduceOp_FMAX
  | 4 => ReduceOp_FADD
  | _ => ReduceOp_ADD

def num_of_ReduceOp (arg_ : ReduceOp) : Int :=
  match arg_ with
  | .ReduceOp_FMINNUM => 0
  | .ReduceOp_FMAXNUM => 1
  | .ReduceOp_FMIN => 2
  | .ReduceOp_FMAX => 3
  | .ReduceOp_FADD => 4
  | .ReduceOp_ADD => 5

def undefined_CrossTriggerIn (_ : Unit) : SailM CrossTriggerIn := do
  (internal_pick [CrossTriggerIn_CrossHalt, CrossTriggerIn_PMUOverflow, CrossTriggerIn_RSVD2, CrossTriggerIn_RSVD3, CrossTriggerIn_TraceExtOut0, CrossTriggerIn_TraceExtOut1, CrossTriggerIn_TraceExtOut2, CrossTriggerIn_TraceExtOut3])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 7 -/
def CrossTriggerIn_of_num (arg_ : Nat) : CrossTriggerIn :=
  match arg_ with
  | 0 => CrossTriggerIn_CrossHalt
  | 1 => CrossTriggerIn_PMUOverflow
  | 2 => CrossTriggerIn_RSVD2
  | 3 => CrossTriggerIn_RSVD3
  | 4 => CrossTriggerIn_TraceExtOut0
  | 5 => CrossTriggerIn_TraceExtOut1
  | 6 => CrossTriggerIn_TraceExtOut2
  | _ => CrossTriggerIn_TraceExtOut3

def num_of_CrossTriggerIn (arg_ : CrossTriggerIn) : Int :=
  match arg_ with
  | .CrossTriggerIn_CrossHalt => 0
  | .CrossTriggerIn_PMUOverflow => 1
  | .CrossTriggerIn_RSVD2 => 2
  | .CrossTriggerIn_RSVD3 => 3
  | .CrossTriggerIn_TraceExtOut0 => 4
  | .CrossTriggerIn_TraceExtOut1 => 5
  | .CrossTriggerIn_TraceExtOut2 => 6
  | .CrossTriggerIn_TraceExtOut3 => 7

def DebugHalt_OSUnlockCatch : (BitVec 6) := 0b100011#6

def DebugHalt_ResetCatch : (BitVec 6) := 0b100111#6

def DebugHalt_SoftwareAccess : (BitVec 6) := 0b110011#6

def RCW64_PROTECTED_BIT : Nat := 52

def RCW128_PROTECTED_BIT : Nat := 114

def undefined_InterruptReq (_ : Unit) : SailM InterruptReq := do
  (pure { take_SE := ← (do (undefined_bool ()))
          take_vSE := ← (do (undefined_bool ()))
          take_IRQ := ← (do (undefined_bool ()))
          take_vIRQ := ← (do (undefined_bool ()))
          take_FIQ := ← (do (undefined_bool ()))
          take_vFIQ := ← (do (undefined_bool ()))
          iesb_req := ← (do (undefined_bool ())) })

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def __InstrEnc_of_num (arg_ : Nat) : __InstrEnc :=
  match arg_ with
  | 0 => __A64
  | 1 => __A32
  | 2 => __T16
  | _ => __T32

def num_of___InstrEnc (arg_ : __InstrEnc) : Int :=
  match arg_ with
  | .__A64 => 0
  | .__A32 => 1
  | .__T16 => 2
  | .__T32 => 3

def lst_64bv : (BitVec 2) := 0b01#2

def lst_64b : (BitVec 2) := 0b10#2

def lst_64bv0 : (BitVec 2) := 0b11#2

def CFG_ID_AA64PFR0_EL1_EL0 : (BitVec 4) := 0b0010#4

def CFG_ID_AA64PFR0_EL1_EL1 : (BitVec 4) := 0b0001#4

def CFG_ID_AA64PFR0_EL1_EL2 : (BitVec 4) := 0b0001#4

def CFG_ID_AA64PFR0_EL1_EL3 : (BitVec 4) := 0b0001#4

def CFG_PMCR_IDCODE : (BitVec 8) := 0b00000000#8

def CFG_MPAM_none : (BitVec 4) := 0b0000#4

def CFG_MPAM_v0p1 : (BitVec 4) := 0b0000#4

def CFG_MPAM_v1p1 : (BitVec 4) := 0b0001#4

def CFG_MPAM_frac_none : (BitVec 4) := 0b0000#4

def CFG_MPAM_frac_v0p1 : (BitVec 4) := 0b0001#4

def CFG_MPAM_frac_v1p1 : (BitVec 4) := 0b0001#4

def undefined_SRType (_ : Unit) : SailM SRType := do
  (internal_pick [SRType_LSL, SRType_LSR, SRType_ASR, SRType_ROR, SRType_RRX])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def SRType_of_num (arg_ : Nat) : SRType :=
  match arg_ with
  | 0 => SRType_LSL
  | 1 => SRType_LSR
  | 2 => SRType_ASR
  | 3 => SRType_ROR
  | _ => SRType_RRX

def num_of_SRType (arg_ : SRType) : Int :=
  match arg_ with
  | .SRType_LSL => 0
  | .SRType_LSR => 1
  | .SRType_ASR => 2
  | .SRType_ROR => 3
  | .SRType_RRX => 4

def undefined_VCGEType (_ : Unit) : SailM VCGEType := do
  (internal_pick [VCGEType_signed, VCGEType_unsigned, VCGEType_fp])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def VCGEType_of_num (arg_ : Nat) : VCGEType :=
  match arg_ with
  | 0 => VCGEType_signed
  | 1 => VCGEType_unsigned
  | _ => VCGEType_fp

def num_of_VCGEType (arg_ : VCGEType) : Int :=
  match arg_ with
  | .VCGEType_signed => 0
  | .VCGEType_unsigned => 1
  | .VCGEType_fp => 2

def undefined_VFPNegMul (_ : Unit) : SailM VFPNegMul := do
  (internal_pick [VFPNegMul_VNMLA, VFPNegMul_VNMLS, VFPNegMul_VNMUL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def VFPNegMul_of_num (arg_ : Nat) : VFPNegMul :=
  match arg_ with
  | 0 => VFPNegMul_VNMLA
  | 1 => VFPNegMul_VNMLS
  | _ => VFPNegMul_VNMUL

def num_of_VFPNegMul (arg_ : VFPNegMul) : Int :=
  match arg_ with
  | .VFPNegMul_VNMLA => 0
  | .VFPNegMul_VNMLS => 1
  | .VFPNegMul_VNMUL => 2

def undefined_VCGTtype (_ : Unit) : SailM VCGTtype := do
  (internal_pick [VCGTtype_signed, VCGTtype_unsigned, VCGTtype_fp])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def VCGTtype_of_num (arg_ : Nat) : VCGTtype :=
  match arg_ with
  | 0 => VCGTtype_signed
  | 1 => VCGTtype_unsigned
  | _ => VCGTtype_fp

def num_of_VCGTtype (arg_ : VCGTtype) : Int :=
  match arg_ with
  | .VCGTtype_signed => 0
  | .VCGTtype_unsigned => 1
  | .VCGTtype_fp => 2

def undefined_VBitOps (_ : Unit) : SailM VBitOps := do
  (internal_pick [VBitOps_VBIF, VBitOps_VBIT, VBitOps_VBSL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def VBitOps_of_num (arg_ : Nat) : VBitOps :=
  match arg_ with
  | 0 => VBitOps_VBIF
  | 1 => VBitOps_VBIT
  | _ => VBitOps_VBSL

def num_of_VBitOps (arg_ : VBitOps) : Int :=
  match arg_ with
  | .VBitOps_VBIF => 0
  | .VBitOps_VBIT => 1
  | .VBitOps_VBSL => 2

def DebugException_BKPT : (BitVec 4) := 0b0011#4

def undefined_HCR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_HCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_HCR_EL2_Type_AMO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_HCR_Type_AMO (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_HCR_EL2_Type_AMVOFFEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)

def _update_SCR_EL3_Type_AMVOFFEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _update_HCR_EL2_Type_API (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _update_ID_AA64ISAR1_EL1_Type_API (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_SCR_EL3_Type_API (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_ID_AA64ISAR1_EL1_Type_API (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_HCR_EL2_Type_APK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _update_SCR_EL3_Type_APK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_HCR_EL2_Type_AT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_ID_AA64MMFR2_EL1_Type_AT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)

def _get_ID_AA64MMFR2_EL1_Type_AT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)

def _update_HCR_EL2_Type_ATA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _update_SCR_EL3_Type_ATA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_SCTLR_EL1_Type_ATA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _update_SCTLR_EL2_Type_ATA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _update_SCTLR_EL3_Type_ATA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _update_HCR_EL2_Type_BSU (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_HCR_Type_BSU (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _get_HCR_Type_BSU (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _update_HCR_EL2_Type_CD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_HCR2_Type_CD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_HCR_EL2_Type_DC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_HCR_Type_DC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_HCR_EL2_Type_DCT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _update_HCR_EL2_Type_E2H (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _update_HCR_EL2_Type_EnSCXT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _update_SCR_EL3_Type_EnSCXT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_HCR_EL2_Type_FB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_HCR_Type_FB (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_HCR_Type_FB (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_HCR_EL2_Type_FIEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 47 x)

def _update_SCR_EL3_Type_FIEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_HCR_EL2_Type_FMO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_HCR_Type_FMO (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_HCR_EL2_Type_FWB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _update_ID_AA64MMFR2_EL1_Type_FWB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 40 x)

def _get_ID_AA64MMFR2_EL1_Type_FWB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _update_HCR_EL2_Type_GPF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _update_SCR_EL3_Type_GPF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _update_HCR_EL2_Type_HCD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_HCR_Type_HCD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_HCR_Type_HCD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_HCR_EL2_Type_ID (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _update_HCR2_Type_ID (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_HCR_EL2_Type_IMO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_HCR_Type_IMO (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_HCR_EL2_Type_MIOCNCE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _update_HCR2_Type_MIOCNCE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_HCR2_Type_MIOCNCE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_HCR_EL2_Type_NV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _update_ID_AA64MMFR2_EL1_Type_NV (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_AA64MMFR2_EL1_Type_NV (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_HCR_EL2_Type_NV1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _update_HCR_EL2_Type_NV2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _update_HCR_EL2_Type_PTW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_HCR_Type_PTW (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_PAR_EL1_Type_PTW (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_PAR_EL1_Type_PTW (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_HCR_EL2_Type_SWIO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_HCR_Type_SWIO (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_HCR_Type_SWIO (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_HCR_EL2_Type_TACR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_HCR_EL2_Type_TDZ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_HCR_EL2_Type_TEA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _update_HCR2_Type_TEA (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_HCR_EL2_Type_TERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _update_HCR2_Type_TERR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_SCR_EL3_Type_TERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_SCR_Type_TERR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_HCR2_Type_TERR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_SCR_Type_TERR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_HCR_EL2_Type_TGE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_HCR_Type_TGE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_HCR_EL2_Type_TICAB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _update_HCR2_Type_TICAB (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_HCR2_Type_TICAB (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_HCR_EL2_Type_TID0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_HCR_Type_TID0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_HCR_Type_TID0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_HCR_EL2_Type_TID1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_HCR_Type_TID1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_HCR_Type_TID1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_HCR_EL2_Type_TID2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_HCR_Type_TID2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_HCR_Type_TID2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_HCR_EL2_Type_TID3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_HCR_Type_TID3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_HCR_Type_TID3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_HCR_EL2_Type_TID4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def _update_HCR2_Type_TID4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_HCR2_Type_TID4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_HCR_EL2_Type_TID5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _update_HCR_EL2_Type_TLOR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _update_SCR_EL3_Type_TLOR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_HCR_EL2_Type_TOCU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _update_HCR2_Type_TOCU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_HCR2_Type_TOCU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_HCR_EL2_Type_TPC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_HCR_Type_TPC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_HCR_Type_TPC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_HCR_EL2_Type_TPCP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_HCR_EL2_Type_TPU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_HCR_Type_TPU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_HCR_Type_TPU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_HCR_EL2_Type_TRVM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_HCR_Type_TRVM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_HCR_Type_TRVM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_HCR_EL2_Type_TSC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_HCR_Type_TSC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_HCR_Type_TSC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_HCR_EL2_Type_TSW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_HCR_Type_TSW (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_HCR_Type_TSW (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_HCR_EL2_Type_TTLB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_HCR_Type_TTLB (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_HCR_Type_TTLB (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_HCR_EL2_Type_TTLBIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _update_HCR2_Type_TTLBIS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_HCR2_Type_TTLBIS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_HCR_EL2_Type_TTLBOS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _update_HCR_EL2_Type_TVM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_HCR_Type_TVM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_HCR_Type_TVM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_HCR_EL2_Type_TWEDEL (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _update_SCR_EL3_Type_TWEDEL (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 30 x)

def _update_SCTLR_EL1_Type_TWEDEL (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 46 x)

def _update_SCTLR_EL2_Type_TWEDEL (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 46 x)

def _get_SCTLR_EL1_Type_TWEDEL (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 49 46)

def _get_SCTLR_EL2_Type_TWEDEL (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 49 46)

def _update_HCR_EL2_Type_TWEDEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_SCR_EL3_Type_TWEDEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_SCTLR_EL1_Type_TWEDEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _update_SCTLR_EL2_Type_TWEDEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _get_SCTLR_EL1_Type_TWEDEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)

def _get_SCTLR_EL2_Type_TWEDEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)

def _update_HCR_EL2_Type_VF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_HCR_Type_VF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_HCR_EL2_Type_VI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_HCR_Type_VI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_HCR_EL2_Type_VM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_HCR_Type_VM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_HCR_EL2_Type_VSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def undefined_SCR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SCR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_SCR_EL3_Type_ADEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _update_SCR_EL3_Type_AIEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _update_SCR_EL3_Type_D128En (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 47 x)

def _update_HCRX_EL2_Type_D128En (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_HCRX_EL2_Type_D128En (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_SCR_EL3_Type_EASE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_SCTLR2_EL1_Type_EASE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SCTLR2_EL2_Type_EASE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_SCR_EL3_Type_ECVEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_SCR_EL3_Type_EEL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_SCR_EL3_Type_EnAS0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _update_HCRX_EL2_Type_EnAS0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_SCTLR_EL1_Type_EnAS0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _update_SCTLR_EL2_Type_EnAS0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _get_HCRX_EL2_Type_EnAS0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_SCTLR_EL1_Type_EnAS0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)

def _get_SCTLR_EL2_Type_EnAS0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)

def _update_SCR_EL3_Type_EnIDCP128 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _update_HCRX_EL2_Type_EnIDCP128 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_SCTLR2_EL1_Type_EnIDCP128 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_SCTLR2_EL2_Type_EnIDCP128 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_HCRX_EL2_Type_EnIDCP128 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


