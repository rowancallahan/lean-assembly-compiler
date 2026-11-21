import Armv9.Flow
import Armv9.Prelude
import Armv9.V8Base
import Armv9.Stubs
import Armv9.SysregsAutogen.P00
import Armv9.SysregsAutogen.P01
import Armv9.SysregsAutogen.P02
import Armv9.SysregsAutogen.P03
import Armv9.SysregsAutogen.P04
import Armv9.SysregsAutogen.P05
import Armv9.SysregsAutogen.P06
import Armv9.SysregsAutogen.P07
import Armv9.SysregsAutogen.P08
import Armv9.SysregsAutogen.P09
import Armv9.SysregsAutogen.P10
import Armv9.SysregsAutogen.P11
import Armv9.SysregsAutogen.P12
import Armv9.SysregsAutogen.P13
import Armv9.SysregsAutogen.P14
import Armv9.SysregsAutogen.P15
import Armv9.SysregsAutogen.P16
import Armv9.SysregsAutogen.P17
import Armv9.SysregsAutogen.P18
import Armv9.SysregsAutogen.P19
import Armv9.SysregsAutogen.P20
import Armv9.SysregsAutogen.P21
import Armv9.SysregsAutogen.P22

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


