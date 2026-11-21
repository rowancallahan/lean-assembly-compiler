import Armv9.Flow
import Armv9.Instrs32
import Armv9.Instrs64
import Armv9.Instrs64Sve
import Armv9.Instrs64Sme
import Armv9.DecodeEnd.P00
import Armv9.DecodeEnd.P01
import Armv9.DecodeEnd.P03
import Armv9.DecodeEnd.P04
import Armv9.DecodeEnd.P05
import Armv9.DecodeEnd.P06
import Armv9.DecodeEnd.P24

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

/-- Type quantifiers: pc : Int -/
def __DecodeA64 (pc : Int) (opcode : (BitVec 32)) : SailM Unit := do
  let v__0 := opcode
  if ((((Sail.BitVec.extractLsb v__0 31 31) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb v__0 28 25) == (0x0#4 : (BitVec 4)))) : Bool)
  then (__DecodeA64_Reserved pc opcode)
  else
    (do
      if ((((Sail.BitVec.extractLsb v__0 31 31) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb v__0 28 25) == (0x0#4 : (BitVec 4)))) : Bool)
      then (__DecodeA64_SME pc opcode)
      else
        (do
          if (((Sail.BitVec.extractLsb v__0 28 25) == (0x1#4 : (BitVec 4))) : Bool)
          then (__DecodeA64_Unallocated1 pc opcode)
          else
            (do
              if (((Sail.BitVec.extractLsb v__0 28 25) == (0x2#4 : (BitVec 4))) : Bool)
              then (__DecodeA64_SVE pc opcode)
              else
                (do
                  if (((Sail.BitVec.extractLsb v__0 28 25) == (0x3#4 : (BitVec 4))) : Bool)
                  then (__DecodeA64_Unallocated2 pc opcode)
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__0 28 26) == (0b100#3 : (BitVec 3))) : Bool)
                      then (__DecodeA64_DataProcImm pc opcode)
                      else
                        (do
                          if (((Sail.BitVec.extractLsb v__0 28 26) == (0b101#3 : (BitVec 3))) : Bool)
                          then (__DecodeA64_BranchExcSys pc opcode)
                          else
                            (do
                              if ((((Sail.BitVec.extractLsb v__0 27 27) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb v__0 25 25) == (0#1 : (BitVec 1)))) : Bool)
                              then (__DecodeA64_LoadStore pc opcode)
                              else
                                (do
                                  if (((Sail.BitVec.extractLsb v__0 27 25) == (0b101#3 : (BitVec 3))) : Bool)
                                  then (__DecodeA64_DataProcReg pc opcode)
                                  else (__DecodeA64_DataProcFPSIMD pc opcode)))))))))


