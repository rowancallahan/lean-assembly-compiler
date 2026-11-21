import Armv9.Flow
import Armv9.Instrs32
import Armv9.Instrs64
import Armv9.Instrs64Sve
import Armv9.Instrs64Sme
import Armv9.DecodeEnd.P00
import Armv9.DecodeEnd.P07
import Armv9.DecodeEnd.P08
import Armv9.DecodeEnd.P09
import Armv9.DecodeEnd.P10

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
def __DecodeA32 (pc : Int) (opcode : (BitVec 32)) : SailM Unit := do
  let v__28 := opcode
  if (((Sail.BitVec.extractLsb v__28 31 27) == (0b11110#5 : (BitVec 5))) : Bool)
  then (__DecodeA32_Unconditional pc opcode)
  else
    (do
      if (((Sail.BitVec.extractLsb v__28 27 26) == (0b00#2 : (BitVec 2))) : Bool)
      then (__DecodeA32_DataProMisc pc opcode)
      else
        (do
          if (((Sail.BitVec.extractLsb v__28 27 25) == (0b010#3 : (BitVec 3))) : Bool)
          then (__DecodeA32_LoadStoreImmLit pc opcode)
          else
            (do
              if ((((Sail.BitVec.extractLsb v__28 27 25) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb v__28 4 4) == (0#1 : (BitVec 1)))) : Bool)
              then (__DecodeA32_LoadStoreReg pc opcode)
              else
                (do
                  if ((((Sail.BitVec.extractLsb v__28 27 25) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb v__28 4 4) == (1#1 : (BitVec 1)))) : Bool)
                  then (__DecodeA32_Media pc opcode)
                  else
                    (do
                      if (((Sail.BitVec.extractLsb v__28 27 26) == (0b10#2 : (BitVec 2))) : Bool)
                      then (__DecodeA32_BranchBlock pc opcode)
                      else (__DecodeA32_SysASIMDFP pc opcode))))))

