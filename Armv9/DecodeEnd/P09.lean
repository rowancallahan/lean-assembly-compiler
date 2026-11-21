import Armv9.Flow
import Armv9.Instrs32
import Armv9.Instrs64
import Armv9.Instrs64Sve
import Armv9.Instrs64Sme

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
def __DecodeA32_Media (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 21) == (0b0111110#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 6 0) == (0b0011111#7 : (BitVec 7))))) <&&> (do
       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
         (pure ((← readReg SEE) <b 2856)))))) : Bool)
  then
    (do
      writeReg SEE 2856
      let cond := (BitVec.slice __opcode 28 4)
      let msb := (BitVec.slice __opcode 16 5)
      let Rd := (BitVec.slice __opcode 12 4)
      let lsb := (BitVec.slice __opcode 7 5)
      (decode_aarch32_instrs_BFC_A1enc_A_txt cond msb Rd lsb))
  else
    (do
      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 21) == (0b0111110#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 6 4) == (0b001#3 : (BitVec 3))))) <&&> (do
           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
             (pure ((← readReg SEE) <b 2858)))))) : Bool)
      then
        (do
          writeReg SEE 2858
          let cond := (BitVec.slice __opcode 28 4)
          let msb := (BitVec.slice __opcode 16 5)
          let Rd := (BitVec.slice __opcode 12 4)
          let lsb := (BitVec.slice __opcode 7 5)
          let Rn := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_BFI_A1enc_A_txt cond msb Rd lsb Rn))
      else
        (do
          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x68#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 5 4) == (0b01#2 : (BitVec 2))))) <&&> (do
               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                 (pure ((← readReg SEE) <b 3047)))))) : Bool)
          then
            (do
              writeReg SEE 3047
              let cond := (BitVec.slice __opcode 28 4)
              let Rn := (BitVec.slice __opcode 16 4)
              let Rd := (BitVec.slice __opcode 12 4)
              let imm5 := (BitVec.slice __opcode 7 5)
              let tb := (BitVec.slice __opcode 6 1)
              let Rm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_PKH_A1enc_A_txt cond Rn Rd imm5 tb Rm))
          else
            (do
              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x62#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF1#8 : (BitVec 8))))) <&&> (do
                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                     (pure ((← readReg SEE) <b 3064)))))) : Bool)
              then
                (do
                  writeReg SEE 3064
                  let cond := (BitVec.slice __opcode 28 4)
                  let Rn := (BitVec.slice __opcode 16 4)
                  let Rd := (BitVec.slice __opcode 12 4)
                  let Rm := (BitVec.slice __opcode 0 4)
                  if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                  else (decode_aarch32_instrs_QADD16_A1enc_A_txt cond Rn Rd Rm))
              else
                (do
                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x62#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF9#8 : (BitVec 8))))) <&&> (do
                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                         (pure ((← readReg SEE) <b 3066)))))) : Bool)
                  then
                    (do
                      writeReg SEE 3066
                      let cond := (BitVec.slice __opcode 28 4)
                      let Rn := (BitVec.slice __opcode 16 4)
                      let Rd := (BitVec.slice __opcode 12 4)
                      let Rm := (BitVec.slice __opcode 0 4)
                      if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                      else (decode_aarch32_instrs_QADD8_A1enc_A_txt cond Rn Rd Rm))
                  else
                    (do
                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x62#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF3#8 : (BitVec 8))))) <&&> (do
                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                             (pure ((← readReg SEE) <b 3070)))))) : Bool)
                      then
                        (do
                          writeReg SEE 3070
                          let cond := (BitVec.slice __opcode 28 4)
                          let Rn := (BitVec.slice __opcode 16 4)
                          let Rd := (BitVec.slice __opcode 12 4)
                          let Rm := (BitVec.slice __opcode 0 4)
                          if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                          else (decode_aarch32_instrs_QASX_A1enc_A_txt cond Rn Rd Rm))
                      else
                        (do
                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x62#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF5#8 : (BitVec 8))))) <&&> (do
                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                 (pure ((← readReg SEE) <b 3076)))))) : Bool)
                          then
                            (do
                              writeReg SEE 3076
                              let cond := (BitVec.slice __opcode 28 4)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let Rd := (BitVec.slice __opcode 12 4)
                              let Rm := (BitVec.slice __opcode 0 4)
                              if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                              else (decode_aarch32_instrs_QSAX_A1enc_A_txt cond Rn Rd Rm))
                          else
                            (do
                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x62#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF7#8 : (BitVec 8))))) <&&> (do
                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                     (pure ((← readReg SEE) <b 3078)))))) : Bool)
                              then
                                (do
                                  writeReg SEE 3078
                                  let cond := (BitVec.slice __opcode 28 4)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let Rd := (BitVec.slice __opcode 12 4)
                                  let Rm := (BitVec.slice __opcode 0 4)
                                  if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                  else (decode_aarch32_instrs_QSUB16_A1enc_A_txt cond Rn Rd Rm))
                              else
                                (do
                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x62#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xFF#8 : (BitVec 8))))) <&&> (do
                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                         (pure ((← readReg SEE) <b 3080)))))) : Bool)
                                  then
                                    (do
                                      writeReg SEE 3080
                                      let cond := (BitVec.slice __opcode 28 4)
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let Rd := (BitVec.slice __opcode 12 4)
                                      let Rm := (BitVec.slice __opcode 0 4)
                                      if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                      else (decode_aarch32_instrs_QSUB8_A1enc_A_txt cond Rn Rd Rm))
                                  else
                                    (do
                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 16) == (0x6FF#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF3#8 : (BitVec 8))))) <&&> (do
                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                             (pure ((← readReg SEE) <b 3084)))))) : Bool)
                                      then
                                        (do
                                          writeReg SEE 3084
                                          let cond := (BitVec.slice __opcode 28 4)
                                          let Rd := (BitVec.slice __opcode 12 4)
                                          let Rm := (BitVec.slice __opcode 0 4)
                                          if ((((((((((BitVec.join1 [(BitVec.access __opcode 16)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 17)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 18)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 19)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                          else (decode_aarch32_instrs_RBIT_A1enc_A_txt cond Rd Rm))
                                      else
                                        (do
                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 16) == (0x6BF#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xFB#8 : (BitVec 8))))) <&&> (do
                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                 (pure ((← readReg SEE) <b 3086)))))) : Bool)
                                          then
                                            (do
                                              writeReg SEE 3086
                                              let cond := (BitVec.slice __opcode 28 4)
                                              let Rd := (BitVec.slice __opcode 12 4)
                                              let Rm := (BitVec.slice __opcode 0 4)
                                              if ((((((((((BitVec.join1 [(BitVec.access __opcode 16)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 17)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 18)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 19)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                              else (decode_aarch32_instrs_REV16_A1enc_A_txt cond Rd Rm))
                                          else
                                            (do
                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 16) == (0x6BF#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF3#8 : (BitVec 8))))) <&&> (do
                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                     (pure ((← readReg SEE) <b 3089)))))) : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3089
                                                  let cond := (BitVec.slice __opcode 28 4)
                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                  if ((((((((((BitVec.join1 [(BitVec.access __opcode 16)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 17)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 18)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 19)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                  else (decode_aarch32_instrs_REV_A1enc_A_txt cond Rd Rm))
                                              else
                                                (do
                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 16) == (0x6FF#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xFB#8 : (BitVec 8))))) <&&> (do
                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                         (pure ((← readReg SEE) <b 3092)))))) : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3092
                                                      let cond := (BitVec.slice __opcode 28 4)
                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                      if ((((((((((BitVec.join1 [(BitVec.access __opcode 16)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 17)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 18)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 19)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                      else (decode_aarch32_instrs_REVSH_A1enc_A_txt cond Rd Rm))
                                                  else
                                                    (do
                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x61#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF1#8 : (BitVec 8))))) <&&> (do
                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                             (pure ((← readReg SEE) <b 3105)))))) : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3105
                                                          let cond := (BitVec.slice __opcode 28 4)
                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                          let Rd := (BitVec.slice __opcode 12 4)
                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                          if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                          else (decode_aarch32_instrs_SADD16_A1enc_A_txt cond Rn Rd Rm))
                                                      else
                                                        (do
                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x61#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF9#8 : (BitVec 8))))) <&&> (do
                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                 (pure ((← readReg SEE) <b 3107)))))) : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3107
                                                              let cond := (BitVec.slice __opcode 28 4)
                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                              let Rd := (BitVec.slice __opcode 12 4)
                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                              if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                              else (decode_aarch32_instrs_SADD8_A1enc_A_txt cond Rn Rd Rm))
                                                          else
                                                            (do
                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x61#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF3#8 : (BitVec 8))))) <&&> (do
                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                     (pure ((← readReg SEE) <b 3109)))))) : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3109
                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                                  if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                  else (decode_aarch32_instrs_SASX_A1enc_A_txt cond Rn Rd Rm))
                                                              else
                                                                (do
                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 21) == (0b0111101#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 6 4) == (0b101#3 : (BitVec 3))))) <&&> (do
                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                         (pure ((← readReg SEE) <b 3119)))))) : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3119
                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                      let widthm1 := (BitVec.slice __opcode 16 5)
                                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                                      let lsb := (BitVec.slice __opcode 7 5)
                                                                      let Rn := (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_SBFX_A1enc_A_txt cond widthm1 Rd lsb Rn))
                                                                  else
                                                                    (do
                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x71#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 7 4) == (0x1#4 : (BitVec 4))))) <&&> (do
                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                             (pure ((← readReg SEE) <b 3121)))))) : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3121
                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                          let Rd := (BitVec.slice __opcode 16 4)
                                                                          let Ra := (BitVec.slice __opcode 12 4)
                                                                          let Rm := (BitVec.slice __opcode 8 4)
                                                                          let Rn := (BitVec.slice __opcode 0 4)
                                                                          (decode_aarch32_instrs_SDIV_A1enc_A_txt cond Rd Ra Rm Rn))
                                                                      else
                                                                        (do
                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x68#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xFB#8 : (BitVec 8))))) <&&> (do
                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                 (pure ((← readReg SEE) <b 3123)))))) : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3123
                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                                              let Rd := (BitVec.slice __opcode 12 4)
                                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                                              if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                              else (decode_aarch32_instrs_SEL_A1enc_A_txt cond Rn Rd Rm))
                                                                          else
                                                                            (do
                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x63#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF1#8 : (BitVec 8))))) <&&> (do
                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                     (pure ((← readReg SEE) <b 3130)))))) : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3130
                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                                                  if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                  else (decode_aarch32_instrs_SHADD16_A1enc_A_txt cond Rn Rd Rm))
                                                                              else
                                                                                (do
                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x63#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF9#8 : (BitVec 8))))) <&&> (do
                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                         (pure ((← readReg SEE) <b 3132)))))) : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3132
                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                                                      if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                      else (decode_aarch32_instrs_SHADD8_A1enc_A_txt cond Rn Rd Rm))
                                                                                  else
                                                                                    (do
                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x63#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF3#8 : (BitVec 8))))) <&&> (do
                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                             (pure ((← readReg SEE) <b 3134)))))) : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3134
                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                                                          let Rd := (BitVec.slice __opcode 12 4)
                                                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                                                          if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                          else (decode_aarch32_instrs_SHASX_A1enc_A_txt cond Rn Rd Rm))
                                                                                      else
                                                                                        (do
                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x63#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF5#8 : (BitVec 8))))) <&&> (do
                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                 (pure ((← readReg SEE) <b 3136)))))) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3136
                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                                                              let Rd := (BitVec.slice __opcode 12 4)
                                                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                                                              if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                              else (decode_aarch32_instrs_SHSAX_A1enc_A_txt cond Rn Rd Rm))
                                                                                          else
                                                                                            (do
                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x63#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF7#8 : (BitVec 8))))) <&&> (do
                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                     (pure ((← readReg SEE) <b 3138)))))) : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3138
                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                                                                  if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                  else (decode_aarch32_instrs_SHSUB16_A1enc_A_txt cond Rn Rd Rm))
                                                                                              else
                                                                                                (do
                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x63#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xFF#8 : (BitVec 8))))) <&&> (do
                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                         (pure ((← readReg SEE) <b 3140)))))) : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3140
                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                                                                      if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                      else (decode_aarch32_instrs_SHSUB8_A1enc_A_txt cond Rn Rd Rm))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x70#8 : (BitVec 8))) && (((Sail.BitVec.extractLsb __opcode 7 6) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1)))))) <&&> (do
                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                             (pure ((← readReg SEE) <b 3144)))))) : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3144
                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                          let Rd := (BitVec.slice __opcode 16 4)
                                                                                                          let Ra := (BitVec.slice __opcode 12 4)
                                                                                                          let Rm := (BitVec.slice __opcode 8 4)
                                                                                                          let M := (BitVec.slice __opcode 5 1)
                                                                                                          let Rn := (BitVec.slice __opcode 0 4)
                                                                                                          (decode_aarch32_instrs_SMLAD_A1enc_A_txt cond Rd Ra Rm M Rn))
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x74#8 : (BitVec 8))) && (((Sail.BitVec.extractLsb __opcode 7 6) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1)))))) <&&> (do
                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                 (pure ((← readReg SEE) <b 3150)))))) : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3150
                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                              let RdHi := (BitVec.slice __opcode 16 4)
                                                                                                              let RdLo := (BitVec.slice __opcode 12 4)
                                                                                                              let Rm := (BitVec.slice __opcode 8 4)
                                                                                                              let M := (BitVec.slice __opcode 5 1)
                                                                                                              let Rn := (BitVec.slice __opcode 0 4)
                                                                                                              (decode_aarch32_instrs_SMLALD_A1enc_A_txt cond RdHi RdLo Rm M Rn))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x70#8 : (BitVec 8))) && (((Sail.BitVec.extractLsb __opcode 7 6) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1)))))) <&&> (do
                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                     (pure ((← readReg SEE) <b 3154)))))) : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3154
                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                  let Rd := (BitVec.slice __opcode 16 4)
                                                                                                                  let Ra := (BitVec.slice __opcode 12 4)
                                                                                                                  let Rm := (BitVec.slice __opcode 8 4)
                                                                                                                  let M := (BitVec.slice __opcode 5 1)
                                                                                                                  let Rn := (BitVec.slice __opcode 0 4)
                                                                                                                  (decode_aarch32_instrs_SMLSD_A1enc_A_txt cond Rd Ra Rm M Rn))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x74#8 : (BitVec 8))) && (((Sail.BitVec.extractLsb __opcode 7 6) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1)))))) <&&> (do
                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                         (pure ((← readReg SEE) <b 3156)))))) : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 3156
                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                      let RdHi := (BitVec.slice __opcode 16 4)
                                                                                                                      let RdLo := (BitVec.slice __opcode 12 4)
                                                                                                                      let Rm := (BitVec.slice __opcode 8 4)
                                                                                                                      let M := (BitVec.slice __opcode 5 1)
                                                                                                                      let Rn := (BitVec.slice __opcode 0 4)
                                                                                                                      (decode_aarch32_instrs_SMLSLD_A1enc_A_txt cond RdHi RdLo Rm M Rn))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x75#8 : (BitVec 8))) && (((Sail.BitVec.extractLsb __opcode 7 6) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1)))))) <&&> (do
                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                             (pure ((← readReg SEE) <b 3158)))))) : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 3158
                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                          let Rd := (BitVec.slice __opcode 16 4)
                                                                                                                          let Ra := (BitVec.slice __opcode 12 4)
                                                                                                                          let Rm := (BitVec.slice __opcode 8 4)
                                                                                                                          let R := (BitVec.slice __opcode 5 1)
                                                                                                                          let Rn := (BitVec.slice __opcode 0 4)
                                                                                                                          (decode_aarch32_instrs_SMMLA_A1enc_A_txt cond Rd Ra Rm R Rn))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x75#8 : (BitVec 8))) && (((Sail.BitVec.extractLsb __opcode 7 6) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1)))))) <&&> (do
                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                 (pure ((← readReg SEE) <b 3160)))))) : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 3160
                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                              let Rd := (BitVec.slice __opcode 16 4)
                                                                                                                              let Ra := (BitVec.slice __opcode 12 4)
                                                                                                                              let Rm := (BitVec.slice __opcode 8 4)
                                                                                                                              let R := (BitVec.slice __opcode 5 1)
                                                                                                                              let Rn := (BitVec.slice __opcode 0 4)
                                                                                                                              (decode_aarch32_instrs_SMMLS_A1enc_A_txt cond Rd Ra Rm R Rn))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x75#8 : (BitVec 8))) && (((Sail.BitVec.extractLsb __opcode 15 12) == (0xF#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 7 6) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                     (pure ((← readReg SEE) <b 3162)))))) : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 3162
                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                  let Rd := (BitVec.slice __opcode 16 4)
                                                                                                                                  let Rm := (BitVec.slice __opcode 8 4)
                                                                                                                                  let R := (BitVec.slice __opcode 5 1)
                                                                                                                                  let Rn := (BitVec.slice __opcode 0 4)
                                                                                                                                  (decode_aarch32_instrs_SMMUL_A1enc_A_txt cond Rd Rm R Rn))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x70#8 : (BitVec 8))) && (((Sail.BitVec.extractLsb __opcode 15 12) == (0xF#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 7 6) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                         (pure ((← readReg SEE) <b 3164)))))) : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 3164
                                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                      let Rd := (BitVec.slice __opcode 16 4)
                                                                                                                                      let Rm := (BitVec.slice __opcode 8 4)
                                                                                                                                      let M := (BitVec.slice __opcode 5 1)
                                                                                                                                      let Rn := (BitVec.slice __opcode 0 4)
                                                                                                                                      (decode_aarch32_instrs_SMUAD_A1enc_A_txt cond Rd Rm M Rn))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x70#8 : (BitVec 8))) && (((Sail.BitVec.extractLsb __opcode 15 12) == (0xF#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 7 6) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                             (pure ((← readReg SEE) <b 3172)))))) : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 3172
                                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                          let Rd := (BitVec.slice __opcode 16 4)
                                                                                                                                          let Rm := (BitVec.slice __opcode 8 4)
                                                                                                                                          let M := (BitVec.slice __opcode 5 1)
                                                                                                                                          let Rn := (BitVec.slice __opcode 0 4)
                                                                                                                                          (decode_aarch32_instrs_SMUSD_A1enc_A_txt cond Rd Rm M Rn))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x6A#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF3#8 : (BitVec 8))))) <&&> (do
                                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                 (pure ((← readReg SEE) <b 3174)))))) : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 3174
                                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                              let sat_imm := (BitVec.slice __opcode 16 4)
                                                                                                                                              let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                              let Rn := (BitVec.slice __opcode 0 4)
                                                                                                                                              if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                              else (decode_aarch32_instrs_SSAT16_A1enc_A_txt cond sat_imm Rd Rn))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 21) == (0b0110101#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 5 4) == (0b01#2 : (BitVec 2))))) <&&> (do
                                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                     (pure ((← readReg SEE) <b 3176)))))) : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 3176
                                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                  let sat_imm := (BitVec.slice __opcode 16 5)
                                                                                                                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                  let imm5 := (BitVec.slice __opcode 7 5)
                                                                                                                                                  let sh := (BitVec.slice __opcode 6 1)
                                                                                                                                                  let Rn := (BitVec.slice __opcode 0 4)
                                                                                                                                                  (decode_aarch32_instrs_SSAT_A1enc_A_txt cond sat_imm Rd imm5 sh Rn))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x61#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF5#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                         (pure ((← readReg SEE) <b 3178)))))) : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 3178
                                                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                      if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                      else (decode_aarch32_instrs_SSAX_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x61#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF7#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                             (pure ((← readReg SEE) <b 3180)))))) : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 3180
                                                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                          let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                          if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                          else (decode_aarch32_instrs_SSUB16_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x61#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xFF#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                 (pure ((← readReg SEE) <b 3182)))))) : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 3182
                                                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                              let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                              if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                              else (decode_aarch32_instrs_SSUB8_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x68#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 9 4) == (0b000111#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                     (pure ((← readReg SEE) <b 3253)))))) : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 3253
                                                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                  let rotate := (BitVec.slice __opcode 10 2)
                                                                                                                                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                  if ((((BitVec.join1 [(BitVec.access __opcode 8)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 0#1)) : Bool)
                                                                                                                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                  else (decode_aarch32_instrs_SXTAB16_A1enc_A_txt cond Rn Rd rotate Rm))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x6A#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 9 4) == (0b000111#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                         (pure ((← readReg SEE) <b 3255)))))) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 3255
                                                                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                      let rotate := (BitVec.slice __opcode 10 2)
                                                                                                                                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                      if ((((BitVec.join1 [(BitVec.access __opcode 8)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 0#1)) : Bool)
                                                                                                                                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                      else (decode_aarch32_instrs_SXTAB_A1enc_A_txt cond Rn Rd rotate Rm))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x6B#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 9 4) == (0b000111#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                             (pure ((← readReg SEE) <b 3257)))))) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 3257
                                                                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                          let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                          let rotate := (BitVec.slice __opcode 10 2)
                                                                                                                                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                          if ((((BitVec.join1 [(BitVec.access __opcode 8)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 0#1)) : Bool)
                                                                                                                                                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                          else (decode_aarch32_instrs_SXTAH_A1enc_A_txt cond Rn Rd rotate Rm))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 16) == (0x68F#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 9 4) == (0b000111#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                 (pure ((← readReg SEE) <b 3259)))))) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 3259
                                                                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                              let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                              let rotate := (BitVec.slice __opcode 10 2)
                                                                                                                                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                              if ((((BitVec.join1 [(BitVec.access __opcode 8)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 0#1)) : Bool)
                                                                                                                                                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                              else (decode_aarch32_instrs_SXTB16_A1enc_A_txt cond Rd rotate Rm))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 16) == (0x6AF#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 9 4) == (0b000111#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                     (pure ((← readReg SEE) <b 3261)))))) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 3261
                                                                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                  let rotate := (BitVec.slice __opcode 10 2)
                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                  if ((((BitVec.join1 [(BitVec.access __opcode 8)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 0#1)) : Bool)
                                                                                                                                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                  else (decode_aarch32_instrs_SXTB_A1enc_A_txt cond Rd rotate Rm))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 16) == (0x6BF#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 9 4) == (0b000111#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                         (pure ((← readReg SEE) <b 3264)))))) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      writeReg SEE 3264
                                                                                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                      let rotate := (BitVec.slice __opcode 10 2)
                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                      if ((((BitVec.join1 [(BitVec.access __opcode 8)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 0#1)) : Bool)
                                                                                                                                                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                      else (decode_aarch32_instrs_SXTH_A1enc_A_txt cond Rd rotate Rm))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF1#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                             (pure ((← readReg SEE) <b 3279)))))) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          writeReg SEE 3279
                                                                                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                          if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                          else (decode_aarch32_instrs_UADD16_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF9#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                 (pure ((← readReg SEE) <b 3281)))))) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              writeReg SEE 3281
                                                                                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                              if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                              else (decode_aarch32_instrs_UADD8_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF3#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                     (pure ((← readReg SEE) <b 3283)))))) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  writeReg SEE 3283
                                                                                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                  if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                  else (decode_aarch32_instrs_UASX_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 21) == (0b0111111#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 6 4) == (0b101#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                         (pure ((← readReg SEE) <b 3285)))))) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      writeReg SEE 3285
                                                                                                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                      let widthm1 := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                      let lsb := (BitVec.slice __opcode 7 5)
                                                                                                                                                                                                      let Rn := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                      (decode_aarch32_instrs_UBFX_A1enc_A_txt cond widthm1 Rd lsb Rn))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE7F#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 7 4) == (0xF#4 : (BitVec 4))))) <&&> (do
                                                                                                                                                                                                           (pure ((← readReg SEE) <b 3287))))) : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          writeReg SEE 3287
                                                                                                                                                                                                          let imm12 := (BitVec.slice __opcode 8 12)
                                                                                                                                                                                                          let imm4 := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                          (decode_aarch32_instrs_UDF_A1enc_A_txt imm12 imm4))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x73#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 7 4) == (0x1#4 : (BitVec 4))))) <&&> (do
                                                                                                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                 (pure ((← readReg SEE) <b 3290)))))) : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              writeReg SEE 3290
                                                                                                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                              let Ra := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                              (decode_aarch32_instrs_UDIV_A1enc_A_txt cond Rd Ra Rm Rn))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x67#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF1#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                     (pure ((← readReg SEE) <b 3292)))))) : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  writeReg SEE 3292
                                                                                                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                  if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                  else (decode_aarch32_instrs_UHADD16_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x67#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF9#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                         (pure ((← readReg SEE) <b 3294)))))) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      writeReg SEE 3294
                                                                                                                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                      if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                      else (decode_aarch32_instrs_UHADD8_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x67#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF3#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                             (pure ((← readReg SEE) <b 3296)))))) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          writeReg SEE 3296
                                                                                                                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                          if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                          else (decode_aarch32_instrs_UHASX_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x67#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF5#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                 (pure ((← readReg SEE) <b 3298)))))) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              writeReg SEE 3298
                                                                                                                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                              if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                              else (decode_aarch32_instrs_UHSAX_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x67#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF7#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                     (pure ((← readReg SEE) <b 3300)))))) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  writeReg SEE 3300
                                                                                                                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                  if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                  else (decode_aarch32_instrs_UHSUB16_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x67#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xFF#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                         (pure ((← readReg SEE) <b 3302)))))) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      writeReg SEE 3302
                                                                                                                                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                      if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                      else (decode_aarch32_instrs_UHSUB8_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x66#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF1#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                             (pure ((← readReg SEE) <b 3310)))))) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          writeReg SEE 3310
                                                                                                                                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                          if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                          else (decode_aarch32_instrs_UQADD16_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x66#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF9#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                 (pure ((← readReg SEE) <b 3312)))))) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              writeReg SEE 3312
                                                                                                                                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                              if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                              else (decode_aarch32_instrs_UQADD8_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x66#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF3#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                     (pure ((← readReg SEE) <b 3314)))))) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  writeReg SEE 3314
                                                                                                                                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                  if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                  else (decode_aarch32_instrs_UQASX_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x66#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF5#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                         (pure ((← readReg SEE) <b 3316)))))) : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      writeReg SEE 3316
                                                                                                                                                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                      if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                      else (decode_aarch32_instrs_UQSAX_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x66#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF7#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                             (pure ((← readReg SEE) <b 3318)))))) : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          writeReg SEE 3318
                                                                                                                                                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                          if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                                                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                          else (decode_aarch32_instrs_UQSUB16_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x66#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xFF#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                                 (pure ((← readReg SEE) <b 3320)))))) : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              writeReg SEE 3320
                                                                                                                                                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                              if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                                                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                              else (decode_aarch32_instrs_UQSUB8_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x78#8 : (BitVec 8))) && (((Sail.BitVec.extractLsb __opcode 15 12) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 7 4) == (0x1#4 : (BitVec 4)))))) <&&> (do
                                                                                                                                                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                                     (pure ((← readReg SEE) <b 3322)))))) : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  writeReg SEE 3322
                                                                                                                                                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_USAD8_A1enc_A_txt cond Rd Rm Rn))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x78#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 7 4) == (0x1#4 : (BitVec 4))))) <&&> (do
                                                                                                                                                                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                                         (pure ((← readReg SEE) <b 3324)))))) : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      writeReg SEE 3324
                                                                                                                                                                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                                      let Rd := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                                      let Ra := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                                                                                                                      let Rn := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_USADA8_A1enc_A_txt cond Rd Ra Rm Rn))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x6E#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF3#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                                             (pure ((← readReg SEE) <b 3326)))))) : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          writeReg SEE 3326
                                                                                                                                                                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                                          let sat_imm := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                          let Rn := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                          if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                                                                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                                          else (decode_aarch32_instrs_USAT16_A1enc_A_txt cond sat_imm Rd Rn))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 21) == (0b0110111#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 5 4) == (0b01#2 : (BitVec 2))))) <&&> (do
                                                                                                                                                                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                                                 (pure ((← readReg SEE) <b 3328)))))) : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              writeReg SEE 3328
                                                                                                                                                                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                                              let sat_imm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                              let imm5 := (BitVec.slice __opcode 7 5)
                                                                                                                                                                                                                                                                              let sh := (BitVec.slice __opcode 6 1)
                                                                                                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_USAT_A1enc_A_txt cond sat_imm Rd imm5 sh Rn))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF5#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                                                     (pure ((← readReg SEE) <b 3330)))))) : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  writeReg SEE 3330
                                                                                                                                                                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                                  if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                                                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                                                  else (decode_aarch32_instrs_USAX_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xF7#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                                                         (pure ((← readReg SEE) <b 3332)))))) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      writeReg SEE 3332
                                                                                                                                                                                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                                      if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                                                                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                                                      else (decode_aarch32_instrs_USUB16_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 4) == (0xFF#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                                                             (pure ((← readReg SEE) <b 3334)))))) : Bool)
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          writeReg SEE 3334
                                                                                                                                                                                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                                          if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) : Bool)
                                                                                                                                                                                                                                                                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                                                          else (decode_aarch32_instrs_USUB8_A1enc_A_txt cond Rn Rd Rm))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x6C#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 9 4) == (0b000111#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                                                                 (pure ((← readReg SEE) <b 3336)))))) : Bool)
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              writeReg SEE 3336
                                                                                                                                                                                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                                              let rotate := (BitVec.slice __opcode 10 2)
                                                                                                                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                                              if ((((BitVec.join1 [(BitVec.access __opcode 8)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 0#1)) : Bool)
                                                                                                                                                                                                                                                                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                                                              else (decode_aarch32_instrs_UXTAB16_A1enc_A_txt cond Rn Rd rotate Rm))
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x6E#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 9 4) == (0b000111#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                                                                     (pure ((← readReg SEE) <b 3338)))))) : Bool)
                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  writeReg SEE 3338
                                                                                                                                                                                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                                                  let rotate := (BitVec.slice __opcode 10 2)
                                                                                                                                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                                                  if ((((BitVec.join1 [(BitVec.access __opcode 8)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 0#1)) : Bool)
                                                                                                                                                                                                                                                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                                                                  else (decode_aarch32_instrs_UXTAB_A1enc_A_txt cond Rn Rd rotate Rm))
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0x6F#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 9 4) == (0b000111#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                                                                         (pure ((← readReg SEE) <b 3340)))))) : Bool)
                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      writeReg SEE 3340
                                                                                                                                                                                                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                                                                      let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                                                      let rotate := (BitVec.slice __opcode 10 2)
                                                                                                                                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                                                      if ((((BitVec.join1 [(BitVec.access __opcode 8)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 0#1)) : Bool)
                                                                                                                                                                                                                                                                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                                                                      else (decode_aarch32_instrs_UXTAH_A1enc_A_txt cond Rn Rd rotate Rm))
                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 16) == (0x6CF#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 9 4) == (0b000111#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                                                                             (pure ((← readReg SEE) <b 3342)))))) : Bool)
                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          writeReg SEE 3342
                                                                                                                                                                                                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                                                          let rotate := (BitVec.slice __opcode 10 2)
                                                                                                                                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                                                          if ((((BitVec.join1 [(BitVec.access __opcode 8)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 0#1)) : Bool)
                                                                                                                                                                                                                                                                                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                                                                          else (decode_aarch32_instrs_UXTB16_A1enc_A_txt cond Rd rotate Rm))
                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 16) == (0x6EF#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 9 4) == (0b000111#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                                                                                 (pure ((← readReg SEE) <b 3344)))))) : Bool)
                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              writeReg SEE 3344
                                                                                                                                                                                                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                                                              let rotate := (BitVec.slice __opcode 10 2)
                                                                                                                                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                                                              if ((((BitVec.join1 [(BitVec.access __opcode 8)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 0#1)) : Bool)
                                                                                                                                                                                                                                                                                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                                                                              else (decode_aarch32_instrs_UXTB_A1enc_A_txt cond Rd rotate Rm))
                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 16) == (0x6FF#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 9 4) == (0b000111#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                                                                                     (pure ((← readReg SEE) <b 3347)))))) : Bool)
                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  writeReg SEE 3347
                                                                                                                                                                                                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                                                                  let rotate := (BitVec.slice __opcode 10 2)
                                                                                                                                                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                                                                  if ((((BitVec.join1 [(BitVec.access __opcode 8)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 0#1)) : Bool)
                                                                                                                                                                                                                                                                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                                                                                  else (decode_aarch32_instrs_UXTH_A1enc_A_txt cond Rd rotate Rm))
                                                                                                                                                                                                                                                                                                              else (sailThrow ((Error_Undefined ())) : SailM Unit))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


