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

def __DecodeA64_SVE_tail11 (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100101100#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b101#3 : (BitVec 3))))) <&&> (do
       (pure ((← readReg SEE) <b 2137))))) : Bool)
  then
    (do
      writeReg SEE 2137
      let msz := (BitVec.slice __opcode 23 2)
      let Zm := (BitVec.slice __opcode 16 5)
      let Pg := (BitVec.slice __opcode 10 3)
      let Rn := (BitVec.slice __opcode 5 5)
      let Zt := (BitVec.slice __opcode 0 5)
      (decode_ST1D_Z_P_BZ_D_64_unscaled msz Zm Pg Rn Zt))
  else
    (do
      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100100101#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b101#3 : (BitVec 3))))) <&&> (do
           (pure ((← readReg SEE) <b 2138))))) : Bool)
      then
        (do
          writeReg SEE 2138
          let msz := (BitVec.slice __opcode 23 2)
          let Zm := (BitVec.slice __opcode 16 5)
          let Pg := (BitVec.slice __opcode 10 3)
          let Rn := (BitVec.slice __opcode 5 5)
          let Zt := (BitVec.slice __opcode 0 5)
          (decode_ST1H_Z_P_BZ_D_64_scaled msz Zm Pg Rn Zt))
      else
        (do
          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100101001#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b101#3 : (BitVec 3))))) <&&> (do
               (pure ((← readReg SEE) <b 2139))))) : Bool)
          then
            (do
              writeReg SEE 2139
              let msz := (BitVec.slice __opcode 23 2)
              let Zm := (BitVec.slice __opcode 16 5)
              let Pg := (BitVec.slice __opcode 10 3)
              let Rn := (BitVec.slice __opcode 5 5)
              let Zt := (BitVec.slice __opcode 0 5)
              (decode_ST1W_Z_P_BZ_D_64_scaled msz Zm Pg Rn Zt))
          else
            (do
              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100101101#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b101#3 : (BitVec 3))))) <&&> (do
                   (pure ((← readReg SEE) <b 2140))))) : Bool)
              then
                (do
                  writeReg SEE 2140
                  let msz := (BitVec.slice __opcode 23 2)
                  let Zm := (BitVec.slice __opcode 16 5)
                  let Pg := (BitVec.slice __opcode 10 3)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let Zt := (BitVec.slice __opcode 0 5)
                  (decode_ST1D_Z_P_BZ_D_64_scaled msz Zm Pg Rn Zt))
              else
                (do
                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100100010#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b101#3 : (BitVec 3))))) <&&> (do
                       (pure ((← readReg SEE) <b 2141))))) : Bool)
                  then
                    (do
                      writeReg SEE 2141
                      let msz := (BitVec.slice __opcode 23 2)
                      let imm5 := (BitVec.slice __opcode 16 5)
                      let Pg := (BitVec.slice __opcode 10 3)
                      let Zn := (BitVec.slice __opcode 5 5)
                      let Zt := (BitVec.slice __opcode 0 5)
                      (decode_ST1B_Z_P_AI_D msz imm5 Pg Zn Zt))
                  else
                    (do
                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100100110#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b101#3 : (BitVec 3))))) <&&> (do
                           (pure ((← readReg SEE) <b 2142))))) : Bool)
                      then
                        (do
                          writeReg SEE 2142
                          let msz := (BitVec.slice __opcode 23 2)
                          let imm5 := (BitVec.slice __opcode 16 5)
                          let Pg := (BitVec.slice __opcode 10 3)
                          let Zn := (BitVec.slice __opcode 5 5)
                          let Zt := (BitVec.slice __opcode 0 5)
                          (decode_ST1H_Z_P_AI_D msz imm5 Pg Zn Zt))
                      else
                        (do
                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100101010#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b101#3 : (BitVec 3))))) <&&> (do
                               (pure ((← readReg SEE) <b 2143))))) : Bool)
                          then
                            (do
                              writeReg SEE 2143
                              let msz := (BitVec.slice __opcode 23 2)
                              let imm5 := (BitVec.slice __opcode 16 5)
                              let Pg := (BitVec.slice __opcode 10 3)
                              let Zn := (BitVec.slice __opcode 5 5)
                              let Zt := (BitVec.slice __opcode 0 5)
                              (decode_ST1W_Z_P_AI_D msz imm5 Pg Zn Zt))
                          else
                            (do
                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100101110#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b101#3 : (BitVec 3))))) <&&> (do
                                   (pure ((← readReg SEE) <b 2144))))) : Bool)
                              then
                                (do
                                  writeReg SEE 2144
                                  let msz := (BitVec.slice __opcode 23 2)
                                  let imm5 := (BitVec.slice __opcode 16 5)
                                  let Pg := (BitVec.slice __opcode 10 3)
                                  let Zn := (BitVec.slice __opcode 5 5)
                                  let Zt := (BitVec.slice __opcode 0 5)
                                  (decode_ST1D_Z_P_AI_D msz imm5 Pg Zn Zt))
                              else
                                (do
                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100100011#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b101#3 : (BitVec 3))))) <&&> (do
                                       (pure ((← readReg SEE) <b 2145))))) : Bool)
                                  then
                                    (do
                                      writeReg SEE 2145
                                      let msz := (BitVec.slice __opcode 23 2)
                                      let imm5 := (BitVec.slice __opcode 16 5)
                                      let Pg := (BitVec.slice __opcode 10 3)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let Zt := (BitVec.slice __opcode 0 5)
                                      (decode_ST1B_Z_P_AI_S msz imm5 Pg Zn Zt))
                                  else
                                    (do
                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100100111#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b101#3 : (BitVec 3))))) <&&> (do
                                           (pure ((← readReg SEE) <b 2146))))) : Bool)
                                      then
                                        (do
                                          writeReg SEE 2146
                                          let msz := (BitVec.slice __opcode 23 2)
                                          let imm5 := (BitVec.slice __opcode 16 5)
                                          let Pg := (BitVec.slice __opcode 10 3)
                                          let Zn := (BitVec.slice __opcode 5 5)
                                          let Zt := (BitVec.slice __opcode 0 5)
                                          (decode_ST1H_Z_P_AI_S msz imm5 Pg Zn Zt))
                                      else
                                        (do
                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100101011#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b101#3 : (BitVec 3))))) <&&> (do
                                               (pure ((← readReg SEE) <b 2147))))) : Bool)
                                          then
                                            (do
                                              writeReg SEE 2147
                                              let msz := (BitVec.slice __opcode 23 2)
                                              let imm5 := (BitVec.slice __opcode 16 5)
                                              let Pg := (BitVec.slice __opcode 10 3)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let Zt := (BitVec.slice __opcode 0 5)
                                              (decode_ST1W_Z_P_AI_S msz imm5 Pg Zn Zt))
                                          else
                                            (do
                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111001000#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3)))))) <&&> (do
                                                   (pure ((← readReg SEE) <b 2148))))) : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2148
                                                  let msz := (BitVec.slice __opcode 23 2)
                                                  let size := (BitVec.slice __opcode 21 2)
                                                  let imm4 := (BitVec.slice __opcode 16 4)
                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                  (decode_ST1B_Z_P_BI__ msz size imm4 Pg Rn Zt))
                                              else
                                                (do
                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111001001#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3)))))) <&&> (do
                                                       (pure ((← readReg SEE) <b 2149))))) : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2149
                                                      let msz := (BitVec.slice __opcode 23 2)
                                                      let size := (BitVec.slice __opcode 21 2)
                                                      let imm4 := (BitVec.slice __opcode 16 4)
                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                      (decode_ST1H_Z_P_BI__ msz size imm4 Pg Rn Zt))
                                                  else
                                                    (do
                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 22) == (0b1110010101#10 : (BitVec 10))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3)))))) <&&> (do
                                                           (pure ((← readReg SEE) <b 2150))))) : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2150
                                                          let msz := (BitVec.slice __opcode 23 2)
                                                          let sz := (BitVec.slice __opcode 21 1)
                                                          let imm4 := (BitVec.slice __opcode 16 4)
                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let Zt := (BitVec.slice __opcode 0 5)
                                                          (decode_ST1W_Z_P_BI__ msz sz imm4 Pg Rn Zt))
                                                      else
                                                        (do
                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE5E#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                               (pure ((← readReg SEE) <b 2151))))) : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2151
                                                              let msz := (BitVec.slice __opcode 23 2)
                                                              let imm4 := (BitVec.slice __opcode 16 4)
                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let Zt := (BitVec.slice __opcode 0 5)
                                                              (decode_ST1D_Z_P_BI__ msz imm4 Pg Rn Zt))
                                                          else
                                                            (do
                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE50#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                   (pure ((← readReg SEE) <b 2152))))) : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2152
                                                                  let msz := (BitVec.slice __opcode 23 2)
                                                                  let imm4 := (BitVec.slice __opcode 16 4)
                                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                                  (decode_ST1W_Z_P_BI_U128 msz imm4 Pg Rn Zt))
                                                              else
                                                                (do
                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE5C#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                       (pure ((← readReg SEE) <b 2153))))) : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2153
                                                                      let msz := (BitVec.slice __opcode 23 2)
                                                                      let imm4 := (BitVec.slice __opcode 16 4)
                                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                                      (decode_ST1D_Z_P_BI_U128 msz imm4 Pg Rn Zt))
                                                                  else
                                                                    (do
                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE41#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                           (pure ((← readReg SEE) <b 2154))))) : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2154
                                                                          let msz := (BitVec.slice __opcode 23 2)
                                                                          let imm4 := (BitVec.slice __opcode 16 4)
                                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                          let Zt := (BitVec.slice __opcode 0 5)
                                                                          (decode_STNT1B_Z_P_BI_Contiguous msz imm4 Pg Rn Zt))
                                                                      else
                                                                        (do
                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE49#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                               (pure ((← readReg SEE) <b 2155))))) : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2155
                                                                              let msz := (BitVec.slice __opcode 23 2)
                                                                              let imm4 := (BitVec.slice __opcode 16 4)
                                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                              let Zt := (BitVec.slice __opcode 0 5)
                                                                              (decode_STNT1H_Z_P_BI_Contiguous msz imm4 Pg Rn Zt))
                                                                          else
                                                                            (do
                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE51#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                                   (pure ((← readReg SEE) <b 2156))))) : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2156
                                                                                  let msz := (BitVec.slice __opcode 23 2)
                                                                                  let imm4 := (BitVec.slice __opcode 16 4)
                                                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                                                  (decode_STNT1W_Z_P_BI_Contiguous msz imm4 Pg Rn Zt))
                                                                              else
                                                                                (do
                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE59#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                                       (pure ((← readReg SEE) <b 2157))))) : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2157
                                                                                      let msz := (BitVec.slice __opcode 23 2)
                                                                                      let imm4 := (BitVec.slice __opcode 16 4)
                                                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                                                      (decode_STNT1D_Z_P_BI_Contiguous msz imm4 Pg Rn Zt))
                                                                                  else
                                                                                    (do
                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE43#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                                           (pure ((← readReg SEE) <b 2158))))) : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2158
                                                                                          let msz := (BitVec.slice __opcode 23 2)
                                                                                          let imm4 := (BitVec.slice __opcode 16 4)
                                                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                          let Zt := (BitVec.slice __opcode 0 5)
                                                                                          (decode_ST2B_Z_P_BI_Contiguous msz imm4 Pg Rn Zt))
                                                                                      else
                                                                                        (do
                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE4B#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                                               (pure ((← readReg SEE) <b 2159))))) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2159
                                                                                              let msz := (BitVec.slice __opcode 23 2)
                                                                                              let imm4 := (BitVec.slice __opcode 16 4)
                                                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                              let Zt := (BitVec.slice __opcode 0 5)
                                                                                              (decode_ST2H_Z_P_BI_Contiguous msz imm4 Pg Rn Zt))
                                                                                          else
                                                                                            (do
                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE53#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                                                   (pure ((← readReg SEE) <b 2160))))) : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2160
                                                                                                  let msz := (BitVec.slice __opcode 23 2)
                                                                                                  let imm4 := (BitVec.slice __opcode 16 4)
                                                                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                                                                  (decode_ST2W_Z_P_BI_Contiguous msz imm4 Pg Rn Zt))
                                                                                              else
                                                                                                (do
                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE5B#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                                                       (pure ((← readReg SEE) <b 2161))))) : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2161
                                                                                                      let msz := (BitVec.slice __opcode 23 2)
                                                                                                      let imm4 := (BitVec.slice __opcode 16 4)
                                                                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                                                                      (decode_ST2D_Z_P_BI_Contiguous msz imm4 Pg Rn Zt))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE45#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                                                           (pure ((← readReg SEE) <b 2162))))) : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2162
                                                                                                          let msz := (BitVec.slice __opcode 23 2)
                                                                                                          let imm4 := (BitVec.slice __opcode 16 4)
                                                                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                                          let Zt := (BitVec.slice __opcode 0 5)
                                                                                                          (decode_ST3B_Z_P_BI_Contiguous msz imm4 Pg Rn Zt))
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE4D#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                                                               (pure ((← readReg SEE) <b 2163))))) : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2163
                                                                                                              let msz := (BitVec.slice __opcode 23 2)
                                                                                                              let imm4 := (BitVec.slice __opcode 16 4)
                                                                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                                              let Zt := (BitVec.slice __opcode 0 5)
                                                                                                              (decode_ST3H_Z_P_BI_Contiguous msz imm4 Pg Rn Zt))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE55#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                                                                   (pure ((← readReg SEE) <b 2164))))) : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2164
                                                                                                                  let msz := (BitVec.slice __opcode 23 2)
                                                                                                                  let imm4 := (BitVec.slice __opcode 16 4)
                                                                                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                  (decode_ST3W_Z_P_BI_Contiguous msz imm4 Pg Rn Zt))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE5D#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                                                                       (pure ((← readReg SEE) <b 2165))))) : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2165
                                                                                                                      let msz := (BitVec.slice __opcode 23 2)
                                                                                                                      let imm4 := (BitVec.slice __opcode 16 4)
                                                                                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                      (decode_ST3D_Z_P_BI_Contiguous msz imm4 Pg Rn Zt))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE47#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                                                                           (pure ((← readReg SEE) <b 2166))))) : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2166
                                                                                                                          let msz := (BitVec.slice __opcode 23 2)
                                                                                                                          let imm4 := (BitVec.slice __opcode 16 4)
                                                                                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                          let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                          (decode_ST4B_Z_P_BI_Contiguous msz imm4 Pg Rn Zt))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE4F#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                                                                               (pure ((← readReg SEE) <b 2167))))) : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2167
                                                                                                                              let msz := (BitVec.slice __opcode 23 2)
                                                                                                                              let imm4 := (BitVec.slice __opcode 16 4)
                                                                                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                              let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                              (decode_ST4H_Z_P_BI_Contiguous msz imm4 Pg Rn Zt))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE57#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                                                                                   (pure ((← readReg SEE) <b 2168))))) : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2168
                                                                                                                                  let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                  let imm4 := (BitVec.slice __opcode 16 4)
                                                                                                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                  (decode_ST4W_Z_P_BI_Contiguous msz imm4 Pg Rn Zt))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE5F#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                                                                                       (pure ((← readReg SEE) <b 2169))))) : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2169
                                                                                                                                      let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                      let imm4 := (BitVec.slice __opcode 16 4)
                                                                                                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                      (decode_ST4D_Z_P_BI_Contiguous msz imm4 Pg Rn Zt))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE44#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b000#3 : (BitVec 3))))) <&&> (do
                                                                                                                                           (pure ((← readReg SEE) <b 2170))))) : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 2170
                                                                                                                                          let num := (BitVec.slice __opcode 22 2)
                                                                                                                                          let imm4 := (BitVec.slice __opcode 16 4)
                                                                                                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                          let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                          (decode_ST2Q_Z_P_BI_Contiguous num imm4 Pg Rn Zt))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE48#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b000#3 : (BitVec 3))))) <&&> (do
                                                                                                                                               (pure ((← readReg SEE) <b 2171))))) : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 2171
                                                                                                                                              let num := (BitVec.slice __opcode 22 2)
                                                                                                                                              let imm4 := (BitVec.slice __opcode 16 4)
                                                                                                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                              let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                              (decode_ST3Q_Z_P_BI_Contiguous num imm4 Pg Rn Zt))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 20) == (0xE4C#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b000#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                   (pure ((← readReg SEE) <b 2172))))) : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 2172
                                                                                                                                                  let num := (BitVec.slice __opcode 22 2)
                                                                                                                                                  let imm4 := (BitVec.slice __opcode 16 4)
                                                                                                                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                  (decode_ST4Q_Z_P_BI_Contiguous num imm4 Pg Rn Zt))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10000100000#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b101#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                       (pure ((← readReg SEE) <b 2173))))) : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 2173
                                                                                                                                                      let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                      let U := (BitVec.slice __opcode 13 1)
                                                                                                                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                      (decode_LDNT1B_Z_P_AR_S_x32_unscaled msz Rm U Pg Zn Zt))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10000100100#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b101#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                           (pure ((← readReg SEE) <b 2174))))) : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 2174
                                                                                                                                                          let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                          let U := (BitVec.slice __opcode 13 1)
                                                                                                                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                          let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                          (decode_LDNT1H_Z_P_AR_S_x32_unscaled msz Rm U Pg Zn Zt))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10000101000#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b101#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                               (pure ((← readReg SEE) <b 2175))))) : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 2175
                                                                                                                                                              let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                              let U := (BitVec.slice __opcode 13 1)
                                                                                                                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                              let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                              (decode_LDNT1W_Z_P_AR_S_x32_unscaled msz Rm U Pg Zn Zt))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10000100000#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b100#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                   (pure ((← readReg SEE) <b 2176))))) : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 2176
                                                                                                                                                                  let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                  let U := (BitVec.slice __opcode 13 1)
                                                                                                                                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                  (decode_LDNT1SB_Z_P_AR_S_x32_unscaled msz Rm U Pg Zn Zt))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10000100100#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b100#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                       (pure ((← readReg SEE) <b 2177))))) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 2177
                                                                                                                                                                      let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                      let U := (BitVec.slice __opcode 13 1)
                                                                                                                                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                      (decode_LDNT1SH_Z_P_AR_S_x32_unscaled msz Rm U Pg Zn Zt))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11000100000#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b110#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                           (pure ((← readReg SEE) <b 2178))))) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 2178
                                                                                                                                                                          let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                          let U := (BitVec.slice __opcode 14 1)
                                                                                                                                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                          let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                          (decode_LDNT1B_Z_P_AR_D_64_unscaled msz Rm U Pg Zn Zt))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11000100100#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b110#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                               (pure ((← readReg SEE) <b 2179))))) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 2179
                                                                                                                                                                              let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                              let U := (BitVec.slice __opcode 14 1)
                                                                                                                                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                              let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                              (decode_LDNT1H_Z_P_AR_D_64_unscaled msz Rm U Pg Zn Zt))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11000101000#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b110#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                   (pure ((← readReg SEE) <b 2180))))) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 2180
                                                                                                                                                                                  let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                  let U := (BitVec.slice __opcode 14 1)
                                                                                                                                                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                  (decode_LDNT1W_Z_P_AR_D_64_unscaled msz Rm U Pg Zn Zt))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11000101100#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b110#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                       (pure ((← readReg SEE) <b 2181))))) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      writeReg SEE 2181
                                                                                                                                                                                      let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                      let U := (BitVec.slice __opcode 14 1)
                                                                                                                                                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                      (decode_LDNT1D_Z_P_AR_D_64_unscaled msz Rm U Pg Zn Zt))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11000100000#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b100#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                           (pure ((← readReg SEE) <b 2182))))) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          writeReg SEE 2182
                                                                                                                                                                                          let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                          let U := (BitVec.slice __opcode 14 1)
                                                                                                                                                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                          let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                          (decode_LDNT1SB_Z_P_AR_D_64_unscaled msz Rm U Pg Zn Zt))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11000100100#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b100#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                               (pure ((← readReg SEE) <b 2183))))) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              writeReg SEE 2183
                                                                                                                                                                                              let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                              let U := (BitVec.slice __opcode 14 1)
                                                                                                                                                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                              let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                              (decode_LDNT1SH_Z_P_AR_D_64_unscaled msz Rm U Pg Zn Zt))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11000101000#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b100#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                   (pure ((← readReg SEE) <b 2184))))) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  writeReg SEE 2184
                                                                                                                                                                                                  let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                  let U := (BitVec.slice __opcode 14 1)
                                                                                                                                                                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                  (decode_LDNT1SW_Z_P_AR_D_64_unscaled msz Rm U Pg Zn Zt))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100100010#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b001#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                       (pure ((← readReg SEE) <b 2185))))) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      writeReg SEE 2185
                                                                                                                                                                                                      let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                      (decode_STNT1B_Z_P_AR_S_x32_unscaled msz Rm Pg Zn Zt))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100100110#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b001#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                           (pure ((← readReg SEE) <b 2186))))) : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          writeReg SEE 2186
                                                                                                                                                                                                          let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                          let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                          (decode_STNT1H_Z_P_AR_S_x32_unscaled msz Rm Pg Zn Zt))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100101010#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b001#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                               (pure ((← readReg SEE) <b 2187))))) : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              writeReg SEE 2187
                                                                                                                                                                                                              let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                              let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                              (decode_STNT1W_Z_P_AR_S_x32_unscaled msz Rm Pg Zn Zt))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100100000#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b001#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 2188))))) : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  writeReg SEE 2188
                                                                                                                                                                                                                  let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                  (decode_STNT1B_Z_P_AR_D_64_unscaled msz Rm Pg Zn Zt))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100100100#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b001#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 2189))))) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      writeReg SEE 2189
                                                                                                                                                                                                                      let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                      (decode_STNT1H_Z_P_AR_D_64_unscaled msz Rm Pg Zn Zt))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100101000#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b001#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 2190))))) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          writeReg SEE 2190
                                                                                                                                                                                                                          let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                          let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                          (decode_STNT1W_Z_P_AR_D_64_unscaled msz Rm Pg Zn Zt))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100101100#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b001#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 2191))))) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              writeReg SEE 2191
                                                                                                                                                                                                                              let msz := (BitVec.slice __opcode 23 2)
                                                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                              let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                              (decode_STNT1D_Z_P_AR_D_64_unscaled msz Rm Pg Zn Zt))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11000100000#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b101#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 2192))))) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  writeReg SEE 2192
                                                                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                                                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                  (decode_LD1Q_Z_P_AR_D_64_unscaled Rm Pg Zn Zt))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11100100001#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 13) == (0b001#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 2193))))) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      writeReg SEE 2193
                                                                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                                                                                                                                                                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                      (decode_ST1Q_Z_P_AR_D_64_unscaled Rm Pg Zn Zt))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 11) == (0b000001001011111101011#21 : (BitVec 21)))) <&&> (do
                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 2727))))) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          writeReg SEE 2727
                                                                                                                                                                                                                                          let imm6 := (BitVec.slice __opcode 5 6)
                                                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                          (decode_RDSVL_R_I__ imm6 Rd))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b00000100011#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 11) == (0b01011#5 : (BitVec 5))))) <&&> (do
                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 2728))))) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              writeReg SEE 2728
                                                                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                              let imm6 := (BitVec.slice __opcode 5 6)
                                                                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                              (decode_ADDSPL_R_RI__ Rn imm6 Rd))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b00000100001#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 11) == (0b01011#5 : (BitVec 5))))) <&&> (do
                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 2729))))) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  writeReg SEE 2729
                                                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                                  let imm6 := (BitVec.slice __opcode 5 6)
                                                                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                  (decode_ADDSVL_R_RI__ Rn imm6 Rd))
                                                                                                                                                                                                                                              else (sailThrow ((Error_Undefined ())) : SailM Unit))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


