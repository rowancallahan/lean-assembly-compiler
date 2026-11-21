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
def __DecodeA64_DataProcReg (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 10) == (0b101101011000000001000#21 : (BitVec 21)))) <&&> (do
       (pure ((← readReg SEE) <b 1))))) : Bool)
  then
    (do
      writeReg SEE 1
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let sf := (BitVec.slice __opcode 31 1)
      (decode_abs_aarch64_instrs_integer_arithmetic_unary_abs Rd Rn sf))
  else
    (do
      if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011010000#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b000000#6 : (BitVec 6))))) <&&> (do
           (pure ((← readReg SEE) <b 6))))) : Bool)
      then
        (do
          writeReg SEE 6
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let Rm := (BitVec.slice __opcode 16 5)
          let S := (BitVec.slice __opcode 29 1)
          let op := (BitVec.slice __opcode 30 1)
          let sf := (BitVec.slice __opcode 31 1)
          (decode_adc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf))
      else
        (do
          if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0111010000#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b000000#6 : (BitVec 6))))) <&&> (do
               (pure ((← readReg SEE) <b 7))))) : Bool)
          then
            (do
              writeReg SEE 7
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let Rm := (BitVec.slice __opcode 16 5)
              let S := (BitVec.slice __opcode 29 1)
              let op := (BitVec.slice __opcode 30 1)
              let sf := (BitVec.slice __opcode 31 1)
              (decode_adcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf))
          else
            (do
              if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b1011010000#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b000000#6 : (BitVec 6))))) <&&> (do
                   (pure ((← readReg SEE) <b 8))))) : Bool)
              then
                (do
                  writeReg SEE 8
                  let Rd := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let Rm := (BitVec.slice __opcode 16 5)
                  let S := (BitVec.slice __opcode 29 1)
                  let op := (BitVec.slice __opcode 30 1)
                  let sf := (BitVec.slice __opcode 31 1)
                  (decode_sbc_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf))
              else
                (do
                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b1111010000#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b000000#6 : (BitVec 6))))) <&&> (do
                       (pure ((← readReg SEE) <b 9))))) : Bool)
                  then
                    (do
                      writeReg SEE 9
                      let Rd := (BitVec.slice __opcode 0 5)
                      let Rn := (BitVec.slice __opcode 5 5)
                      let Rm := (BitVec.slice __opcode 16 5)
                      let S := (BitVec.slice __opcode 29 1)
                      let op := (BitVec.slice __opcode 30 1)
                      let sf := (BitVec.slice __opcode 31 1)
                      (decode_sbcs_aarch64_instrs_integer_arithmetic_add_sub_carry Rd Rn Rm S op sf))
                  else
                    (do
                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 24) == (0b0001011#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 21 21) == (0#1 : (BitVec 1))))) <&&> (do
                           (pure ((← readReg SEE) <b 14))))) : Bool)
                      then
                        (do
                          writeReg SEE 14
                          let Rd := (BitVec.slice __opcode 0 5)
                          let Rn := (BitVec.slice __opcode 5 5)
                          let imm6 := (BitVec.slice __opcode 10 6)
                          let Rm := (BitVec.slice __opcode 16 5)
                          let shift := (BitVec.slice __opcode 22 2)
                          let S := (BitVec.slice __opcode 29 1)
                          let op := (BitVec.slice __opcode 30 1)
                          let sf := (BitVec.slice __opcode 31 1)
                          (decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf))
                      else
                        (do
                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 24) == (0b0101011#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 21 21) == (0#1 : (BitVec 1))))) <&&> (do
                               (pure ((← readReg SEE) <b 15))))) : Bool)
                          then
                            (do
                              writeReg SEE 15
                              let Rd := (BitVec.slice __opcode 0 5)
                              let Rn := (BitVec.slice __opcode 5 5)
                              let imm6 := (BitVec.slice __opcode 10 6)
                              let Rm := (BitVec.slice __opcode 16 5)
                              let shift := (BitVec.slice __opcode 22 2)
                              let S := (BitVec.slice __opcode 29 1)
                              let op := (BitVec.slice __opcode 30 1)
                              let sf := (BitVec.slice __opcode 31 1)
                              (decode_adds_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf))
                          else
                            (do
                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 24) == (0b1001011#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 21 21) == (0#1 : (BitVec 1))))) <&&> (do
                                   (pure ((← readReg SEE) <b 16))))) : Bool)
                              then
                                (do
                                  writeReg SEE 16
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let imm6 := (BitVec.slice __opcode 10 6)
                                  let Rm := (BitVec.slice __opcode 16 5)
                                  let shift := (BitVec.slice __opcode 22 2)
                                  let S := (BitVec.slice __opcode 29 1)
                                  let op := (BitVec.slice __opcode 30 1)
                                  let sf := (BitVec.slice __opcode 31 1)
                                  (decode_sub_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf))
                              else
                                (do
                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 24) == (0b1101011#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 21 21) == (0#1 : (BitVec 1))))) <&&> (do
                                       (pure ((← readReg SEE) <b 17))))) : Bool)
                                  then
                                    (do
                                      writeReg SEE 17
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let imm6 := (BitVec.slice __opcode 10 6)
                                      let Rm := (BitVec.slice __opcode 16 5)
                                      let shift := (BitVec.slice __opcode 22 2)
                                      let S := (BitVec.slice __opcode 29 1)
                                      let op := (BitVec.slice __opcode 30 1)
                                      let sf := (BitVec.slice __opcode 31 1)
                                      (decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg Rd Rn imm6 Rm shift S op sf))
                                  else
                                    (do
                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 21) == (0b0001011001#10 : (BitVec 10)))) <&&> (do
                                           (pure ((← readReg SEE) <b 22))))) : Bool)
                                      then
                                        (do
                                          writeReg SEE 22
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let imm3 := (BitVec.slice __opcode 10 3)
                                          let option_name := (BitVec.slice __opcode 13 3)
                                          let Rm := (BitVec.slice __opcode 16 5)
                                          let S := (BitVec.slice __opcode 29 1)
                                          let op := (BitVec.slice __opcode 30 1)
                                          let sf := (BitVec.slice __opcode 31 1)
                                          (decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op sf))
                                      else
                                        (do
                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 21) == (0b0101011001#10 : (BitVec 10)))) <&&> (do
                                               (pure ((← readReg SEE) <b 23))))) : Bool)
                                          then
                                            (do
                                              writeReg SEE 23
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let imm3 := (BitVec.slice __opcode 10 3)
                                              let option_name := (BitVec.slice __opcode 13 3)
                                              let Rm := (BitVec.slice __opcode 16 5)
                                              let S := (BitVec.slice __opcode 29 1)
                                              let op := (BitVec.slice __opcode 30 1)
                                              let sf := (BitVec.slice __opcode 31 1)
                                              (decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op sf))
                                          else
                                            (do
                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 21) == (0b1001011001#10 : (BitVec 10)))) <&&> (do
                                                   (pure ((← readReg SEE) <b 24))))) : Bool)
                                              then
                                                (do
                                                  writeReg SEE 24
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let imm3 := (BitVec.slice __opcode 10 3)
                                                  let option_name := (BitVec.slice __opcode 13 3)
                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                  let S := (BitVec.slice __opcode 29 1)
                                                  let op := (BitVec.slice __opcode 30 1)
                                                  let sf := (BitVec.slice __opcode 31 1)
                                                  (decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op sf))
                                              else
                                                (do
                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 21) == (0b1101011001#10 : (BitVec 10)))) <&&> (do
                                                       (pure ((← readReg SEE) <b 25))))) : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 25
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let imm3 := (BitVec.slice __opcode 10 3)
                                                      let option_name := (BitVec.slice __opcode 13 3)
                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                      let S := (BitVec.slice __opcode 29 1)
                                                      let op := (BitVec.slice __opcode 30 1)
                                                      let sf := (BitVec.slice __opcode 31 1)
                                                      (decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg Rd Rn imm3 option_name Rm S op sf))
                                                  else
                                                    (do
                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 24) == (0b0001010#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 21 21) == (0#1 : (BitVec 1))))) <&&> (do
                                                           (pure ((← readReg SEE) <b 48))))) : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 48
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let imm6 := (BitVec.slice __opcode 10 6)
                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                          let N := (BitVec.slice __opcode 21 1)
                                                          let shift := (BitVec.slice __opcode 22 2)
                                                          let opc := (BitVec.slice __opcode 29 2)
                                                          let sf := (BitVec.slice __opcode 31 1)
                                                          (decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf))
                                                      else
                                                        (do
                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 24) == (0b1101010#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 21 21) == (0#1 : (BitVec 1))))) <&&> (do
                                                               (pure ((← readReg SEE) <b 49))))) : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 49
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let imm6 := (BitVec.slice __opcode 10 6)
                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                              let N := (BitVec.slice __opcode 21 1)
                                                              let shift := (BitVec.slice __opcode 22 2)
                                                              let opc := (BitVec.slice __opcode 29 2)
                                                              let sf := (BitVec.slice __opcode 31 1)
                                                              (decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf))
                                                          else
                                                            (do
                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 24) == (0b0001010#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 21 21) == (1#1 : (BitVec 1))))) <&&> (do
                                                                   (pure ((← readReg SEE) <b 50))))) : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 50
                                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                  let imm6 := (BitVec.slice __opcode 10 6)
                                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                                  let N := (BitVec.slice __opcode 21 1)
                                                                  let shift := (BitVec.slice __opcode 22 2)
                                                                  let opc := (BitVec.slice __opcode 29 2)
                                                                  let sf := (BitVec.slice __opcode 31 1)
                                                                  (decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf))
                                                              else
                                                                (do
                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 24) == (0b1101010#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 21 21) == (1#1 : (BitVec 1))))) <&&> (do
                                                                       (pure ((← readReg SEE) <b 51))))) : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 51
                                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                      let imm6 := (BitVec.slice __opcode 10 6)
                                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                                      let N := (BitVec.slice __opcode 21 1)
                                                                      let shift := (BitVec.slice __opcode 22 2)
                                                                      let opc := (BitVec.slice __opcode 29 2)
                                                                      let sf := (BitVec.slice __opcode 31 1)
                                                                      (decode_bics_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf))
                                                                  else
                                                                    (do
                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 24) == (0b1001010#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 21 21) == (1#1 : (BitVec 1))))) <&&> (do
                                                                           (pure ((← readReg SEE) <b 52))))) : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 52
                                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                          let imm6 := (BitVec.slice __opcode 10 6)
                                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                                          let N := (BitVec.slice __opcode 21 1)
                                                                          let shift := (BitVec.slice __opcode 22 2)
                                                                          let opc := (BitVec.slice __opcode 29 2)
                                                                          let sf := (BitVec.slice __opcode 31 1)
                                                                          (decode_eon_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf))
                                                                      else
                                                                        (do
                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 24) == (0b1001010#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 21 21) == (0#1 : (BitVec 1))))) <&&> (do
                                                                               (pure ((← readReg SEE) <b 53))))) : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 53
                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                              let imm6 := (BitVec.slice __opcode 10 6)
                                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                                              let N := (BitVec.slice __opcode 21 1)
                                                                              let shift := (BitVec.slice __opcode 22 2)
                                                                              let opc := (BitVec.slice __opcode 29 2)
                                                                              let sf := (BitVec.slice __opcode 31 1)
                                                                              (decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf))
                                                                          else
                                                                            (do
                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 24) == (0b0101010#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 21 21) == (1#1 : (BitVec 1))))) <&&> (do
                                                                                   (pure ((← readReg SEE) <b 54))))) : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 54
                                                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                  let imm6 := (BitVec.slice __opcode 10 6)
                                                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                                                  let N := (BitVec.slice __opcode 21 1)
                                                                                  let shift := (BitVec.slice __opcode 22 2)
                                                                                  let opc := (BitVec.slice __opcode 29 2)
                                                                                  let sf := (BitVec.slice __opcode 31 1)
                                                                                  (decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf))
                                                                              else
                                                                                (do
                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 24) == (0b0101010#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 21 21) == (0#1 : (BitVec 1))))) <&&> (do
                                                                                       (pure ((← readReg SEE) <b 55))))) : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 55
                                                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                                      let imm6 := (BitVec.slice __opcode 10 6)
                                                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                                                      let N := (BitVec.slice __opcode 21 1)
                                                                                      let shift := (BitVec.slice __opcode 22 2)
                                                                                      let opc := (BitVec.slice __opcode 29 2)
                                                                                      let sf := (BitVec.slice __opcode 31 1)
                                                                                      (decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg Rd Rn imm6 Rm N shift opc sf))
                                                                                  else
                                                                                    (do
                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b001010#6 : (BitVec 6))))) <&&> (do
                                                                                           (pure ((← readReg SEE) <b 56))))) : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 56
                                                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                          let op2 := (BitVec.slice __opcode 10 2)
                                                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                                                          let sf := (BitVec.slice __opcode 31 1)
                                                                                          (decode_asrv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm sf))
                                                                                      else
                                                                                        (do
                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b001000#6 : (BitVec 6))))) <&&> (do
                                                                                               (pure ((← readReg SEE) <b 57))))) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 57
                                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                              let op2 := (BitVec.slice __opcode 10 2)
                                                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                                                              let sf := (BitVec.slice __opcode 31 1)
                                                                                              (decode_lslv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm sf))
                                                                                          else
                                                                                            (do
                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b001001#6 : (BitVec 6))))) <&&> (do
                                                                                                   (pure ((← readReg SEE) <b 58))))) : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 58
                                                                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                                  let op2 := (BitVec.slice __opcode 10 2)
                                                                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                                                                  let sf := (BitVec.slice __opcode 31 1)
                                                                                                  (decode_lsrv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm sf))
                                                                                              else
                                                                                                (do
                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b001011#6 : (BitVec 6))))) <&&> (do
                                                                                                       (pure ((← readReg SEE) <b 59))))) : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 59
                                                                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                                                      let op2 := (BitVec.slice __opcode 10 2)
                                                                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                                                                      let sf := (BitVec.slice __opcode 31 1)
                                                                                                      (decode_rorv_aarch64_instrs_integer_shift_variable Rd Rn op2 Rm sf))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 14) == (0b110110101100000100#18 : (BitVec 18))) && ((Sail.BitVec.extractLsb __opcode 12 10) == (0b110#3 : (BitVec 3))))) <&&> (do
                                                                                                           (pure ((← readReg SEE) <b 60))))) : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 60
                                                                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                                          let Z := (BitVec.slice __opcode 13 1)
                                                                                                          (decode_autda_aarch64_instrs_integer_pac_autda_dp_1src Rd Rn Z))
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 14) == (0b110110101100000100#18 : (BitVec 18))) && ((Sail.BitVec.extractLsb __opcode 12 10) == (0b111#3 : (BitVec 3))))) <&&> (do
                                                                                                               (pure ((← readReg SEE) <b 61))))) : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 61
                                                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                                              let Z := (BitVec.slice __opcode 13 1)
                                                                                                              (decode_autdb_aarch64_instrs_integer_pac_autdb_dp_1src Rd Rn Z))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 14) == (0b110110101100000100#18 : (BitVec 18))) && ((Sail.BitVec.extractLsb __opcode 12 10) == (0b100#3 : (BitVec 3))))) <&&> (do
                                                                                                                   (pure ((← readReg SEE) <b 62))))) : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 62
                                                                                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                  let Z := (BitVec.slice __opcode 13 1)
                                                                                                                  (decode_autia_aarch64_instrs_integer_pac_autia_dp_1src Rd Rn Z))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 14) == (0b110110101100000100#18 : (BitVec 18))) && ((Sail.BitVec.extractLsb __opcode 12 10) == (0b101#3 : (BitVec 3))))) <&&> (do
                                                                                                                       (pure ((← readReg SEE) <b 64))))) : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 64
                                                                                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                      let Z := (BitVec.slice __opcode 13 1)
                                                                                                                      (decode_autib_aarch64_instrs_integer_pac_autib_dp_1src Rd Rn Z))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0111010010#10 : (BitVec 10))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))) <&&> (do
                                                                                                                           (pure ((← readReg SEE) <b 119))))) : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 119
                                                                                                                          let nzcv := (BitVec.slice __opcode 0 4)
                                                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                          let cond := (BitVec.slice __opcode 12 4)
                                                                                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                          let op := (BitVec.slice __opcode 30 1)
                                                                                                                          let sf := (BitVec.slice __opcode 31 1)
                                                                                                                          (decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register nzcv Rn cond Rm op sf))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b1111010010#10 : (BitVec 10))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))) <&&> (do
                                                                                                                               (pure ((← readReg SEE) <b 120))))) : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 120
                                                                                                                              let nzcv := (BitVec.slice __opcode 0 4)
                                                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                              let cond := (BitVec.slice __opcode 12 4)
                                                                                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                              let op := (BitVec.slice __opcode 30 1)
                                                                                                                              let sf := (BitVec.slice __opcode 31 1)
                                                                                                                              (decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register nzcv Rn cond Rm op sf))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0111010010#10 : (BitVec 10))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))) <&&> (do
                                                                                                                                   (pure ((← readReg SEE) <b 121))))) : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 121
                                                                                                                                  let nzcv := (BitVec.slice __opcode 0 4)
                                                                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                  let cond := (BitVec.slice __opcode 12 4)
                                                                                                                                  let imm5 := (BitVec.slice __opcode 16 5)
                                                                                                                                  let op := (BitVec.slice __opcode 30 1)
                                                                                                                                  let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                  (decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate nzcv Rn cond imm5 op sf))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b1111010010#10 : (BitVec 10))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))) <&&> (do
                                                                                                                                       (pure ((← readReg SEE) <b 122))))) : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 122
                                                                                                                                      let nzcv := (BitVec.slice __opcode 0 4)
                                                                                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                      let cond := (BitVec.slice __opcode 12 4)
                                                                                                                                      let imm5 := (BitVec.slice __opcode 16 5)
                                                                                                                                      let op := (BitVec.slice __opcode 30 1)
                                                                                                                                      let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                      (decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate nzcv Rn cond imm5 op sf))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 10) == (0b101101011000000000101#21 : (BitVec 21)))) <&&> (do
                                                                                                                                           (pure ((← readReg SEE) <b 127))))) : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 127
                                                                                                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                          let op := (BitVec.slice __opcode 10 1)
                                                                                                                                          let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                          (decode_cls_int_aarch64_instrs_integer_arithmetic_cnt Rd Rn op sf))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 10) == (0b101101011000000000100#21 : (BitVec 21)))) <&&> (do
                                                                                                                                               (pure ((← readReg SEE) <b 128))))) : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 128
                                                                                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                              let op := (BitVec.slice __opcode 10 1)
                                                                                                                                              let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                              (decode_clz_int_aarch64_instrs_integer_arithmetic_cnt Rd Rn op sf))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 10) == (0b101101011000000000111#21 : (BitVec 21)))) <&&> (do
                                                                                                                                                   (pure ((← readReg SEE) <b 151))))) : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 151
                                                                                                                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                  let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                  (decode_cnt_aarch64_instrs_integer_arithmetic_unary_cnt Rd Rn sf))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 12) == (0x4#4 : (BitVec 4))))) <&&> (do
                                                                                                                                                       (pure ((← readReg SEE) <b 185))))) : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 185
                                                                                                                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                      let sz := (BitVec.slice __opcode 10 2)
                                                                                                                                                      let C := (BitVec.slice __opcode 12 1)
                                                                                                                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                      let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                      (decode_crc32_aarch64_instrs_integer_crc Rd Rn sz C Rm sf))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 12) == (0x5#4 : (BitVec 4))))) <&&> (do
                                                                                                                                                           (pure ((← readReg SEE) <b 186))))) : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 186
                                                                                                                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                          let sz := (BitVec.slice __opcode 10 2)
                                                                                                                                                          let C := (BitVec.slice __opcode 12 1)
                                                                                                                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                          let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                          (decode_crc32c_aarch64_instrs_integer_crc Rd Rn sz C Rm sf))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011010100#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 11 10) == (0b00#2 : (BitVec 2))))) <&&> (do
                                                                                                                                                               (pure ((← readReg SEE) <b 187))))) : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 187
                                                                                                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                              let o2 := (BitVec.slice __opcode 10 1)
                                                                                                                                                              let cond := (BitVec.slice __opcode 12 4)
                                                                                                                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                              let op := (BitVec.slice __opcode 30 1)
                                                                                                                                                              let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                              (decode_csel_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011010100#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 11 10) == (0b01#2 : (BitVec 2))))) <&&> (do
                                                                                                                                                                   (pure ((← readReg SEE) <b 188))))) : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 188
                                                                                                                                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                  let o2 := (BitVec.slice __opcode 10 1)
                                                                                                                                                                  let cond := (BitVec.slice __opcode 12 4)
                                                                                                                                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                  let op := (BitVec.slice __opcode 30 1)
                                                                                                                                                                  let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                  (decode_csinc_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b1011010100#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 11 10) == (0b00#2 : (BitVec 2))))) <&&> (do
                                                                                                                                                                       (pure ((← readReg SEE) <b 189))))) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 189
                                                                                                                                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                      let o2 := (BitVec.slice __opcode 10 1)
                                                                                                                                                                      let cond := (BitVec.slice __opcode 12 4)
                                                                                                                                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                      let op := (BitVec.slice __opcode 30 1)
                                                                                                                                                                      let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                      (decode_csinv_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b1011010100#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 11 10) == (0b01#2 : (BitVec 2))))) <&&> (do
                                                                                                                                                                           (pure ((← readReg SEE) <b 190))))) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 190
                                                                                                                                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                          let o2 := (BitVec.slice __opcode 10 1)
                                                                                                                                                                          let cond := (BitVec.slice __opcode 12 4)
                                                                                                                                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                          let op := (BitVec.slice __opcode 30 1)
                                                                                                                                                                          let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                          (decode_csneg_aarch64_instrs_integer_conditional_select Rd Rn o2 cond Rm op sf))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 10) == (0b101101011000000000110#21 : (BitVec 21)))) <&&> (do
                                                                                                                                                                               (pure ((← readReg SEE) <b 191))))) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 191
                                                                                                                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                              let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                              (decode_ctz_aarch64_instrs_integer_arithmetic_unary_ctz Rd Rn sf))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10011010110#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b000101#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                   (pure ((← readReg SEE) <b 477))))) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 477
                                                                                                                                                                                  let Xd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                  let Xn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                  let Xm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                  (decode_gmi_aarch64_instrs_integer_tags_mcinserttagmask Xd Xn Xm))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10011010110#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b000100#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                       (pure ((← readReg SEE) <b 482))))) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      writeReg SEE 482
                                                                                                                                                                                      let Xd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                      let Xn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                      let Xm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                      (decode_irg_aarch64_instrs_integer_tags_mcinsertrandomtag Xd Xn Xm))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011011000#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 15) == (0#1 : (BitVec 1))))) <&&> (do
                                                                                                                                                                                           (pure ((← readReg SEE) <b 690))))) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          writeReg SEE 690
                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                          let Ra := (BitVec.slice __opcode 10 5)
                                                                                                                                                                                          let o0 := (BitVec.slice __opcode 15 1)
                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                          let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                                          (decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub Rd Rn Ra o0 Rm sf))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011011000#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 15) == (1#1 : (BitVec 1))))) <&&> (do
                                                                                                                                                                                               (pure ((← readReg SEE) <b 691))))) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              writeReg SEE 691
                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                              let Ra := (BitVec.slice __opcode 10 5)
                                                                                                                                                                                              let o0 := (BitVec.slice __opcode 15 1)
                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                              let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                                              (decode_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub Rd Rn Ra o0 Rm sf))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 14) == (0b110110101100000100#18 : (BitVec 18))) && ((Sail.BitVec.extractLsb __opcode 12 10) == (0b010#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                   (pure ((← readReg SEE) <b 708))))) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  writeReg SEE 708
                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                  let Z := (BitVec.slice __opcode 13 1)
                                                                                                                                                                                                  (decode_pacda_aarch64_instrs_integer_pac_pacda_dp_1src Rd Rn Z))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 14) == (0b110110101100000100#18 : (BitVec 18))) && ((Sail.BitVec.extractLsb __opcode 12 10) == (0b011#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                       (pure ((← readReg SEE) <b 709))))) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      writeReg SEE 709
                                                                                                                                                                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                      let Z := (BitVec.slice __opcode 13 1)
                                                                                                                                                                                                      (decode_pacdb_aarch64_instrs_integer_pac_pacdb_dp_1src Rd Rn Z))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10011010110#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b001100#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                           (pure ((← readReg SEE) <b 710))))) : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          writeReg SEE 710
                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                          (decode_pacga_aarch64_instrs_integer_pac_pacga_dp_2src Rd Rn Rm))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 14) == (0b110110101100000100#18 : (BitVec 18))) && ((Sail.BitVec.extractLsb __opcode 12 10) == (0b000#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                               (pure ((← readReg SEE) <b 711))))) : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              writeReg SEE 711
                                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                              let Z := (BitVec.slice __opcode 13 1)
                                                                                                                                                                                                              (decode_pacia_aarch64_instrs_integer_pac_pacia_dp_1src Rd Rn Z))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 14) == (0b110110101100000100#18 : (BitVec 18))) && ((Sail.BitVec.extractLsb __opcode 12 10) == (0b001#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 713))))) : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  writeReg SEE 713
                                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                  let Z := (BitVec.slice __opcode 13 1)
                                                                                                                                                                                                                  (decode_pacib_aarch64_instrs_integer_pac_pacib_dp_1src Rd Rn Z))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 10) == (0b101101011000000000000#21 : (BitVec 21)))) <&&> (do
                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 719))))) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      writeReg SEE 719
                                                                                                                                                                                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                      let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                                                                      (decode_rbit_int_aarch64_instrs_integer_arithmetic_rbit Rd Rn sf))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 11) == (0xB5801#20 : (BitVec 20)))) <&&> (do
                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 736))))) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          writeReg SEE 736
                                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                          let opc := (BitVec.slice __opcode 10 2)
                                                                                                                                                                                                                          let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                                                                          (decode_rev_aarch64_instrs_integer_arithmetic_rev Rd Rn opc sf))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 10) == (0b101101011000000000001#21 : (BitVec 21)))) <&&> (do
                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 737))))) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              writeReg SEE 737
                                                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                              let opc := (BitVec.slice __opcode 10 2)
                                                                                                                                                                                                                              let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                                                                              (decode_rev16_int_aarch64_instrs_integer_arithmetic_rev Rd Rn opc sf))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 10) == (0b1101101011000000000010#22 : (BitVec 22)))) <&&> (do
                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 738))))) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  writeReg SEE 738
                                                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                  let opc := (BitVec.slice __opcode 10 2)
                                                                                                                                                                                                                                  let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                                                                                  (decode_rev32_int_aarch64_instrs_integer_arithmetic_rev Rd Rn opc sf))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10111010000#11 : (BitVec 11))) && (((Sail.BitVec.extractLsb __opcode 14 10) == (0b00001#5 : (BitVec 5))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))) <&&> (do
                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 742))))) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      writeReg SEE 742
                                                                                                                                                                                                                                      let mask := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                      let imm6 := (BitVec.slice __opcode 15 6)
                                                                                                                                                                                                                                      let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                                                                                      (decode_rmif_aarch64_instrs_integer_flags_rmif mask Rn imm6 sf))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b000011#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 781))))) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          writeReg SEE 781
                                                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                          let o1 := (BitVec.slice __opcode 10 1)
                                                                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                          let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                                                                                          (decode_sdiv_aarch64_instrs_integer_arithmetic_div Rd Rn o1 Rm sf))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b000010#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 782))))) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              writeReg SEE 782
                                                                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                              let o1 := (BitVec.slice __opcode 10 1)
                                                                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                              let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                                                                                              (decode_udiv_aarch64_instrs_integer_arithmetic_div Rd Rn o1 Rm sf))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 15) == (0b00111010000000000#17 : (BitVec 17))) && (((Sail.BitVec.extractLsb __opcode 13 10) == (0x2#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b01101#5 : (BitVec 5)))))) <&&> (do
                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 791))))) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  writeReg SEE 791
                                                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                                  let sz := (BitVec.slice __opcode 14 1)
                                                                                                                                                                                                                                                  let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                                                                                                  (decode_setf_aarch64_instrs_integer_flags_setf Rn sz sf))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10011011001#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 15) == (0#1 : (BitVec 1))))) <&&> (do
                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 828))))) : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      writeReg SEE 828
                                                                                                                                                                                                                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                                      let Ra := (BitVec.slice __opcode 10 5)
                                                                                                                                                                                                                                                      let o0 := (BitVec.slice __opcode 15 1)
                                                                                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                                      let U := (BitVec.slice __opcode 23 1)
                                                                                                                                                                                                                                                      (decode_smaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10011011001#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 15) == (1#1 : (BitVec 1))))) <&&> (do
                                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 829))))) : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          writeReg SEE 829
                                                                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                                          let Ra := (BitVec.slice __opcode 10 5)
                                                                                                                                                                                                                                                          let o0 := (BitVec.slice __opcode 15 1)
                                                                                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                                          let U := (BitVec.slice __opcode 23 1)
                                                                                                                                                                                                                                                          (decode_smsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10011011101#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 15) == (0#1 : (BitVec 1))))) <&&> (do
                                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 830))))) : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              writeReg SEE 830
                                                                                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                                              let Ra := (BitVec.slice __opcode 10 5)
                                                                                                                                                                                                                                                              let o0 := (BitVec.slice __opcode 15 1)
                                                                                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                                              let U := (BitVec.slice __opcode 23 1)
                                                                                                                                                                                                                                                              (decode_umaddl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10011011101#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 15) == (1#1 : (BitVec 1))))) <&&> (do
                                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 831))))) : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  writeReg SEE 831
                                                                                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                                                  let Ra := (BitVec.slice __opcode 10 5)
                                                                                                                                                                                                                                                                  let o0 := (BitVec.slice __opcode 15 1)
                                                                                                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                                                  let U := (BitVec.slice __opcode 23 1)
                                                                                                                                                                                                                                                                  (decode_umsubl_aarch64_instrs_integer_arithmetic_mul_widening_32_64 Rd Rn Ra o0 Rm U))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b011000#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 833))))) : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      writeReg SEE 833
                                                                                                                                                                                                                                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                                                      let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                                                                                                                      (decode_smax_reg_aarch64_instrs_integer_arithmetic_max_min_smax_reg Rd Rn Rm sf))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b011010#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 848))))) : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          writeReg SEE 848
                                                                                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                                                          let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                                                                                                                          (decode_smin_reg_aarch64_instrs_integer_arithmetic_max_min_smin_reg Rd Rn Rm sf))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10011011010#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b011111#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 861))))) : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              writeReg SEE 861
                                                                                                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                                                              let Ra := (BitVec.slice __opcode 10 5)
                                                                                                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                                                              let U := (BitVec.slice __opcode 23 1)
                                                                                                                                                                                                                                                                              if (((((((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 12)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 13)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 14)]) != 1#1)) : Bool)
                                                                                                                                                                                                                                                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                                              else (decode_smulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn Ra Rm U))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10011011110#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b011111#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 862))))) : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  writeReg SEE 862
                                                                                                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                                                                  let Ra := (BitVec.slice __opcode 10 5)
                                                                                                                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                                                                  let U := (BitVec.slice __opcode 23 1)
                                                                                                                                                                                                                                                                                  if (((((((BitVec.join1 [(BitVec.access __opcode 10)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 12)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 13)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 14)]) != 1#1)) : Bool)
                                                                                                                                                                                                                                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                                                  else (decode_umulh_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi Rd Rn Ra Rm U))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10011010110#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b000000#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 991))))) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      writeReg SEE 991
                                                                                                                                                                                                                                                                                      let Xd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                                                      let Xn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                                                                      let Xm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                                                                      (decode_subp_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddress Xd Xn Xm))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b10111010110#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b000000#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 992))))) : Bool)
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          writeReg SEE 992
                                                                                                                                                                                                                                                                                          let Xd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                                                          let Xn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                                                                          let Xm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                                                                          (decode_subps_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags Xd Xn Xm))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b011001#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 1019))))) : Bool)
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              writeReg SEE 1019
                                                                                                                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                                                                              let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                                                                                                                                              (decode_umax_reg_aarch64_instrs_integer_arithmetic_max_min_umax_reg Rd Rn Rm sf))
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 21) == (0b0011010110#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 10) == (0b011011#6 : (BitVec 6))))) <&&> (do
                                                                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 1020))))) : Bool)
                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  writeReg SEE 1020
                                                                                                                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 16 5)
                                                                                                                                                                                                                                                                                                  let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                                                                                                                                                                                  (decode_umin_reg_aarch64_instrs_integer_arithmetic_max_min_umin_reg Rd Rn Rm sf))
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 11) == (0b110110101100000101000#21 : (BitVec 21))) && ((Sail.BitVec.extractLsb __opcode 9 5) == (0b11111#5 : (BitVec 5))))) <&&> (do
                                                                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 1032))))) : Bool)
                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      writeReg SEE 1032
                                                                                                                                                                                                                                                                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                                                                                                                                                      let D := (BitVec.slice __opcode 10 1)
                                                                                                                                                                                                                                                                                                      (decode_xpac_aarch64_instrs_integer_pac_strip_dp_1src Rd Rn D))
                                                                                                                                                                                                                                                                                                  else (sailThrow ((Error_Undefined ())) : SailM Unit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


