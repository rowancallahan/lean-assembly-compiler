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
def __DecodeA64_Reserved (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 16) == (0x0000#16 : (BitVec 16)))) <&&> (do
       (pure ((← readReg SEE) <b 1017))))) : Bool)
  then
    (do
      writeReg SEE 1017
      let imm16 := (BitVec.slice __opcode 0 16)
      (decode_udf_perm_undef_aarch64_instrs_udf imm16))
  else (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: x_0 : Int -/
def __DecodeA64_Unallocated1 (x_0 : Int) (x_1 : (BitVec 32)) : SailM Unit := do
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: x_0 : Int -/
def __DecodeA64_Unallocated2 (x_0 : Int) (x_1 : (BitVec 32)) : SailM Unit := do
  (sailThrow ((Error_Undefined ())) : SailM Unit)

/-- Type quantifiers: pc : Int -/
def __DecodeA64_DataProcImm (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 23) == (0x22#8 : (BitVec 8)))) <&&> (do
       (pure ((← readReg SEE) <b 18))))) : Bool)
  then
    (do
      writeReg SEE 18
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let imm12 := (BitVec.slice __opcode 10 12)
      let sh := (BitVec.slice __opcode 22 1)
      let S := (BitVec.slice __opcode 29 1)
      let op := (BitVec.slice __opcode 30 1)
      let sf := (BitVec.slice __opcode 31 1)
      (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf))
  else
    (do
      if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 23) == (0x62#8 : (BitVec 8)))) <&&> (do
           (pure ((← readReg SEE) <b 19))))) : Bool)
      then
        (do
          writeReg SEE 19
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let imm12 := (BitVec.slice __opcode 10 12)
          let sh := (BitVec.slice __opcode 22 1)
          let S := (BitVec.slice __opcode 29 1)
          let op := (BitVec.slice __opcode 30 1)
          let sf := (BitVec.slice __opcode 31 1)
          (decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf))
      else
        (do
          if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 23) == (0xA2#8 : (BitVec 8)))) <&&> (do
               (pure ((← readReg SEE) <b 20))))) : Bool)
          then
            (do
              writeReg SEE 20
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let imm12 := (BitVec.slice __opcode 10 12)
              let sh := (BitVec.slice __opcode 22 1)
              let S := (BitVec.slice __opcode 29 1)
              let op := (BitVec.slice __opcode 30 1)
              let sf := (BitVec.slice __opcode 31 1)
              (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf))
          else
            (do
              if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 23) == (0xE2#8 : (BitVec 8)))) <&&> (do
                   (pure ((← readReg SEE) <b 21))))) : Bool)
              then
                (do
                  writeReg SEE 21
                  let Rd := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let imm12 := (BitVec.slice __opcode 10 12)
                  let sh := (BitVec.slice __opcode 22 1)
                  let S := (BitVec.slice __opcode 29 1)
                  let op := (BitVec.slice __opcode 30 1)
                  let sf := (BitVec.slice __opcode 31 1)
                  (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op sf))
              else
                (do
                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 22) == (0b1001000110#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 14) == (0b00#2 : (BitVec 2))))) <&&> (do
                       (pure ((← readReg SEE) <b 26))))) : Bool)
                  then
                    (do
                      writeReg SEE 26
                      let Xd := (BitVec.slice __opcode 0 5)
                      let Xn := (BitVec.slice __opcode 5 5)
                      let uimm4 := (BitVec.slice __opcode 10 4)
                      let op3 := (BitVec.slice __opcode 14 2)
                      let uimm6 := (BitVec.slice __opcode 16 6)
                      if ((((BitVec.join1 [(BitVec.access __opcode 14)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 15)]) != 0#1)) : Bool)
                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                      else (decode_addg_aarch64_instrs_integer_tags_mcaddtag Xd Xn uimm4 op3 uimm6))
                  else
                    (do
                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 31) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 28 24) == (0b10000#5 : (BitVec 5))))) <&&> (do
                           (pure ((← readReg SEE) <b 34))))) : Bool)
                      then
                        (do
                          writeReg SEE 34
                          let Rd := (BitVec.slice __opcode 0 5)
                          let immhi := (BitVec.slice __opcode 5 19)
                          let immlo := (BitVec.slice __opcode 29 2)
                          let op := (BitVec.slice __opcode 31 1)
                          (decode_adr_aarch64_instrs_integer_arithmetic_address_pc_rel Rd immhi immlo op))
                      else
                        (do
                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 31) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 28 24) == (0b10000#5 : (BitVec 5))))) <&&> (do
                               (pure ((← readReg SEE) <b 35))))) : Bool)
                          then
                            (do
                              writeReg SEE 35
                              let Rd := (BitVec.slice __opcode 0 5)
                              let immhi := (BitVec.slice __opcode 5 19)
                              let immlo := (BitVec.slice __opcode 29 2)
                              let op := (BitVec.slice __opcode 31 1)
                              (decode_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel Rd immhi immlo op))
                          else
                            (do
                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 23) == (0x24#8 : (BitVec 8)))) <&&> (do
                                   (pure ((← readReg SEE) <b 40))))) : Bool)
                              then
                                (do
                                  writeReg SEE 40
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let imms := (BitVec.slice __opcode 10 6)
                                  let immr := (BitVec.slice __opcode 16 6)
                                  let N := (BitVec.slice __opcode 22 1)
                                  let opc := (BitVec.slice __opcode 29 2)
                                  let sf := (BitVec.slice __opcode 31 1)
                                  (decode_and_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc sf))
                              else
                                (do
                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 23) == (0xE4#8 : (BitVec 8)))) <&&> (do
                                       (pure ((← readReg SEE) <b 41))))) : Bool)
                                  then
                                    (do
                                      writeReg SEE 41
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let imms := (BitVec.slice __opcode 10 6)
                                      let immr := (BitVec.slice __opcode 16 6)
                                      let N := (BitVec.slice __opcode 22 1)
                                      let opc := (BitVec.slice __opcode 29 2)
                                      let sf := (BitVec.slice __opcode 31 1)
                                      (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc sf))
                                  else
                                    (do
                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 23) == (0xA4#8 : (BitVec 8)))) <&&> (do
                                           (pure ((← readReg SEE) <b 42))))) : Bool)
                                      then
                                        (do
                                          writeReg SEE 42
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let imms := (BitVec.slice __opcode 10 6)
                                          let immr := (BitVec.slice __opcode 16 6)
                                          let N := (BitVec.slice __opcode 22 1)
                                          let opc := (BitVec.slice __opcode 29 2)
                                          let sf := (BitVec.slice __opcode 31 1)
                                          (decode_eor_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc sf))
                                      else
                                        (do
                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 23) == (0x64#8 : (BitVec 8)))) <&&> (do
                                               (pure ((← readReg SEE) <b 43))))) : Bool)
                                          then
                                            (do
                                              writeReg SEE 43
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let imms := (BitVec.slice __opcode 10 6)
                                              let immr := (BitVec.slice __opcode 16 6)
                                              let N := (BitVec.slice __opcode 22 1)
                                              let opc := (BitVec.slice __opcode 29 2)
                                              let sf := (BitVec.slice __opcode 31 1)
                                              (decode_orr_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn imms immr N opc sf))
                                          else
                                            (do
                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 23) == (0x66#8 : (BitVec 8)))) <&&> (do
                                                   (pure ((← readReg SEE) <b 76))))) : Bool)
                                              then
                                                (do
                                                  writeReg SEE 76
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let imms := (BitVec.slice __opcode 10 6)
                                                  let immr := (BitVec.slice __opcode 16 6)
                                                  let N := (BitVec.slice __opcode 22 1)
                                                  let opc := (BitVec.slice __opcode 29 2)
                                                  let sf := (BitVec.slice __opcode 31 1)
                                                  (decode_bfm_aarch64_instrs_integer_bitfield Rd Rn imms immr N opc sf))
                                              else
                                                (do
                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 23) == (0x26#8 : (BitVec 8)))) <&&> (do
                                                       (pure ((← readReg SEE) <b 77))))) : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 77
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let imms := (BitVec.slice __opcode 10 6)
                                                      let immr := (BitVec.slice __opcode 16 6)
                                                      let N := (BitVec.slice __opcode 22 1)
                                                      let opc := (BitVec.slice __opcode 29 2)
                                                      let sf := (BitVec.slice __opcode 31 1)
                                                      (decode_sbfm_aarch64_instrs_integer_bitfield Rd Rn imms immr N opc sf))
                                                  else
                                                    (do
                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 23) == (0xA6#8 : (BitVec 8)))) <&&> (do
                                                           (pure ((← readReg SEE) <b 78))))) : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 78
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let imms := (BitVec.slice __opcode 10 6)
                                                          let immr := (BitVec.slice __opcode 16 6)
                                                          let N := (BitVec.slice __opcode 22 1)
                                                          let opc := (BitVec.slice __opcode 29 2)
                                                          let sf := (BitVec.slice __opcode 31 1)
                                                          (decode_ubfm_aarch64_instrs_integer_bitfield Rd Rn imms immr N opc sf))
                                                      else
                                                        (do
                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 30 23) == (0x27#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 21 21) == (0#1 : (BitVec 1))))) <&&> (do
                                                               (pure ((← readReg SEE) <b 206))))) : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 206
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let imms := (BitVec.slice __opcode 10 6)
                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                              let N := (BitVec.slice __opcode 22 1)
                                                              let sf := (BitVec.slice __opcode 31 1)
                                                              (decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate Rd Rn imms Rm N sf))
                                                          else
                                                            (do
                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 23) == (0xE5#8 : (BitVec 8)))) <&&> (do
                                                                   (pure ((← readReg SEE) <b 696))))) : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 696
                                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                                  let imm16 := (BitVec.slice __opcode 5 16)
                                                                  let hw := (BitVec.slice __opcode 21 2)
                                                                  let opc := (BitVec.slice __opcode 29 2)
                                                                  let sf := (BitVec.slice __opcode 31 1)
                                                                  (decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc sf))
                                                              else
                                                                (do
                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 23) == (0x25#8 : (BitVec 8)))) <&&> (do
                                                                       (pure ((← readReg SEE) <b 697))))) : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 697
                                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                                      let imm16 := (BitVec.slice __opcode 5 16)
                                                                      let hw := (BitVec.slice __opcode 21 2)
                                                                      let opc := (BitVec.slice __opcode 29 2)
                                                                      let sf := (BitVec.slice __opcode 31 1)
                                                                      (decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc sf))
                                                                  else
                                                                    (do
                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 23) == (0xA5#8 : (BitVec 8)))) <&&> (do
                                                                           (pure ((← readReg SEE) <b 698))))) : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 698
                                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                                          let imm16 := (BitVec.slice __opcode 5 16)
                                                                          let hw := (BitVec.slice __opcode 21 2)
                                                                          let opc := (BitVec.slice __opcode 29 2)
                                                                          let sf := (BitVec.slice __opcode 31 1)
                                                                          (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc sf))
                                                                      else
                                                                        (do
                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 18) == (0b0010001110000#13 : (BitVec 13)))) <&&> (do
                                                                               (pure ((← readReg SEE) <b 832))))) : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 832
                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                              let imm8 := (BitVec.slice __opcode 10 8)
                                                                              let sf := (BitVec.slice __opcode 31 1)
                                                                              (decode_smax_imm_aarch64_instrs_integer_arithmetic_max_min_smax_imm Rd Rn imm8 sf))
                                                                          else
                                                                            (do
                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 18) == (0b0010001110010#13 : (BitVec 13)))) <&&> (do
                                                                                   (pure ((← readReg SEE) <b 847))))) : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 847
                                                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                                                  let imm8 := (BitVec.slice __opcode 10 8)
                                                                                  let sf := (BitVec.slice __opcode 31 1)
                                                                                  (decode_smin_imm_aarch64_instrs_integer_arithmetic_max_min_smin_imm Rd Rn imm8 sf))
                                                                              else
                                                                                (do
                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 22) == (0b1101000110#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb __opcode 15 14) == (0b00#2 : (BitVec 2))))) <&&> (do
                                                                                       (pure ((← readReg SEE) <b 990))))) : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 990
                                                                                      let Xd := (BitVec.slice __opcode 0 5)
                                                                                      let Xn := (BitVec.slice __opcode 5 5)
                                                                                      let uimm4 := (BitVec.slice __opcode 10 4)
                                                                                      let op3 := (BitVec.slice __opcode 14 2)
                                                                                      let uimm6 := (BitVec.slice __opcode 16 6)
                                                                                      if ((((BitVec.join1 [(BitVec.access __opcode 14)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 15)]) != 0#1)) : Bool)
                                                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                      else (decode_subg_aarch64_instrs_integer_tags_mcsubtag Xd Xn uimm4 op3 uimm6))
                                                                                  else
                                                                                    (do
                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 18) == (0b0010001110001#13 : (BitVec 13)))) <&&> (do
                                                                                           (pure ((← readReg SEE) <b 1018))))) : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1018
                                                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                          let imm8 := (BitVec.slice __opcode 10 8)
                                                                                          let sf := (BitVec.slice __opcode 31 1)
                                                                                          (decode_umax_imm_aarch64_instrs_integer_arithmetic_max_min_umax_imm Rd Rn imm8 sf))
                                                                                      else
                                                                                        (do
                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 18) == (0b0010001110011#13 : (BitVec 13)))) <&&> (do
                                                                                               (pure ((← readReg SEE) <b 1021))))) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1021
                                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                              let imm8 := (BitVec.slice __opcode 10 8)
                                                                                              let sf := (BitVec.slice __opcode 31 1)
                                                                                              (decode_umin_imm_aarch64_instrs_integer_arithmetic_max_min_umin_imm Rd Rn imm8 sf))
                                                                                          else (sailThrow ((Error_Undefined ())) : SailM Unit)))))))))))))))))))))))

/-- Type quantifiers: pc : Int -/
def __DecodeA32_LoadStoreImmLit (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 22 22) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 20 20) == (1#1 : (BitVec 1)))))) <&&> (do
       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
         (pure ((← readReg SEE) <b 2923)))))) : Bool)
  then
    (do
      writeReg SEE 2923
      let cond := (BitVec.slice __opcode 28 4)
      let P := (BitVec.slice __opcode 24 1)
      let U := (BitVec.slice __opcode 23 1)
      let W := (BitVec.slice __opcode 21 1)
      let Rn := (BitVec.slice __opcode 16 4)
      let Rt := (BitVec.slice __opcode 12 4)
      let imm12 := (BitVec.slice __opcode 0 12)
      (decode_aarch32_instrs_LDRB_i_A1enc_A_txt cond P U W Rn Rt imm12))
  else
    (do
      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 22 22) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 20 16) == (0b11111#5 : (BitVec 5)))))) <&&> (do
           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
             (pure ((← readReg SEE) <b 2927)))))) : Bool)
      then
        (do
          writeReg SEE 2927
          let cond := (BitVec.slice __opcode 28 4)
          let P := (BitVec.slice __opcode 24 1)
          let U := (BitVec.slice __opcode 23 1)
          let W := (BitVec.slice __opcode 21 1)
          let Rt := (BitVec.slice __opcode 12 4)
          let imm12 := (BitVec.slice __opcode 0 12)
          (decode_aarch32_instrs_LDRB_l_A1enc_A_txt cond P U W Rt imm12))
      else
        (do
          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 24) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 22 20) == (0b111#3 : (BitVec 3))))) <&&> (do
               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                 (pure ((← readReg SEE) <b 2932)))))) : Bool)
          then
            (do
              writeReg SEE 2932
              let cond := (BitVec.slice __opcode 28 4)
              let U := (BitVec.slice __opcode 23 1)
              let Rn := (BitVec.slice __opcode 16 4)
              let Rt := (BitVec.slice __opcode 12 4)
              let imm12 := (BitVec.slice __opcode 0 12)
              (decode_aarch32_instrs_LDRBT_A1enc_A_txt cond U Rn Rt imm12))
          else
            (do
              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 22 22) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 20 20) == (1#1 : (BitVec 1)))))) <&&> (do
                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                     (pure ((← readReg SEE) <b 2960)))))) : Bool)
              then
                (do
                  writeReg SEE 2960
                  let cond := (BitVec.slice __opcode 28 4)
                  let P := (BitVec.slice __opcode 24 1)
                  let U := (BitVec.slice __opcode 23 1)
                  let W := (BitVec.slice __opcode 21 1)
                  let Rn := (BitVec.slice __opcode 16 4)
                  let Rt := (BitVec.slice __opcode 12 4)
                  let imm12 := (BitVec.slice __opcode 0 12)
                  (decode_aarch32_instrs_LDR_i_A1enc_A_txt cond P U W Rn Rt imm12))
              else
                (do
                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 22 22) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 20 16) == (0b11111#5 : (BitVec 5)))))) <&&> (do
                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                         (pure ((← readReg SEE) <b 2965)))))) : Bool)
                  then
                    (do
                      writeReg SEE 2965
                      let cond := (BitVec.slice __opcode 28 4)
                      let P := (BitVec.slice __opcode 24 1)
                      let U := (BitVec.slice __opcode 23 1)
                      let W := (BitVec.slice __opcode 21 1)
                      let Rt := (BitVec.slice __opcode 12 4)
                      let imm12 := (BitVec.slice __opcode 0 12)
                      (decode_aarch32_instrs_LDR_l_A1enc_A_txt cond P U W Rt imm12))
                  else
                    (do
                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 24) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 22 20) == (0b011#3 : (BitVec 3))))) <&&> (do
                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                             (pure ((← readReg SEE) <b 2993)))))) : Bool)
                      then
                        (do
                          writeReg SEE 2993
                          let cond := (BitVec.slice __opcode 28 4)
                          let U := (BitVec.slice __opcode 23 1)
                          let Rn := (BitVec.slice __opcode 16 4)
                          let Rt := (BitVec.slice __opcode 12 4)
                          let imm12 := (BitVec.slice __opcode 0 12)
                          (decode_aarch32_instrs_LDRT_A1enc_A_txt cond U Rn Rt imm12))
                      else
                        (do
                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 22 22) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1)))))) <&&> (do
                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                 (pure ((← readReg SEE) <b 3193)))))) : Bool)
                          then
                            (do
                              writeReg SEE 3193
                              let cond := (BitVec.slice __opcode 28 4)
                              let P := (BitVec.slice __opcode 24 1)
                              let U := (BitVec.slice __opcode 23 1)
                              let W := (BitVec.slice __opcode 21 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let Rt := (BitVec.slice __opcode 12 4)
                              let imm12 := (BitVec.slice __opcode 0 12)
                              (decode_aarch32_instrs_STRB_i_A1enc_A_txt cond P U W Rn Rt imm12))
                          else
                            (do
                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 24) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 22 20) == (0b110#3 : (BitVec 3))))) <&&> (do
                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                     (pure ((← readReg SEE) <b 3200)))))) : Bool)
                              then
                                (do
                                  writeReg SEE 3200
                                  let cond := (BitVec.slice __opcode 28 4)
                                  let U := (BitVec.slice __opcode 23 1)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let Rt := (BitVec.slice __opcode 12 4)
                                  let imm12 := (BitVec.slice __opcode 0 12)
                                  (decode_aarch32_instrs_STRBT_A1enc_A_txt cond U Rn Rt imm12))
                              else
                                (do
                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b010#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 22 22) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1)))))) <&&> (do
                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                         (pure ((← readReg SEE) <b 3224)))))) : Bool)
                                  then
                                    (do
                                      writeReg SEE 3224
                                      let cond := (BitVec.slice __opcode 28 4)
                                      let P := (BitVec.slice __opcode 24 1)
                                      let U := (BitVec.slice __opcode 23 1)
                                      let W := (BitVec.slice __opcode 21 1)
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let Rt := (BitVec.slice __opcode 12 4)
                                      let imm12 := (BitVec.slice __opcode 0 12)
                                      (decode_aarch32_instrs_STR_i_A1enc_A_txt cond P U W Rn Rt imm12))
                                  else
                                    (do
                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 24) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 22 20) == (0b010#3 : (BitVec 3))))) <&&> (do
                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                             (pure ((← readReg SEE) <b 3232)))))) : Bool)
                                      then
                                        (do
                                          writeReg SEE 3232
                                          let cond := (BitVec.slice __opcode 28 4)
                                          let U := (BitVec.slice __opcode 23 1)
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let Rt := (BitVec.slice __opcode 12 4)
                                          let imm12 := (BitVec.slice __opcode 0 12)
                                          (decode_aarch32_instrs_STRT_A1enc_A_txt cond U Rn Rt imm12))
                                      else (sailThrow ((Error_Undefined ())) : SailM Unit))))))))))

/-- Type quantifiers: pc : Int -/
def __DecodeA32_LoadStoreReg (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b011#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 22 22) == (1#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
         (pure ((← readReg SEE) <b 2929)))))) : Bool)
  then
    (do
      writeReg SEE 2929
      let cond := (BitVec.slice __opcode 28 4)
      let P := (BitVec.slice __opcode 24 1)
      let U := (BitVec.slice __opcode 23 1)
      let W := (BitVec.slice __opcode 21 1)
      let Rn := (BitVec.slice __opcode 16 4)
      let Rt := (BitVec.slice __opcode 12 4)
      let imm5 := (BitVec.slice __opcode 7 5)
      let stype := (BitVec.slice __opcode 5 2)
      let Rm := (BitVec.slice __opcode 0 4)
      (decode_aarch32_instrs_LDRB_r_A1enc_A_txt cond P U W Rn Rt imm5 stype Rm))
  else
    (do
      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 24) == (0x6#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 22 20) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))) <&&> (do
           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
             (pure ((← readReg SEE) <b 2933)))))) : Bool)
      then
        (do
          writeReg SEE 2933
          let cond := (BitVec.slice __opcode 28 4)
          let U := (BitVec.slice __opcode 23 1)
          let Rn := (BitVec.slice __opcode 16 4)
          let Rt := (BitVec.slice __opcode 12 4)
          let imm5 := (BitVec.slice __opcode 7 5)
          let stype := (BitVec.slice __opcode 5 2)
          let Rm := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_LDRBT_A2enc_A_txt cond U Rn Rt imm5 stype Rm))
      else
        (do
          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b011#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 22 22) == (0#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                 (pure ((← readReg SEE) <b 2968)))))) : Bool)
          then
            (do
              writeReg SEE 2968
              let cond := (BitVec.slice __opcode 28 4)
              let P := (BitVec.slice __opcode 24 1)
              let U := (BitVec.slice __opcode 23 1)
              let W := (BitVec.slice __opcode 21 1)
              let Rn := (BitVec.slice __opcode 16 4)
              let Rt := (BitVec.slice __opcode 12 4)
              let imm5 := (BitVec.slice __opcode 7 5)
              let stype := (BitVec.slice __opcode 5 2)
              let Rm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_LDR_r_A1enc_A_txt cond P U W Rn Rt imm5 stype Rm))
          else
            (do
              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 24) == (0x6#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 22 20) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))) <&&> (do
                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                     (pure ((← readReg SEE) <b 2994)))))) : Bool)
              then
                (do
                  writeReg SEE 2994
                  let cond := (BitVec.slice __opcode 28 4)
                  let U := (BitVec.slice __opcode 23 1)
                  let Rn := (BitVec.slice __opcode 16 4)
                  let Rt := (BitVec.slice __opcode 12 4)
                  let imm5 := (BitVec.slice __opcode 7 5)
                  let stype := (BitVec.slice __opcode 5 2)
                  let Rm := (BitVec.slice __opcode 0 4)
                  (decode_aarch32_instrs_LDRT_A2enc_A_txt cond U Rn Rt imm5 stype Rm))
              else
                (do
                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b011#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 22 22) == (1#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                         (pure ((← readReg SEE) <b 3197)))))) : Bool)
                  then
                    (do
                      writeReg SEE 3197
                      let cond := (BitVec.slice __opcode 28 4)
                      let P := (BitVec.slice __opcode 24 1)
                      let U := (BitVec.slice __opcode 23 1)
                      let W := (BitVec.slice __opcode 21 1)
                      let Rn := (BitVec.slice __opcode 16 4)
                      let Rt := (BitVec.slice __opcode 12 4)
                      let imm5 := (BitVec.slice __opcode 7 5)
                      let stype := (BitVec.slice __opcode 5 2)
                      let Rm := (BitVec.slice __opcode 0 4)
                      (decode_aarch32_instrs_STRB_r_A1enc_A_txt cond P U W Rn Rt imm5 stype Rm))
                  else
                    (do
                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 24) == (0x6#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 22 20) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))) <&&> (do
                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                             (pure ((← readReg SEE) <b 3201)))))) : Bool)
                      then
                        (do
                          writeReg SEE 3201
                          let cond := (BitVec.slice __opcode 28 4)
                          let U := (BitVec.slice __opcode 23 1)
                          let Rn := (BitVec.slice __opcode 16 4)
                          let Rt := (BitVec.slice __opcode 12 4)
                          let imm5 := (BitVec.slice __opcode 7 5)
                          let stype := (BitVec.slice __opcode 5 2)
                          let Rm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_STRBT_A2enc_A_txt cond U Rn Rt imm5 stype Rm))
                      else
                        (do
                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b011#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 22 22) == (0#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                 (pure ((← readReg SEE) <b 3229)))))) : Bool)
                          then
                            (do
                              writeReg SEE 3229
                              let cond := (BitVec.slice __opcode 28 4)
                              let P := (BitVec.slice __opcode 24 1)
                              let U := (BitVec.slice __opcode 23 1)
                              let W := (BitVec.slice __opcode 21 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let Rt := (BitVec.slice __opcode 12 4)
                              let imm5 := (BitVec.slice __opcode 7 5)
                              let stype := (BitVec.slice __opcode 5 2)
                              let Rm := (BitVec.slice __opcode 0 4)
                              (decode_aarch32_instrs_STR_r_A1enc_A_txt cond P U W Rn Rt imm5 stype Rm))
                          else
                            (do
                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 24) == (0x6#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 22 20) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))) <&&> (do
                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                     (pure ((← readReg SEE) <b 3233)))))) : Bool)
                              then
                                (do
                                  writeReg SEE 3233
                                  let cond := (BitVec.slice __opcode 28 4)
                                  let U := (BitVec.slice __opcode 23 1)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let Rt := (BitVec.slice __opcode 12 4)
                                  let imm5 := (BitVec.slice __opcode 7 5)
                                  let stype := (BitVec.slice __opcode 5 2)
                                  let Rm := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_STRT_A2enc_A_txt cond U Rn Rt imm5 stype Rm))
                              else (sailThrow ((Error_Undefined ())) : SailM Unit))))))))

/-- Type quantifiers: pc : Int -/
def __DecodeA32_BranchBlock (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  if ((←((pure ((Sail.BitVec.extractLsb __opcode 27 24) == (0xA#4 : (BitVec 4)))) <&&> (do
       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
         (pure ((← readReg SEE) <b 2851)))))) : Bool)
  then
    (do
      writeReg SEE 2851
      let cond := (BitVec.slice __opcode 28 4)
      let imm24 := (BitVec.slice __opcode 0 24)
      (decode_aarch32_instrs_B_A1enc_A_txt cond imm24))
  else
    (do
      if ((←((pure ((Sail.BitVec.extractLsb __opcode 27 24) == (0xB#4 : (BitVec 4)))) <&&> (do
           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
             (pure ((← readReg SEE) <b 2868)))))) : Bool)
      then
        (do
          writeReg SEE 2868
          let cond := (BitVec.slice __opcode 28 4)
          let imm24 := (BitVec.slice __opcode 0 24)
          (decode_aarch32_instrs_BL_i_A1enc_A_txt cond imm24))
      else
        (do
          if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 25) == (0b1111101#7 : (BitVec 7)))) <&&> (do
               (pure ((← readReg SEE) <b 2869))))) : Bool)
          then
            (do
              writeReg SEE 2869
              let H := (BitVec.slice __opcode 24 1)
              let imm24 := (BitVec.slice __opcode 0 24)
              (decode_aarch32_instrs_BL_i_A2enc_A_txt H imm24))
          else
            (do
              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 22) == (0b100010#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb __opcode 20 20) == (1#1 : (BitVec 1))))) <&&> (do
                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                     (pure ((← readReg SEE) <b 2916)))))) : Bool)
              then
                (do
                  writeReg SEE 2916
                  let cond := (BitVec.slice __opcode 28 4)
                  let W := (BitVec.slice __opcode 21 1)
                  let Rn := (BitVec.slice __opcode 16 4)
                  let register_list := (BitVec.slice __opcode 0 16)
                  (decode_aarch32_instrs_LDM_A1enc_A_txt cond W Rn register_list))
              else
                (do
                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 22) == (0b100000#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb __opcode 20 20) == (1#1 : (BitVec 1))))) <&&> (do
                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                         (pure ((← readReg SEE) <b 2919)))))) : Bool)
                  then
                    (do
                      writeReg SEE 2919
                      let cond := (BitVec.slice __opcode 28 4)
                      let W := (BitVec.slice __opcode 21 1)
                      let Rn := (BitVec.slice __opcode 16 4)
                      let register_list := (BitVec.slice __opcode 0 16)
                      (decode_aarch32_instrs_LDMDA_A1enc_A_txt cond W Rn register_list))
                  else
                    (do
                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 22) == (0b100100#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb __opcode 20 20) == (1#1 : (BitVec 1))))) <&&> (do
                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                             (pure ((← readReg SEE) <b 2920)))))) : Bool)
                      then
                        (do
                          writeReg SEE 2920
                          let cond := (BitVec.slice __opcode 28 4)
                          let W := (BitVec.slice __opcode 21 1)
                          let Rn := (BitVec.slice __opcode 16 4)
                          let register_list := (BitVec.slice __opcode 0 16)
                          (decode_aarch32_instrs_LDMDB_A1enc_A_txt cond W Rn register_list))
                      else
                        (do
                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 22) == (0b100110#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb __opcode 20 20) == (1#1 : (BitVec 1))))) <&&> (do
                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                 (pure ((← readReg SEE) <b 2922)))))) : Bool)
                          then
                            (do
                              writeReg SEE 2922
                              let cond := (BitVec.slice __opcode 28 4)
                              let W := (BitVec.slice __opcode 21 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let register_list := (BitVec.slice __opcode 0 16)
                              (decode_aarch32_instrs_LDMIB_A1enc_A_txt cond W Rn register_list))
                          else
                            (do
                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 22) == (0b100010#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1))))) <&&> (do
                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                     (pure ((← readReg SEE) <b 3186)))))) : Bool)
                              then
                                (do
                                  writeReg SEE 3186
                                  let cond := (BitVec.slice __opcode 28 4)
                                  let W := (BitVec.slice __opcode 21 1)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let register_list := (BitVec.slice __opcode 0 16)
                                  (decode_aarch32_instrs_STM_A1enc_A_txt cond W Rn register_list))
                              else
                                (do
                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 22) == (0b100000#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1))))) <&&> (do
                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                         (pure ((← readReg SEE) <b 3189)))))) : Bool)
                                  then
                                    (do
                                      writeReg SEE 3189
                                      let cond := (BitVec.slice __opcode 28 4)
                                      let W := (BitVec.slice __opcode 21 1)
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let register_list := (BitVec.slice __opcode 0 16)
                                      (decode_aarch32_instrs_STMDA_A1enc_A_txt cond W Rn register_list))
                                  else
                                    (do
                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 22) == (0b100100#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1))))) <&&> (do
                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                             (pure ((← readReg SEE) <b 3190)))))) : Bool)
                                      then
                                        (do
                                          writeReg SEE 3190
                                          let cond := (BitVec.slice __opcode 28 4)
                                          let W := (BitVec.slice __opcode 21 1)
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let register_list := (BitVec.slice __opcode 0 16)
                                          (decode_aarch32_instrs_STMDB_A1enc_A_txt cond W Rn register_list))
                                      else
                                        (do
                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 22) == (0b100110#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1))))) <&&> (do
                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                 (pure ((← readReg SEE) <b 3192)))))) : Bool)
                                          then
                                            (do
                                              writeReg SEE 3192
                                              let cond := (BitVec.slice __opcode 28 4)
                                              let W := (BitVec.slice __opcode 21 1)
                                              let Rn := (BitVec.slice __opcode 16 4)
                                              let register_list := (BitVec.slice __opcode 0 16)
                                              (decode_aarch32_instrs_STMIB_A1enc_A_txt cond W Rn register_list))
                                          else
                                            (do
                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 22 22) == (1#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 15 15) == (1#1 : (BitVec 1))))))) <&&> (do
                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                     (pure ((← readReg SEE) <b 3776)))))) : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3776
                                                  let cond := (BitVec.slice __opcode 28 4)
                                                  let P := (BitVec.slice __opcode 24 1)
                                                  let U := (BitVec.slice __opcode 23 1)
                                                  let W := (BitVec.slice __opcode 21 1)
                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                  let register_list := (BitVec.slice __opcode 0 15)
                                                  (decode_aarch32_instrs_LDM_e_A1enc_AS_txt cond P U W Rn register_list))
                                              else
                                                (do
                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 22 20) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb __opcode 15 15) == (0#1 : (BitVec 1)))))) <&&> (do
                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                         (pure ((← readReg SEE) <b 3777)))))) : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3777
                                                      let cond := (BitVec.slice __opcode 28 4)
                                                      let P := (BitVec.slice __opcode 24 1)
                                                      let U := (BitVec.slice __opcode 23 1)
                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                      let register_list := (BitVec.slice __opcode 0 15)
                                                      if (((BitVec.join1 [(BitVec.access __opcode 21)]) != 0#1) : Bool)
                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                      else (decode_aarch32_instrs_LDM_u_A1enc_AS_txt cond P U Rn register_list))
                                                  else
                                                    (do
                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 25) == (0b1111100#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb __opcode 22 22) == (0#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 15 0) == (0x0A00#16 : (BitVec 16))))))) <&&> (do
                                                           (pure ((← readReg SEE) <b 3787))))) : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3787
                                                          let P := (BitVec.slice __opcode 24 1)
                                                          let U := (BitVec.slice __opcode 23 1)
                                                          let W := (BitVec.slice __opcode 21 1)
                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                          if ((((((((((((((BitVec.join1 [(BitVec.access __opcode 12)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 13)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 14)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 15)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 0)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 1)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 2)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 3)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 4)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 5)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 6)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 7)]) != 0#1)) : Bool)
                                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                          else (decode_aarch32_instrs_RFE_A1enc_AS_txt P U W Rn))
                                                      else
                                                        (do
                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 25) == (0b1111100#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb __opcode 22 22) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 20 5) == (0x6828#16 : (BitVec 16)))))) <&&> (do
                                                               (pure ((← readReg SEE) <b 3792))))) : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3792
                                                              let P := (BitVec.slice __opcode 24 1)
                                                              let U := (BitVec.slice __opcode 23 1)
                                                              let W := (BitVec.slice __opcode 21 1)
                                                              let mode := (BitVec.slice __opcode 0 5)
                                                              if (((((((((((((BitVec.join1 [(BitVec.access __opcode 16)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 17)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 18)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 19)]) != 1#1)) || ((BitVec.join1 [(BitVec.access __opcode 12)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 13)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 14)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 15)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 5)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 6)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 7)]) != 0#1)) : Bool)
                                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                              else (decode_aarch32_instrs_SRS_A1enc_AS_txt P U W mode))
                                                          else
                                                            (do
                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb __opcode 22 20) == (0b100#3 : (BitVec 3))))) <&&> (do
                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                     (pure ((← readReg SEE) <b 3795)))))) : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3795
                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                  let P := (BitVec.slice __opcode 24 1)
                                                                  let U := (BitVec.slice __opcode 23 1)
                                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                                  let register_list := (BitVec.slice __opcode 0 16)
                                                                  if (((BitVec.join1 [(BitVec.access __opcode 21)]) != 0#1) : Bool)
                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                  else (decode_aarch32_instrs_STM_u_A1enc_AS_txt cond P U Rn register_list))
                                                              else (sailThrow ((Error_Undefined ())) : SailM Unit))))))))))))))))


