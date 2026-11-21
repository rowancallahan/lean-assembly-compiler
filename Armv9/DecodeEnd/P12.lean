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
def __DecodeT16 (pc : Int) (__opcode : (BitVec 16)) : SailM Unit := do
  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0100000101#10 : (BitVec 10)))) <&&> (do
       (pure ((← readReg SEE) <b 2816))))) : Bool)
  then
    (do
      writeReg SEE 2816
      let Rm := (BitVec.slice __opcode 3 3)
      let Rdn := (BitVec.slice __opcode 0 3)
      (decode_aarch32_instrs_ADC_r_T1enc_A_txt Rm Rdn))
  else
    (do
      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 9) == (0b0001110#7 : (BitVec 7)))) <&&> (do
           (pure ((← readReg SEE) <b 2820))))) : Bool)
      then
        (do
          writeReg SEE 2820
          let imm3 := (BitVec.slice __opcode 6 3)
          let Rn := (BitVec.slice __opcode 3 3)
          let Rd := (BitVec.slice __opcode 0 3)
          (decode_aarch32_instrs_ADD_i_T1enc_A_txt imm3 Rn Rd))
      else
        (do
          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b00110#5 : (BitVec 5)))) <&&> (do
               (pure ((← readReg SEE) <b 2821))))) : Bool)
          then
            (do
              writeReg SEE 2821
              let Rdn := (BitVec.slice __opcode 8 3)
              let imm8 := (BitVec.slice __opcode 0 8)
              (decode_aarch32_instrs_ADD_i_T2enc_A_txt Rdn imm8))
          else
            (do
              if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 9) == (0b0001100#7 : (BitVec 7)))) <&&> (do
                   (pure ((← readReg SEE) <b 2825))))) : Bool)
              then
                (do
                  writeReg SEE 2825
                  let Rm := (BitVec.slice __opcode 6 3)
                  let Rn := (BitVec.slice __opcode 3 3)
                  let Rd := (BitVec.slice __opcode 0 3)
                  (decode_aarch32_instrs_ADD_r_T1enc_A_txt Rm Rn Rd))
              else
                (do
                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 8) == (0x44#8 : (BitVec 8)))) <&&> (do
                       (pure ((← readReg SEE) <b 2826))))) : Bool)
                  then
                    (do
                      writeReg SEE 2826
                      let DN := (BitVec.slice __opcode 7 1)
                      let Rm := (BitVec.slice __opcode 3 4)
                      let Rdn := (BitVec.slice __opcode 0 3)
                      (decode_aarch32_instrs_ADD_r_T2enc_A_txt DN Rm Rdn))
                  else
                    (do
                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b10101#5 : (BitVec 5)))) <&&> (do
                           (pure ((← readReg SEE) <b 2830))))) : Bool)
                      then
                        (do
                          writeReg SEE 2830
                          let Rd := (BitVec.slice __opcode 8 3)
                          let imm8 := (BitVec.slice __opcode 0 8)
                          (decode_aarch32_instrs_ADD_SP_i_T1enc_A_txt Rd imm8))
                      else
                        (do
                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 7) == (0b101100000#9 : (BitVec 9)))) <&&> (do
                               (pure ((← readReg SEE) <b 2831))))) : Bool)
                          then
                            (do
                              writeReg SEE 2831
                              let imm7 := (BitVec.slice __opcode 0 7)
                              (decode_aarch32_instrs_ADD_SP_i_T2enc_A_txt imm7))
                          else
                            (do
                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 15 8) == (0x44#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 6 3) == (0xD#4 : (BitVec 4))))) <&&> (do
                                   (pure ((← readReg SEE) <b 2835))))) : Bool)
                              then
                                (do
                                  writeReg SEE 2835
                                  let DM := (BitVec.slice __opcode 7 1)
                                  let Rdm := (BitVec.slice __opcode 0 3)
                                  (decode_aarch32_instrs_ADD_SP_r_T1enc_A_txt DM Rdm))
                              else
                                (do
                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 15 7) == (0b010001001#9 : (BitVec 9))) && ((Sail.BitVec.extractLsb __opcode 2 0) == (0b101#3 : (BitVec 3))))) <&&> (do
                                       (pure ((← readReg SEE) <b 2836))))) : Bool)
                                  then
                                    (do
                                      writeReg SEE 2836
                                      let Rm := (BitVec.slice __opcode 3 4)
                                      (decode_aarch32_instrs_ADD_SP_r_T2enc_A_txt Rm))
                                  else
                                    (do
                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b10100#5 : (BitVec 5)))) <&&> (do
                                           (pure ((← readReg SEE) <b 2840))))) : Bool)
                                      then
                                        (do
                                          writeReg SEE 2840
                                          let Rd := (BitVec.slice __opcode 8 3)
                                          let imm8 := (BitVec.slice __opcode 0 8)
                                          (decode_aarch32_instrs_ADR_T1enc_A_txt Rd imm8))
                                      else
                                        (do
                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0100000000#10 : (BitVec 10)))) <&&> (do
                                               (pure ((← readReg SEE) <b 2846))))) : Bool)
                                          then
                                            (do
                                              writeReg SEE 2846
                                              let Rm := (BitVec.slice __opcode 3 3)
                                              let Rdn := (BitVec.slice __opcode 0 3)
                                              (decode_aarch32_instrs_AND_r_T1enc_A_txt Rm Rdn))
                                          else
                                            (do
                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b00010#5 : (BitVec 5)))) <&&> (do
                                                   (pure ((← readReg SEE) <b 2849))))) : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2849
                                                  let imm5 := (BitVec.slice __opcode 6 5)
                                                  let Rm := (BitVec.slice __opcode 3 3)
                                                  let Rd := (BitVec.slice __opcode 0 3)
                                                  (decode_aarch32_instrs_ASR_i_T1enc_A_txt imm5 Rm Rd))
                                              else
                                                (do
                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0100000100#10 : (BitVec 10)))) <&&> (do
                                                       (pure ((← readReg SEE) <b 2850))))) : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2850
                                                      let Rm := (BitVec.slice __opcode 3 3)
                                                      let Rdn := (BitVec.slice __opcode 0 3)
                                                      (decode_aarch32_instrs_ASR_r_T1enc_A_txt Rm Rdn))
                                                  else
                                                    (do
                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 12) == (0xD#4 : (BitVec 4)))) <&&> (do
                                                           (pure ((BitVec.slice __opcode 8 4) != 0b1111#4)) <&&> (do
                                                             (pure ((← readReg SEE) <b 2852)))))) : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2852
                                                          let cond := (BitVec.slice __opcode 8 4)
                                                          let imm8 := (BitVec.slice __opcode 0 8)
                                                          (decode_aarch32_instrs_B_T1enc_A_txt cond imm8))
                                                      else
                                                        (do
                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b11100#5 : (BitVec 5)))) <&&> (do
                                                               (pure ((← readReg SEE) <b 2853))))) : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2853
                                                              let imm11 := (BitVec.slice __opcode 0 11)
                                                              (decode_aarch32_instrs_B_T2enc_A_txt imm11))
                                                          else
                                                            (do
                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0100001110#10 : (BitVec 10)))) <&&> (do
                                                                   (pure ((← readReg SEE) <b 2863))))) : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2863
                                                                  let Rm := (BitVec.slice __opcode 3 3)
                                                                  let Rdn := (BitVec.slice __opcode 0 3)
                                                                  (decode_aarch32_instrs_BIC_r_T1enc_A_txt Rm Rdn))
                                                              else
                                                                (do
                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 8) == (0xBE#8 : (BitVec 8)))) <&&> (do
                                                                       (pure ((← readReg SEE) <b 2867))))) : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2867
                                                                      let imm8 := (BitVec.slice __opcode 0 8)
                                                                      (decode_aarch32_instrs_BKPT_T1enc_A_txt imm8))
                                                                  else
                                                                    (do
                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 15 7) == (0b010001111#9 : (BitVec 9))) && ((Sail.BitVec.extractLsb __opcode 2 0) == (0b000#3 : (BitVec 3))))) <&&> (do
                                                                           (pure ((← readReg SEE) <b 2873))))) : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2873
                                                                          let Rm := (BitVec.slice __opcode 3 4)
                                                                          if (((((BitVec.join1 [(BitVec.access __opcode 0)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 1)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 2)]) != 0#1)) : Bool)
                                                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                          else (decode_aarch32_instrs_BLX_r_T1enc_A_txt Rm))
                                                                      else
                                                                        (do
                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 15 7) == (0b010001110#9 : (BitVec 9))) && ((Sail.BitVec.extractLsb __opcode 2 0) == (0b000#3 : (BitVec 3))))) <&&> (do
                                                                               (pure ((← readReg SEE) <b 2875))))) : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2875
                                                                              let Rm := (BitVec.slice __opcode 3 4)
                                                                              if (((((BitVec.join1 [(BitVec.access __opcode 0)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 1)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 2)]) != 0#1)) : Bool)
                                                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                              else (decode_aarch32_instrs_BX_T1enc_A_txt Rm))
                                                                          else
                                                                            (do
                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 15 12) == (0xB#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 10 10) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 8 8) == (1#1 : (BitVec 1)))))) <&&> (do
                                                                                   (pure ((← readReg SEE) <b 2878))))) : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2878
                                                                                  let op := (BitVec.slice __opcode 11 1)
                                                                                  let i := (BitVec.slice __opcode 9 1)
                                                                                  let imm5 := (BitVec.slice __opcode 3 5)
                                                                                  let Rn := (BitVec.slice __opcode 0 3)
                                                                                  (decode_aarch32_instrs_CBNZ_T1enc_A_txt op i imm5 Rn))
                                                                              else
                                                                                (do
                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0100001011#10 : (BitVec 10)))) <&&> (do
                                                                                       (pure ((← readReg SEE) <b 2886))))) : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2886
                                                                                      let Rm := (BitVec.slice __opcode 3 3)
                                                                                      let Rn := (BitVec.slice __opcode 0 3)
                                                                                      (decode_aarch32_instrs_CMN_r_T1enc_A_txt Rm Rn))
                                                                                  else
                                                                                    (do
                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b00101#5 : (BitVec 5)))) <&&> (do
                                                                                           (pure ((← readReg SEE) <b 2890))))) : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2890
                                                                                          let Rn := (BitVec.slice __opcode 8 3)
                                                                                          let imm8 := (BitVec.slice __opcode 0 8)
                                                                                          (decode_aarch32_instrs_CMP_i_T1enc_A_txt Rn imm8))
                                                                                      else
                                                                                        (do
                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0100001010#10 : (BitVec 10)))) <&&> (do
                                                                                               (pure ((← readReg SEE) <b 2893))))) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2893
                                                                                              let Rm := (BitVec.slice __opcode 3 3)
                                                                                              let Rn := (BitVec.slice __opcode 0 3)
                                                                                              (decode_aarch32_instrs_CMP_r_T1enc_A_txt Rm Rn))
                                                                                          else
                                                                                            (do
                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 8) == (0x45#8 : (BitVec 8)))) <&&> (do
                                                                                                   (pure ((← readReg SEE) <b 2894))))) : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2894
                                                                                                  let N := (BitVec.slice __opcode 7 1)
                                                                                                  let Rm := (BitVec.slice __opcode 3 4)
                                                                                                  let Rn := (BitVec.slice __opcode 0 3)
                                                                                                  (decode_aarch32_instrs_CMP_r_T2enc_A_txt N Rm Rn))
                                                                                              else
                                                                                                (do
                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0100000001#10 : (BitVec 10)))) <&&> (do
                                                                                                       (pure ((← readReg SEE) <b 2906))))) : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2906
                                                                                                      let Rm := (BitVec.slice __opcode 3 3)
                                                                                                      let Rdn := (BitVec.slice __opcode 0 3)
                                                                                                      (decode_aarch32_instrs_EOR_r_T1enc_A_txt Rm Rdn))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 8) == (0xBF#8 : (BitVec 8)))) <&&> (do
                                                                                                           (pure ((← readReg SEE) <b 2911))))) : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2911
                                                                                                          let firstcond := (BitVec.slice __opcode 4 4)
                                                                                                          let mask := (BitVec.slice __opcode 0 4)
                                                                                                          (decode_aarch32_instrs_IT_T1enc_A_txt firstcond mask))
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b11001#5 : (BitVec 5)))) <&&> (do
                                                                                                               (pure ((← readReg SEE) <b 2917))))) : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2917
                                                                                                              let Rn := (BitVec.slice __opcode 8 3)
                                                                                                              let register_list := (BitVec.slice __opcode 0 8)
                                                                                                              (decode_aarch32_instrs_LDM_T1enc_A_txt Rn register_list))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b01111#5 : (BitVec 5)))) <&&> (do
                                                                                                                   (pure ((← readReg SEE) <b 2924))))) : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2924
                                                                                                                  let imm5 := (BitVec.slice __opcode 6 5)
                                                                                                                  let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                  let Rt := (BitVec.slice __opcode 0 3)
                                                                                                                  (decode_aarch32_instrs_LDRB_i_T1enc_A_txt imm5 Rn Rt))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 9) == (0b0101110#7 : (BitVec 7)))) <&&> (do
                                                                                                                       (pure ((← readReg SEE) <b 2930))))) : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2930
                                                                                                                      let Rm := (BitVec.slice __opcode 6 3)
                                                                                                                      let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                      let Rt := (BitVec.slice __opcode 0 3)
                                                                                                                      (decode_aarch32_instrs_LDRB_r_T1enc_A_txt Rm Rn Rt))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b10001#5 : (BitVec 5)))) <&&> (do
                                                                                                                           (pure ((← readReg SEE) <b 2949))))) : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2949
                                                                                                                          let imm5 := (BitVec.slice __opcode 6 5)
                                                                                                                          let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                          let Rt := (BitVec.slice __opcode 0 3)
                                                                                                                          (decode_aarch32_instrs_LDRH_i_T1enc_A_txt imm5 Rn Rt))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 9) == (0b0101101#7 : (BitVec 7)))) <&&> (do
                                                                                                                               (pure ((← readReg SEE) <b 2955))))) : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2955
                                                                                                                              let Rm := (BitVec.slice __opcode 6 3)
                                                                                                                              let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                              let Rt := (BitVec.slice __opcode 0 3)
                                                                                                                              (decode_aarch32_instrs_LDRH_r_T1enc_A_txt Rm Rn Rt))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b01101#5 : (BitVec 5)))) <&&> (do
                                                                                                                                   (pure ((← readReg SEE) <b 2961))))) : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2961
                                                                                                                                  let imm5 := (BitVec.slice __opcode 6 5)
                                                                                                                                  let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                                  let Rt := (BitVec.slice __opcode 0 3)
                                                                                                                                  (decode_aarch32_instrs_LDR_i_T1enc_A_txt imm5 Rn Rt))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b10011#5 : (BitVec 5)))) <&&> (do
                                                                                                                                       (pure ((← readReg SEE) <b 2962))))) : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2962
                                                                                                                                      let Rt := (BitVec.slice __opcode 8 3)
                                                                                                                                      let imm8 := (BitVec.slice __opcode 0 8)
                                                                                                                                      (decode_aarch32_instrs_LDR_i_T2enc_A_txt Rt imm8))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b01001#5 : (BitVec 5)))) <&&> (do
                                                                                                                                           (pure ((← readReg SEE) <b 2966))))) : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 2966
                                                                                                                                          let Rt := (BitVec.slice __opcode 8 3)
                                                                                                                                          let imm8 := (BitVec.slice __opcode 0 8)
                                                                                                                                          (decode_aarch32_instrs_LDR_l_T1enc_A_txt Rt imm8))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 9) == (0b0101100#7 : (BitVec 7)))) <&&> (do
                                                                                                                                               (pure ((← readReg SEE) <b 2969))))) : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 2969
                                                                                                                                              let Rm := (BitVec.slice __opcode 6 3)
                                                                                                                                              let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                                              let Rt := (BitVec.slice __opcode 0 3)
                                                                                                                                              (decode_aarch32_instrs_LDR_r_T1enc_A_txt Rm Rn Rt))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 9) == (0b0101011#7 : (BitVec 7)))) <&&> (do
                                                                                                                                                   (pure ((← readReg SEE) <b 2977))))) : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 2977
                                                                                                                                                  let Rm := (BitVec.slice __opcode 6 3)
                                                                                                                                                  let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                                                  let Rt := (BitVec.slice __opcode 0 3)
                                                                                                                                                  (decode_aarch32_instrs_LDRSB_r_T1enc_A_txt Rm Rn Rt))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 9) == (0b0101111#7 : (BitVec 7)))) <&&> (do
                                                                                                                                                       (pure ((← readReg SEE) <b 2988))))) : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 2988
                                                                                                                                                      let Rm := (BitVec.slice __opcode 6 3)
                                                                                                                                                      let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                                                      let Rt := (BitVec.slice __opcode 0 3)
                                                                                                                                                      (decode_aarch32_instrs_LDRSH_r_T1enc_A_txt Rm Rn Rt))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b00000#5 : (BitVec 5)))) <&&> (do
                                                                                                                                                           (pure ((← readReg SEE) <b 2996))))) : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 2996
                                                                                                                                                          let imm5 := (BitVec.slice __opcode 6 5)
                                                                                                                                                          let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                          let Rd := (BitVec.slice __opcode 0 3)
                                                                                                                                                          (decode_aarch32_instrs_LSL_i_T1enc_A_txt imm5 Rm Rd))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0100000010#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                               (pure ((← readReg SEE) <b 2997))))) : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 2997
                                                                                                                                                              let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                              let Rdn := (BitVec.slice __opcode 0 3)
                                                                                                                                                              (decode_aarch32_instrs_LSL_r_T1enc_A_txt Rm Rdn))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b00001#5 : (BitVec 5)))) <&&> (do
                                                                                                                                                                   (pure ((← readReg SEE) <b 2999))))) : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 2999
                                                                                                                                                                  let imm5 := (BitVec.slice __opcode 6 5)
                                                                                                                                                                  let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                                  let Rd := (BitVec.slice __opcode 0 3)
                                                                                                                                                                  (decode_aarch32_instrs_LSR_i_T1enc_A_txt imm5 Rm Rd))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0100000011#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                       (pure ((← readReg SEE) <b 3000))))) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 3000
                                                                                                                                                                      let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                                      let Rdn := (BitVec.slice __opcode 0 3)
                                                                                                                                                                      (decode_aarch32_instrs_LSR_r_T1enc_A_txt Rm Rdn))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b00100#5 : (BitVec 5)))) <&&> (do
                                                                                                                                                                           (pure ((← readReg SEE) <b 3011))))) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 3011
                                                                                                                                                                          let Rd := (BitVec.slice __opcode 8 3)
                                                                                                                                                                          let imm8 := (BitVec.slice __opcode 0 8)
                                                                                                                                                                          (decode_aarch32_instrs_MOV_i_T1enc_A_txt Rd imm8))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 8) == (0x46#8 : (BitVec 8)))) <&&> (do
                                                                                                                                                                               (pure ((← readReg SEE) <b 3015))))) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 3015
                                                                                                                                                                              let D := (BitVec.slice __opcode 7 1)
                                                                                                                                                                              let Rm := (BitVec.slice __opcode 3 4)
                                                                                                                                                                              let Rd := (BitVec.slice __opcode 0 3)
                                                                                                                                                                              (decode_aarch32_instrs_MOV_r_T1enc_A_txt D Rm Rd))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0000000000#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                                   (pure ((← readReg SEE) <b 3016))))) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 3016
                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                  (decode_aarch32_instrs_MOV_r_T2enc_A_txt Rm Rd))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 10) == (0b010000#6 : (BitVec 6)))) <&&> (do
                                                                                                                                                                                       (pure ((← readReg SEE) <b 3019))))) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      writeReg SEE 3019
                                                                                                                                                                                      let op := (BitVec.slice __opcode 6 4)
                                                                                                                                                                                      let Rs := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                      let Rdm := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                      (decode_aarch32_instrs_MOV_rr_T1enc_A_txt op Rs Rdm))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0100001101#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                                           (pure ((← readReg SEE) <b 3028))))) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          writeReg SEE 3028
                                                                                                                                                                                          let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                          let Rdm := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                          (decode_aarch32_instrs_MUL_T1enc_A_txt Rn Rdm))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0100001111#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                                               (pure ((← readReg SEE) <b 3033))))) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              writeReg SEE 3033
                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                              (decode_aarch32_instrs_MVN_r_T1enc_A_txt Rm Rd))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              if ((←((pure (__opcode == (0xBF00#16 : (BitVec 16)))) <&&> (do
                                                                                                                                                                                                   (pure ((← readReg SEE) <b 3037))))) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  writeReg SEE 3037
                                                                                                                                                                                                  (decode_aarch32_instrs_NOP_T1enc_A_txt ()))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0100001100#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                                                       (pure ((← readReg SEE) <b 3044))))) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      writeReg SEE 3044
                                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                      let Rdn := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                      (decode_aarch32_instrs_ORR_r_T1enc_A_txt Rm Rdn))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 9) == (0b1011110#7 : (BitVec 7)))) <&&> (do
                                                                                                                                                                                                           (pure ((← readReg SEE) <b 3062))))) : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          writeReg SEE 3062
                                                                                                                                                                                                          let P := (BitVec.slice __opcode 8 1)
                                                                                                                                                                                                          let register_list := (BitVec.slice __opcode 0 8)
                                                                                                                                                                                                          (decode_aarch32_instrs_POP_T1enc_A_txt P register_list))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 9) == (0b1011010#7 : (BitVec 7)))) <&&> (do
                                                                                                                                                                                                               (pure ((← readReg SEE) <b 3063))))) : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              writeReg SEE 3063
                                                                                                                                                                                                              let M := (BitVec.slice __opcode 8 1)
                                                                                                                                                                                                              let register_list := (BitVec.slice __opcode 0 8)
                                                                                                                                                                                                              (decode_aarch32_instrs_PUSH_T1enc_A_txt M register_list))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b1011101001#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 3087))))) : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  writeReg SEE 3087
                                                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                  (decode_aarch32_instrs_REV16_T1enc_A_txt Rm Rd))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b1011101000#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 3090))))) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      writeReg SEE 3090
                                                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                      let Rd := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                      (decode_aarch32_instrs_REV_T1enc_A_txt Rm Rd))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b1011101011#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 3093))))) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          writeReg SEE 3093
                                                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                          (decode_aarch32_instrs_REVSH_T1enc_A_txt Rm Rd))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0100000111#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 3095))))) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              writeReg SEE 3095
                                                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                              let Rdn := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                              (decode_aarch32_instrs_ROR_r_T1enc_A_txt Rm Rdn))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0100001001#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 3097))))) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  writeReg SEE 3097
                                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                                  (decode_aarch32_instrs_RSB_i_T1enc_A_txt Rn Rd))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0100000110#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 3116))))) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      writeReg SEE 3116
                                                                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                                      let Rdn := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                                      (decode_aarch32_instrs_SBC_r_T1enc_A_txt Rm Rdn))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 15 4) == (0xB65#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 2 0) == (0b000#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 3126))))) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          writeReg SEE 3126
                                                                                                                                                                                                                                          let E := (BitVec.slice __opcode 3 1)
                                                                                                                                                                                                                                          if (((((BitVec.join1 [(BitVec.access __opcode 0)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 1)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 2)]) != 0#1)) : Bool)
                                                                                                                                                                                                                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                          else (decode_aarch32_instrs_SETEND_T1enc_A_txt E))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          if ((←((pure (__opcode == (0xBF40#16 : (BitVec 16)))) <&&> (do
                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 3128))))) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              writeReg SEE 3128
                                                                                                                                                                                                                                              (decode_aarch32_instrs_SEV_T1enc_A_txt ()))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b11000#5 : (BitVec 5)))) <&&> (do
                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 3187))))) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  writeReg SEE 3187
                                                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 8 3)
                                                                                                                                                                                                                                                  let register_list := (BitVec.slice __opcode 0 8)
                                                                                                                                                                                                                                                  (decode_aarch32_instrs_STM_T1enc_A_txt Rn register_list))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b01110#5 : (BitVec 5)))) <&&> (do
                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 3194))))) : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      writeReg SEE 3194
                                                                                                                                                                                                                                                      let imm5 := (BitVec.slice __opcode 6 5)
                                                                                                                                                                                                                                                      let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                                                      let Rt := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                                                      (decode_aarch32_instrs_STRB_i_T1enc_A_txt imm5 Rn Rt))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 9) == (0b0101010#7 : (BitVec 7)))) <&&> (do
                                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 3198))))) : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          writeReg SEE 3198
                                                                                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 6 3)
                                                                                                                                                                                                                                                          let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                                                          let Rt := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                                                          (decode_aarch32_instrs_STRB_r_T1enc_A_txt Rm Rn Rt))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b10000#5 : (BitVec 5)))) <&&> (do
                                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 3215))))) : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              writeReg SEE 3215
                                                                                                                                                                                                                                                              let imm5 := (BitVec.slice __opcode 6 5)
                                                                                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                                                              let Rt := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                                                              (decode_aarch32_instrs_STRH_i_T1enc_A_txt imm5 Rn Rt))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 9) == (0b0101001#7 : (BitVec 7)))) <&&> (do
                                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 3219))))) : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  writeReg SEE 3219
                                                                                                                                                                                                                                                                  let Rm := (BitVec.slice __opcode 6 3)
                                                                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                                                                  let Rt := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_STRH_r_T1enc_A_txt Rm Rn Rt))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b01100#5 : (BitVec 5)))) <&&> (do
                                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 3225))))) : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      writeReg SEE 3225
                                                                                                                                                                                                                                                                      let imm5 := (BitVec.slice __opcode 6 5)
                                                                                                                                                                                                                                                                      let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                                                                      let Rt := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_STR_i_T1enc_A_txt imm5 Rn Rt))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b10010#5 : (BitVec 5)))) <&&> (do
                                                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 3226))))) : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          writeReg SEE 3226
                                                                                                                                                                                                                                                                          let Rt := (BitVec.slice __opcode 8 3)
                                                                                                                                                                                                                                                                          let imm8 := (BitVec.slice __opcode 0 8)
                                                                                                                                                                                                                                                                          (decode_aarch32_instrs_STR_i_T2enc_A_txt Rt imm8))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 9) == (0b0101000#7 : (BitVec 7)))) <&&> (do
                                                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 3230))))) : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              writeReg SEE 3230
                                                                                                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 6 3)
                                                                                                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                                                                              let Rt := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_STR_r_T1enc_A_txt Rm Rn Rt))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 9) == (0b0001111#7 : (BitVec 7)))) <&&> (do
                                                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 3236))))) : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  writeReg SEE 3236
                                                                                                                                                                                                                                                                                  let imm3 := (BitVec.slice __opcode 6 3)
                                                                                                                                                                                                                                                                                  let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                                                                                  let Rd := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_SUB_i_T1enc_A_txt imm3 Rn Rd))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 11) == (0b00111#5 : (BitVec 5)))) <&&> (do
                                                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 3237))))) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      writeReg SEE 3237
                                                                                                                                                                                                                                                                                      let Rdn := (BitVec.slice __opcode 8 3)
                                                                                                                                                                                                                                                                                      let imm8 := (BitVec.slice __opcode 0 8)
                                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_SUB_i_T2enc_A_txt Rdn imm8))
                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 9) == (0b0001101#7 : (BitVec 7)))) <&&> (do
                                                                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 3242))))) : Bool)
                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          writeReg SEE 3242
                                                                                                                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 6 3)
                                                                                                                                                                                                                                                                                          let Rn := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                                                                                          (decode_aarch32_instrs_SUB_r_T1enc_A_txt Rm Rn Rd))
                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 7) == (0b101100001#9 : (BitVec 9)))) <&&> (do
                                                                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 3246))))) : Bool)
                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              writeReg SEE 3246
                                                                                                                                                                                                                                                                                              let imm7 := (BitVec.slice __opcode 0 7)
                                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_SUB_SP_i_T1enc_A_txt imm7))
                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 8) == (0xDF#8 : (BitVec 8)))) <&&> (do
                                                                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 3252))))) : Bool)
                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  writeReg SEE 3252
                                                                                                                                                                                                                                                                                                  let imm8 := (BitVec.slice __opcode 0 8)
                                                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_SVC_T1enc_A_txt imm8))
                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b1011001001#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 3262))))) : Bool)
                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      writeReg SEE 3262
                                                                                                                                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                                                                                                      let Rd := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_SXTB_T1enc_A_txt Rm Rd))
                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b1011001000#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 3265))))) : Bool)
                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          writeReg SEE 3265
                                                                                                                                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                                                                                                          (decode_aarch32_instrs_SXTH_T1enc_A_txt Rm Rd))
                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b0100001000#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 3276))))) : Bool)
                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              writeReg SEE 3276
                                                                                                                                                                                                                                                                                                              let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                                                                                                              let Rn := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_TST_r_T1enc_A_txt Rm Rn))
                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 8) == (0xDE#8 : (BitVec 8)))) <&&> (do
                                                                                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 3288))))) : Bool)
                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  writeReg SEE 3288
                                                                                                                                                                                                                                                                                                                  let imm8 := (BitVec.slice __opcode 0 8)
                                                                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_UDF_T1enc_A_txt imm8))
                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b1011001011#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 3345))))) : Bool)
                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      writeReg SEE 3345
                                                                                                                                                                                                                                                                                                                      let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                                                                                                                      let Rd := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_UXTB_T1enc_A_txt Rm Rd))
                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b1011001010#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 3348))))) : Bool)
                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          writeReg SEE 3348
                                                                                                                                                                                                                                                                                                                          let Rm := (BitVec.slice __opcode 3 3)
                                                                                                                                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 0 3)
                                                                                                                                                                                                                                                                                                                          (decode_aarch32_instrs_UXTH_T1enc_A_txt Rm Rd))
                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                          if ((←((pure (__opcode == (0xBF20#16 : (BitVec 16)))) <&&> (do
                                                                                                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 3761))))) : Bool)
                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              writeReg SEE 3761
                                                                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_WFE_T1enc_A_txt ()))
                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                              if ((←((pure (__opcode == (0xBF30#16 : (BitVec 16)))) <&&> (do
                                                                                                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 3764))))) : Bool)
                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  writeReg SEE 3764
                                                                                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_WFI_T1enc_A_txt ()))
                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                  if ((←((pure (__opcode == (0xBF10#16 : (BitVec 16)))) <&&> (do
                                                                                                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 3767))))) : Bool)
                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      writeReg SEE 3767
                                                                                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_YIELD_T1enc_A_txt ()))
                                                                                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 15 5) == (0b10110110011#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 3 3) == (0#1 : (BitVec 1))))) <&&> (do
                                                                                                                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 3770))))) : Bool)
                                                                                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          writeReg SEE 3770
                                                                                                                                                                                                                                                                                                                                          let im := (BitVec.slice __opcode 4 1)
                                                                                                                                                                                                                                                                                                                                          let A := (BitVec.slice __opcode 2 1)
                                                                                                                                                                                                                                                                                                                                          let I := (BitVec.slice __opcode 1 1)
                                                                                                                                                                                                                                                                                                                                          let F := (BitVec.slice __opcode 0 1)
                                                                                                                                                                                                                                                                                                                                          (decode_aarch32_instrs_CPS_T1enc_AS_txt im A I F))
                                                                                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 15 6) == (0b1011101010#10 : (BitVec 10)))) <&&> (do
                                                                                                                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 3814))))) : Bool)
                                                                                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              writeReg SEE 3814
                                                                                                                                                                                                                                                                                                                                              let imm6 := (BitVec.slice __opcode 0 6)
                                                                                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_HLT_T1enc_A_txt imm6))
                                                                                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                                                                                              if ((←((pure (__opcode == (0xBF50#16 : (BitVec 16)))) <&&> (do
                                                                                                                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 3830))))) : Bool)
                                                                                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  writeReg SEE 3830
                                                                                                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_SEVL_T1enc_A_txt ()))
                                                                                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 15 4) == (0xB61#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb __opcode 2 0) == (0b000#3 : (BitVec 3))))) <&&> (do
                                                                                                                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 3889))))) : Bool)
                                                                                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                                                                                      writeReg SEE 3889
                                                                                                                                                                                                                                                                                                                                                      let imm1 := (BitVec.slice __opcode 3 1)
                                                                                                                                                                                                                                                                                                                                                      if ((((((BitVec.join1 [(BitVec.access __opcode 4)]) != 1#1) || ((BitVec.join1 [(BitVec.access __opcode 0)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 1)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 2)]) != 0#1)) : Bool)
                                                                                                                                                                                                                                                                                                                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                                                                                                                      else (decode_aarch32_instrs_SETPAN_T1enc_A_txt imm1))
                                                                                                                                                                                                                                                                                                                                                  else (sailThrow ((Error_Undefined ())) : SailM Unit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


