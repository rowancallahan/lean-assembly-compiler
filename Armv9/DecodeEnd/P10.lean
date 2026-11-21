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
def __DecodeA32_SysASIMDFP (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b110#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 22 22) == (0#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 15 8) == (0x5E#8 : (BitVec 8))))))) <&&> (do
       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
         (pure ((← readReg SEE) <b 2912)))))) : Bool)
  then
    (do
      writeReg SEE 2912
      let cond := (BitVec.slice __opcode 28 4)
      let P := (BitVec.slice __opcode 24 1)
      let U := (BitVec.slice __opcode 23 1)
      let W := (BitVec.slice __opcode 21 1)
      let Rn := (BitVec.slice __opcode 16 4)
      let imm8 := (BitVec.slice __opcode 0 8)
      (decode_aarch32_instrs_LDC_i_A1enc_A_txt cond P U W Rn imm8))
  else
    (do
      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b110#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 22 22) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 20 8) == (0b1111101011110#13 : (BitVec 13)))))) <&&> (do
           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
             (pure ((← readReg SEE) <b 2914)))))) : Bool)
      then
        (do
          writeReg SEE 2914
          let cond := (BitVec.slice __opcode 28 4)
          let P := (BitVec.slice __opcode 24 1)
          let U := (BitVec.slice __opcode 23 1)
          let W := (BitVec.slice __opcode 21 1)
          let imm8 := (BitVec.slice __opcode 0 8)
          (decode_aarch32_instrs_LDC_l_A1enc_A_txt cond P U W imm8))
      else
        (do
          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 24) == (0xE#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 11 9) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1))))))) <&&> (do
               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                 (pure ((← readReg SEE) <b 3001)))))) : Bool)
          then
            (do
              writeReg SEE 3001
              let cond := (BitVec.slice __opcode 28 4)
              let opc1 := (BitVec.slice __opcode 21 3)
              let CRn := (BitVec.slice __opcode 16 4)
              let Rt := (BitVec.slice __opcode 12 4)
              let coproc := (BitVec.slice __opcode 8 1)
              let opc2 := (BitVec.slice __opcode 5 3)
              let CRm := (BitVec.slice __opcode 0 4)
              (decode_aarch32_instrs_MCR_A1enc_A_txt cond opc1 CRn Rt coproc opc2 CRm))
          else
            (do
              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0xC4#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 9) == (0b111#3 : (BitVec 3))))) <&&> (do
                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                     (pure ((← readReg SEE) <b 3003)))))) : Bool)
              then
                (do
                  writeReg SEE 3003
                  let cond := (BitVec.slice __opcode 28 4)
                  let Rt2 := (BitVec.slice __opcode 16 4)
                  let Rt := (BitVec.slice __opcode 12 4)
                  let coproc := (BitVec.slice __opcode 8 1)
                  let opc1 := (BitVec.slice __opcode 4 4)
                  let CRm := (BitVec.slice __opcode 0 4)
                  (decode_aarch32_instrs_MCRR_A1enc_A_txt cond Rt2 Rt coproc opc1 CRm))
              else
                (do
                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 24) == (0xE#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (1#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 11 9) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1))))))) <&&> (do
                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                         (pure ((← readReg SEE) <b 3023)))))) : Bool)
                  then
                    (do
                      writeReg SEE 3023
                      let cond := (BitVec.slice __opcode 28 4)
                      let opc1 := (BitVec.slice __opcode 21 3)
                      let CRn := (BitVec.slice __opcode 16 4)
                      let Rt := (BitVec.slice __opcode 12 4)
                      let coproc := (BitVec.slice __opcode 8 1)
                      let opc2 := (BitVec.slice __opcode 5 3)
                      let CRm := (BitVec.slice __opcode 0 4)
                      (decode_aarch32_instrs_MRC_A1enc_A_txt cond opc1 CRn Rt coproc opc2 CRm))
                  else
                    (do
                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0xC5#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 9) == (0b111#3 : (BitVec 3))))) <&&> (do
                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                             (pure ((← readReg SEE) <b 3025)))))) : Bool)
                      then
                        (do
                          writeReg SEE 3025
                          let cond := (BitVec.slice __opcode 28 4)
                          let Rt2 := (BitVec.slice __opcode 16 4)
                          let Rt := (BitVec.slice __opcode 12 4)
                          let coproc := (BitVec.slice __opcode 8 1)
                          let opc1 := (BitVec.slice __opcode 4 4)
                          let CRm := (BitVec.slice __opcode 0 4)
                          (decode_aarch32_instrs_MRRC_A1enc_A_txt cond Rt2 Rt coproc opc1 CRm))
                      else
                        (do
                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b110#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 22 22) == (0#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 15 8) == (0x5E#8 : (BitVec 8))))))) <&&> (do
                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                 (pure ((← readReg SEE) <b 3184)))))) : Bool)
                          then
                            (do
                              writeReg SEE 3184
                              let cond := (BitVec.slice __opcode 28 4)
                              let P := (BitVec.slice __opcode 24 1)
                              let U := (BitVec.slice __opcode 23 1)
                              let W := (BitVec.slice __opcode 21 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let imm8 := (BitVec.slice __opcode 0 8)
                              (decode_aarch32_instrs_STC_A1enc_A_txt cond P U W Rn imm8))
                          else
                            (do
                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 27 24) == (0xF#4 : (BitVec 4)))) <&&> (do
                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                     (pure ((← readReg SEE) <b 3251)))))) : Bool)
                              then
                                (do
                                  writeReg SEE 3251
                                  let cond := (BitVec.slice __opcode 28 4)
                                  let imm24 := (BitVec.slice __opcode 0 24)
                                  (decode_aarch32_instrs_SVC_A1enc_A_txt cond imm24))
                              else
                                (do
                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 16) == (0b110000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 7 6) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                         (pure ((← readReg SEE) <b 3361)))))) : Bool)
                                  then
                                    (do
                                      writeReg SEE 3361
                                      let cond := (BitVec.slice __opcode 28 4)
                                      let D := (BitVec.slice __opcode 22 1)
                                      let Vd := (BitVec.slice __opcode 12 4)
                                      let size := (BitVec.slice __opcode 8 2)
                                      let M := (BitVec.slice __opcode 5 1)
                                      let Vm := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_VABS_A2enc_A_txt cond D Vd size M Vm))
                                  else
                                    (do
                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11100#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 6 6) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                             (pure ((← readReg SEE) <b 3367)))))) : Bool)
                                      then
                                        (do
                                          writeReg SEE 3367
                                          let cond := (BitVec.slice __opcode 28 4)
                                          let D := (BitVec.slice __opcode 22 1)
                                          let Vn := (BitVec.slice __opcode 16 4)
                                          let Vd := (BitVec.slice __opcode 12 4)
                                          let size := (BitVec.slice __opcode 8 2)
                                          let N := (BitVec.slice __opcode 7 1)
                                          let M := (BitVec.slice __opcode 5 1)
                                          let Vm := (BitVec.slice __opcode 0 4)
                                          (decode_aarch32_instrs_VADD_f_A2enc_A_txt cond D Vn Vd size N M Vm))
                                      else
                                        (do
                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 16) == (0b110100#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 6 6) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                 (pure ((← readReg SEE) <b 3412)))))) : Bool)
                                          then
                                            (do
                                              writeReg SEE 3412
                                              let cond := (BitVec.slice __opcode 28 4)
                                              let D := (BitVec.slice __opcode 22 1)
                                              let Vd := (BitVec.slice __opcode 12 4)
                                              let size := (BitVec.slice __opcode 8 2)
                                              let E := (BitVec.slice __opcode 7 1)
                                              let M := (BitVec.slice __opcode 5 1)
                                              let Vm := (BitVec.slice __opcode 0 4)
                                              (decode_aarch32_instrs_VCMP_A1enc_A_txt cond D Vd size E M Vm))
                                          else
                                            (do
                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 16) == (0b110101#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 6 0) == (0b1000000#7 : (BitVec 7))))))) <&&> (do
                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                     (pure ((← readReg SEE) <b 3413)))))) : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3413
                                                  let cond := (BitVec.slice __opcode 28 4)
                                                  let D := (BitVec.slice __opcode 22 1)
                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                  let size := (BitVec.slice __opcode 8 2)
                                                  let E := (BitVec.slice __opcode 7 1)
                                                  if (((((((BitVec.join1 [(BitVec.access __opcode 5)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 0)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 1)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 2)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 3)]) != 0#1)) : Bool)
                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                  else (decode_aarch32_instrs_VCMP_A2enc_A_txt cond D Vd size E))
                                              else
                                                (do
                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 17) == (0b11001#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 11 9) == (0b101#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 6 6) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                         (pure ((← readReg SEE) <b 3418)))))) : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3418
                                                      let cond := (BitVec.slice __opcode 28 4)
                                                      let D := (BitVec.slice __opcode 22 1)
                                                      let op := (BitVec.slice __opcode 16 1)
                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                      let sz := (BitVec.slice __opcode 8 1)
                                                      let T := (BitVec.slice __opcode 7 1)
                                                      let M := (BitVec.slice __opcode 5 1)
                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_VCVTB_A1enc_A_txt cond D op Vd sz T M Vm))
                                                  else
                                                    (do
                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 16) == (0b110111#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb __opcode 11 9) == (0b101#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 7 6) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                             (pure ((← readReg SEE) <b 3420)))))) : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3420
                                                          let cond := (BitVec.slice __opcode 28 4)
                                                          let D := (BitVec.slice __opcode 22 1)
                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                          let size := (BitVec.slice __opcode 8 2)
                                                          let M := (BitVec.slice __opcode 5 1)
                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_VCVT_ds_A1enc_A_txt cond D Vd size M Vm))
                                                      else
                                                        (do
                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 19) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 6 6) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                 (pure ((← readReg SEE) <b 3426)))))) : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3426
                                                              let cond := (BitVec.slice __opcode 28 4)
                                                              let D := (BitVec.slice __opcode 22 1)
                                                              let opc2 := (BitVec.slice __opcode 16 3)
                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                              let size := (BitVec.slice __opcode 8 2)
                                                              let op := (BitVec.slice __opcode 7 1)
                                                              let M := (BitVec.slice __opcode 5 1)
                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_VCVT_iv_A1enc_A_txt cond D opc2 Vd size op M Vm))
                                                          else
                                                            (do
                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 19) == (0b111#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 17 17) == (1#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 6 6) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))))) <&&> (do
                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                     (pure ((← readReg SEE) <b 3430)))))) : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3430
                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                  let D := (BitVec.slice __opcode 22 1)
                                                                  let op := (BitVec.slice __opcode 18 1)
                                                                  let U := (BitVec.slice __opcode 16 1)
                                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                                  let sf := (BitVec.slice __opcode 8 2)
                                                                  let sx := (BitVec.slice __opcode 7 1)
                                                                  let i := (BitVec.slice __opcode 5 1)
                                                                  let imm4 := (BitVec.slice __opcode 0 4)
                                                                  (decode_aarch32_instrs_VCVT_xv_A1enc_A_txt cond D op U Vd sf sx i imm4))
                                                              else
                                                                (do
                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 6 6) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                         (pure ((← readReg SEE) <b 3432)))))) : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3432
                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                      let D := (BitVec.slice __opcode 22 1)
                                                                      let Vn := (BitVec.slice __opcode 16 4)
                                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                                      let size := (BitVec.slice __opcode 8 2)
                                                                      let N := (BitVec.slice __opcode 7 1)
                                                                      let M := (BitVec.slice __opcode 5 1)
                                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_VDIV_A1enc_A_txt cond D Vn Vd size N M Vm))
                                                                  else
                                                                    (do
                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0xB#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 6 6) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b10000#5 : (BitVec 5)))))))) <&&> (do
                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                             (pure ((← readReg SEE) <b 3434)))))) : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3434
                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                          let B := (BitVec.slice __opcode 22 1)
                                                                          let Q := (BitVec.slice __opcode 21 1)
                                                                          let Vd := (BitVec.slice __opcode 16 4)
                                                                          let Rt := (BitVec.slice __opcode 12 4)
                                                                          let D := (BitVec.slice __opcode 7 1)
                                                                          let E := (BitVec.slice __opcode 5 1)
                                                                          if ((((((BitVec.join1 [(BitVec.access __opcode 0)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 1)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 2)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 3)]) != 0#1)) : Bool)
                                                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                          else (decode_aarch32_instrs_VDUP_r_A1enc_A_txt cond B Q Vd Rt D E))
                                                                      else
                                                                        (do
                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                 (pure ((← readReg SEE) <b 3443)))))) : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3443
                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                              let D := (BitVec.slice __opcode 22 1)
                                                                              let Vn := (BitVec.slice __opcode 16 4)
                                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                                              let size := (BitVec.slice __opcode 8 2)
                                                                              let N := (BitVec.slice __opcode 7 1)
                                                                              let op := (BitVec.slice __opcode 6 1)
                                                                              let M := (BitVec.slice __opcode 5 1)
                                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                                              (decode_aarch32_instrs_VFMA_A2enc_A_txt cond D Vn Vd size N op M Vm))
                                                                          else
                                                                            (do
                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                     (pure ((← readReg SEE) <b 3446)))))) : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3446
                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                  let D := (BitVec.slice __opcode 22 1)
                                                                                  let Vn := (BitVec.slice __opcode 16 4)
                                                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                                                  let size := (BitVec.slice __opcode 8 2)
                                                                                  let N := (BitVec.slice __opcode 7 1)
                                                                                  let op := (BitVec.slice __opcode 6 1)
                                                                                  let M := (BitVec.slice __opcode 5 1)
                                                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                                                  (decode_aarch32_instrs_VFNMA_A1enc_A_txt cond D Vn Vd size N op M Vm))
                                                                              else
                                                                                (do
                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b110#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 11 8) == (0xB#4 : (BitVec 4)))))) <&&> (do
                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                         (pure ((← readReg SEE) <b 3498)))))) : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3498
                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                      let P := (BitVec.slice __opcode 24 1)
                                                                                      let U := (BitVec.slice __opcode 23 1)
                                                                                      let D := (BitVec.slice __opcode 22 1)
                                                                                      let W := (BitVec.slice __opcode 21 1)
                                                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                                                      let imm8 := (BitVec.slice __opcode 0 8)
                                                                                      (decode_aarch32_instrs_VLDM_A1enc_A_txt cond P U D W Rn Vd imm8))
                                                                                  else
                                                                                    (do
                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b110#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 11 8) == (0xA#4 : (BitVec 4)))))) <&&> (do
                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                             (pure ((← readReg SEE) <b 3499)))))) : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3499
                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                          let P := (BitVec.slice __opcode 24 1)
                                                                                          let U := (BitVec.slice __opcode 23 1)
                                                                                          let D := (BitVec.slice __opcode 22 1)
                                                                                          let W := (BitVec.slice __opcode 21 1)
                                                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                                                          let imm8 := (BitVec.slice __opcode 0 8)
                                                                                          (decode_aarch32_instrs_VLDM_A2enc_A_txt cond P U D W Rn Vd imm8))
                                                                                      else
                                                                                        (do
                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 24) == (0xD#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2)))))) <&&> (do
                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                 (pure ((← readReg SEE) <b 3502)))))) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3502
                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                              let U := (BitVec.slice __opcode 23 1)
                                                                                              let D := (BitVec.slice __opcode 22 1)
                                                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                                                              let size := (BitVec.slice __opcode 8 2)
                                                                                              let imm8 := (BitVec.slice __opcode 0 8)
                                                                                              (decode_aarch32_instrs_VLDR_A1enc_A_txt cond U D Rn Vd size imm8))
                                                                                          else
                                                                                            (do
                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11100#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                     (pure ((← readReg SEE) <b 3509)))))) : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3509
                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                  let D := (BitVec.slice __opcode 22 1)
                                                                                                  let Vn := (BitVec.slice __opcode 16 4)
                                                                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                                                                  let size := (BitVec.slice __opcode 8 2)
                                                                                                  let N := (BitVec.slice __opcode 7 1)
                                                                                                  let op := (BitVec.slice __opcode 6 1)
                                                                                                  let M := (BitVec.slice __opcode 5 1)
                                                                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                                                                  (decode_aarch32_instrs_VMLA_f_A2enc_A_txt cond D Vn Vd size N op M Vm))
                                                                                              else
                                                                                                (do
                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 21 16) == (0b110000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb __opcode 11 6) == (0b101001#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                                                                                                       (pure ((← readReg SEE) <b 3520))))) : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3520
                                                                                                      let D := (BitVec.slice __opcode 22 1)
                                                                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                                                                      let M := (BitVec.slice __opcode 5 1)
                                                                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                                                                      (decode_aarch32_instrs_VMOVX_A1enc_A_txt D Vd M Vm))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 21 16) == (0b110000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb __opcode 11 6) == (0b101011#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                                                                                                           (pure ((← readReg SEE) <b 3522))))) : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3522
                                                                                                          let D := (BitVec.slice __opcode 22 1)
                                                                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                                                                          let M := (BitVec.slice __opcode 5 1)
                                                                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                                                                          (decode_aarch32_instrs_VINS_A1enc_A_txt D Vd M Vm))
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 21) == (0b1100010#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb __opcode 11 6) == (0b101100#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1)))))) <&&> (do
                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                 (pure ((← readReg SEE) <b 3524)))))) : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3524
                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                              let op := (BitVec.slice __opcode 20 1)
                                                                                                              let Rt2 := (BitVec.slice __opcode 16 4)
                                                                                                              let Rt := (BitVec.slice __opcode 12 4)
                                                                                                              let M := (BitVec.slice __opcode 5 1)
                                                                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                                                                              (decode_aarch32_instrs_VMOV_d_A1enc_A_txt cond op Rt2 Rt M Vm))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 7 4) == (0x0#4 : (BitVec 4))))))) <&&> (do
                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                     (pure ((← readReg SEE) <b 3527)))))) : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3527
                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                  let D := (BitVec.slice __opcode 22 1)
                                                                                                                  let imm4H := (BitVec.slice __opcode 16 4)
                                                                                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                  let size := (BitVec.slice __opcode 8 2)
                                                                                                                  let imm4L := (BitVec.slice __opcode 0 4)
                                                                                                                  if ((((BitVec.join1 [(BitVec.access __opcode 7)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 5)]) != 0#1)) : Bool)
                                                                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                  else (decode_aarch32_instrs_VMOV_i_A2enc_A_txt cond D imm4H Vd size imm4L))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 21) == (0b1110000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 6 0) == (0b0010000#7 : (BitVec 7)))))) <&&> (do
                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                         (pure ((← readReg SEE) <b 3540)))))) : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 3540
                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                      let op := (BitVec.slice __opcode 20 1)
                                                                                                                      let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                      let Rt := (BitVec.slice __opcode 12 4)
                                                                                                                      let N := (BitVec.slice __opcode 7 1)
                                                                                                                      if ((((((((BitVec.join1 [(BitVec.access __opcode 5)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 6)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 0)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 1)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 2)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 3)]) != 0#1)) : Bool)
                                                                                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                      else (decode_aarch32_instrs_VMOV_h_A1enc_A_txt cond op Vn Rt N))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 16) == (0b110000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 7 6) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                             (pure ((← readReg SEE) <b 3542)))))) : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 3542
                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                          let D := (BitVec.slice __opcode 22 1)
                                                                                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                          let size := (BitVec.slice __opcode 8 2)
                                                                                                                          let M := (BitVec.slice __opcode 5 1)
                                                                                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                          (decode_aarch32_instrs_VMOV_r_A2enc_A_txt cond D Vd size M Vm))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11100#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0xB#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b10000#5 : (BitVec 5))))))) <&&> (do
                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                 (pure ((← readReg SEE) <b 3544)))))) : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 3544
                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                              let opc1 := (BitVec.slice __opcode 21 2)
                                                                                                                              let Vd := (BitVec.slice __opcode 16 4)
                                                                                                                              let Rt := (BitVec.slice __opcode 12 4)
                                                                                                                              let D := (BitVec.slice __opcode 7 1)
                                                                                                                              let opc2 := (BitVec.slice __opcode 5 2)
                                                                                                                              if ((((((BitVec.join1 [(BitVec.access __opcode 0)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 1)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 2)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 3)]) != 0#1)) : Bool)
                                                                                                                              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                              else (decode_aarch32_instrs_VMOV_rs_A1enc_A_txt cond opc1 Vd Rt D opc2))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 21) == (0b1110000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0xA#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 6 0) == (0b0010000#7 : (BitVec 7)))))) <&&> (do
                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                     (pure ((← readReg SEE) <b 3546)))))) : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 3546
                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                  let op := (BitVec.slice __opcode 20 1)
                                                                                                                                  let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                  let Rt := (BitVec.slice __opcode 12 4)
                                                                                                                                  let N := (BitVec.slice __opcode 7 1)
                                                                                                                                  if ((((((((BitVec.join1 [(BitVec.access __opcode 5)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 6)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 0)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 1)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 2)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 3)]) != 0#1)) : Bool)
                                                                                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                  else (decode_aarch32_instrs_VMOV_s_A1enc_A_txt cond op Vn Rt N))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 24) == (0xE#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (1#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0xB#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b10000#5 : (BitVec 5))))))) <&&> (do
                                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                         (pure ((← readReg SEE) <b 3548)))))) : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 3548
                                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                      let U := (BitVec.slice __opcode 23 1)
                                                                                                                                      let opc1 := (BitVec.slice __opcode 21 2)
                                                                                                                                      let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                      let Rt := (BitVec.slice __opcode 12 4)
                                                                                                                                      let N := (BitVec.slice __opcode 7 1)
                                                                                                                                      let opc2 := (BitVec.slice __opcode 5 2)
                                                                                                                                      if ((((((BitVec.join1 [(BitVec.access __opcode 0)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 1)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 2)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 3)]) != 0#1)) : Bool)
                                                                                                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                      else (decode_aarch32_instrs_VMOV_sr_A1enc_A_txt cond U opc1 Vn Rt N opc2))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 21) == (0b1100010#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb __opcode 11 6) == (0b101000#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1)))))) <&&> (do
                                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                             (pure ((← readReg SEE) <b 3550)))))) : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 3550
                                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                          let op := (BitVec.slice __opcode 20 1)
                                                                                                                                          let Rt2 := (BitVec.slice __opcode 16 4)
                                                                                                                                          let Rt := (BitVec.slice __opcode 12 4)
                                                                                                                                          let M := (BitVec.slice __opcode 5 1)
                                                                                                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                          (decode_aarch32_instrs_VMOV_ss_A1enc_A_txt cond op Rt2 Rt M Vm))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11100#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 6 6) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                 (pure ((← readReg SEE) <b 3553)))))) : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 3553
                                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                              let D := (BitVec.slice __opcode 22 1)
                                                                                                                                              let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                              let size := (BitVec.slice __opcode 8 2)
                                                                                                                                              let N := (BitVec.slice __opcode 7 1)
                                                                                                                                              let M := (BitVec.slice __opcode 5 1)
                                                                                                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                              (decode_aarch32_instrs_VMUL_f_A2enc_A_txt cond D Vn Vd size N M Vm))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 16) == (0b110001#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 7 6) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                     (pure ((← readReg SEE) <b 3573)))))) : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 3573
                                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                  let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                  let size := (BitVec.slice __opcode 8 2)
                                                                                                                                                  let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                  (decode_aarch32_instrs_VNEG_A2enc_A_txt cond D Vd size M Vm))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11100#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b01#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                         (pure ((← readReg SEE) <b 3576)))))) : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 3576
                                                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                      let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                      let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                      let size := (BitVec.slice __opcode 8 2)
                                                                                                                                                      let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                      let op := (BitVec.slice __opcode 6 1)
                                                                                                                                                      let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                      (decode_aarch32_instrs_VNMLA_A1enc_A_txt cond D Vn Vd size N op M Vm))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11100#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 6 6) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                             (pure ((← readReg SEE) <b 3577)))))) : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 3577
                                                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                          let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                          let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                          let size := (BitVec.slice __opcode 8 2)
                                                                                                                                                          let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                          let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                          (decode_aarch32_instrs_VNMLA_A2enc_A_txt cond D Vn Vd size N M Vm))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 16) == (0b110001#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 7 6) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                 (pure ((← readReg SEE) <b 3686)))))) : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 3686
                                                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                              let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                              let size := (BitVec.slice __opcode 8 2)
                                                                                                                                                              let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                              (decode_aarch32_instrs_VSQRT_A1enc_A_txt cond D Vd size M Vm))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b110#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 11 8) == (0xB#4 : (BitVec 4)))))) <&&> (do
                                                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                     (pure ((← readReg SEE) <b 3732)))))) : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 3732
                                                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                  let P := (BitVec.slice __opcode 24 1)
                                                                                                                                                                  let U := (BitVec.slice __opcode 23 1)
                                                                                                                                                                  let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                  let W := (BitVec.slice __opcode 21 1)
                                                                                                                                                                  let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                  let imm8 := (BitVec.slice __opcode 0 8)
                                                                                                                                                                  (decode_aarch32_instrs_VSTM_A1enc_A_txt cond P U D W Rn Vd imm8))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 25) == (0b110#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb __opcode 20 20) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 11 8) == (0xA#4 : (BitVec 4)))))) <&&> (do
                                                                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                         (pure ((← readReg SEE) <b 3733)))))) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 3733
                                                                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                      let P := (BitVec.slice __opcode 24 1)
                                                                                                                                                                      let U := (BitVec.slice __opcode 23 1)
                                                                                                                                                                      let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                      let W := (BitVec.slice __opcode 21 1)
                                                                                                                                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                      let imm8 := (BitVec.slice __opcode 0 8)
                                                                                                                                                                      (decode_aarch32_instrs_VSTM_A2enc_A_txt cond P U D W Rn Vd imm8))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 24) == (0xD#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2)))))) <&&> (do
                                                                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                             (pure ((← readReg SEE) <b 3736)))))) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 3736
                                                                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                          let U := (BitVec.slice __opcode 23 1)
                                                                                                                                                                          let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                          let size := (BitVec.slice __opcode 8 2)
                                                                                                                                                                          let imm8 := (BitVec.slice __opcode 0 8)
                                                                                                                                                                          (decode_aarch32_instrs_VSTR_A1enc_A_txt cond U D Rn Vd size imm8))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11100#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 6 6) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                                                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                 (pure ((← readReg SEE) <b 3739)))))) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 3739
                                                                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                              let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                              let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                              let size := (BitVec.slice __opcode 8 2)
                                                                                                                                                                              let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                              let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                              (decode_aarch32_instrs_VSUB_f_A2enc_A_txt cond D Vn Vd size N M Vm))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0xEF#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 0) == (0xA10#12 : (BitVec 12))))) <&&> (do
                                                                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                     (pure ((← readReg SEE) <b 3796)))))) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 3796
                                                                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                  let reg := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                  let Rt := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                  if ((((((((BitVec.join1 [(BitVec.access __opcode 5)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 6)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 0)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 1)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 2)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 3)]) != 0#1)) : Bool)
                                                                                                                                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                  else (decode_aarch32_instrs_VMRS_A1enc_AS_txt cond reg Rt))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 20) == (0xEE#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 11 0) == (0xA10#12 : (BitVec 12))))) <&&> (do
                                                                                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                         (pure ((← readReg SEE) <b 3798)))))) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      writeReg SEE 3798
                                                                                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                      let reg := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                      let Rt := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                      if ((((((((BitVec.join1 [(BitVec.access __opcode 5)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 6)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 0)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 1)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 2)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 3)]) != 0#1)) : Bool)
                                                                                                                                                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                      else (decode_aarch32_instrs_VMSR_A1enc_AS_txt cond reg Rt))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 21 18) == (0xF#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 6 6) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                                                                                                                                                                           (pure ((← readReg SEE) <b 3868))))) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          writeReg SEE 3868
                                                                                                                                                                                          let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                          let RM := (BitVec.slice __opcode 16 2)
                                                                                                                                                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                          let size := (BitVec.slice __opcode 8 2)
                                                                                                                                                                                          let op := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                          let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                          (decode_aarch32_instrs_VCVTA_vfp_A1enc_A_txt D RM Vd size op M Vm))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                                                                               (pure ((← readReg SEE) <b 3871))))) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              writeReg SEE 3871
                                                                                                                                                                                              let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                              let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                              let size := (BitVec.slice __opcode 8 2)
                                                                                                                                                                                              let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                              let op := (BitVec.slice __opcode 6 1)
                                                                                                                                                                                              let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                              (decode_aarch32_instrs_VMAXNM_A2enc_A_txt D Vn Vd size N op M Vm))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 21 18) == (0xE#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 7 6) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                                                                                                                                                                                   (pure ((← readReg SEE) <b 3876))))) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  writeReg SEE 3876
                                                                                                                                                                                                  let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                  let RM := (BitVec.slice __opcode 16 2)
                                                                                                                                                                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                  let size := (BitVec.slice __opcode 8 2)
                                                                                                                                                                                                  let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                  (decode_aarch32_instrs_VRINTA_vfp_A1enc_A_txt D RM Vd size M Vm))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 16) == (0b110111#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 7 6) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                                                                                                                                                                                       (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                         (pure ((← readReg SEE) <b 3880)))))) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      writeReg SEE 3880
                                                                                                                                                                                                      let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                      let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                      let size := (BitVec.slice __opcode 8 2)
                                                                                                                                                                                                      let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                      (decode_aarch32_instrs_VRINTX_vfp_A1enc_A_txt cond D Vd size M Vm))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 16) == (0b110110#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 6 6) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                                                                                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                             (pure ((← readReg SEE) <b 3884)))))) : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          writeReg SEE 3884
                                                                                                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                          let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                          let size := (BitVec.slice __opcode 8 2)
                                                                                                                                                                                                          let op := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                          let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                          (decode_aarch32_instrs_VRINTZ_vfp_A1enc_A_txt cond D Vd size op M Vm))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111111100#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 11 10) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 6 6) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                                                                                               (pure ((← readReg SEE) <b 3886))))) : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              writeReg SEE 3886
                                                                                                                                                                                                              let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                              let cc := (BitVec.slice __opcode 20 2)
                                                                                                                                                                                                              let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                              let size := (BitVec.slice __opcode 8 2)
                                                                                                                                                                                                              let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                              let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                              (decode_aarch32_instrs_VSEL_A1enc_A_txt D cc Vn Vd size N M Vm))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111111000#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 11 8) == (0xD#4 : (BitVec 4)))))) <&&> (do
                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 3900))))) : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  writeReg SEE 3900
                                                                                                                                                                                                                  let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                  let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                  let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                                  let Q := (BitVec.slice __opcode 6 1)
                                                                                                                                                                                                                  let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                  let U := (BitVec.slice __opcode 4 1)
                                                                                                                                                                                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                  (decode_aarch32_instrs_VDOT_A1enc_A_txt D Vn Vd N Q M U Vm))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111111100#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 11 8) == (0xD#4 : (BitVec 4)))))) <&&> (do
                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 3902))))) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      writeReg SEE 3902
                                                                                                                                                                                                                      let op1 := (BitVec.slice __opcode 23 1)
                                                                                                                                                                                                                      let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                      let op2 := (BitVec.slice __opcode 20 2)
                                                                                                                                                                                                                      let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                      let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                                      let Q := (BitVec.slice __opcode 6 1)
                                                                                                                                                                                                                      let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                      let U := (BitVec.slice __opcode 4 1)
                                                                                                                                                                                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                      (decode_aarch32_instrs_VDOT_s_A1enc_A_txt op1 D op2 Vn Vd N Q M U Vm))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 16) == (0b111001#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb __opcode 11 6) == (0b101111#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                                                                                                           (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                             (pure ((← readReg SEE) <b 3904)))))) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          writeReg SEE 3904
                                                                                                                                                                                                                          let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                          let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                          let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                          (decode_aarch32_instrs_VJCVT_A1enc_A_txt cond D Vd M Vm))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 25) == (0b1111110#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb __opcode 21 21) == (1#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 3906))))) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              writeReg SEE 3906
                                                                                                                                                                                                                              let rot := (BitVec.slice __opcode 23 2)
                                                                                                                                                                                                                              let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                              let S := (BitVec.slice __opcode 20 1)
                                                                                                                                                                                                                              let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                              let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                                              let Q := (BitVec.slice __opcode 6 1)
                                                                                                                                                                                                                              let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                              (decode_aarch32_instrs_VCMLA_A1enc_A_txt rot D S Vn Vd N Q M Vm))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 24) == (0xFE#8 : (BitVec 8))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))) <&&> (do
                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 3908))))) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  writeReg SEE 3908
                                                                                                                                                                                                                                  let S := (BitVec.slice __opcode 23 1)
                                                                                                                                                                                                                                  let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                                  let rot := (BitVec.slice __opcode 20 2)
                                                                                                                                                                                                                                  let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                  let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                                                  let Q := (BitVec.slice __opcode 6 1)
                                                                                                                                                                                                                                  let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                  (decode_aarch32_instrs_VCMLA_idx_A1enc_A_txt S D rot Vn Vd N Q M Vm))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 25) == (0b1111110#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb __opcode 23 23) == (1#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 21 21) == (0#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 3910))))) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      writeReg SEE 3910
                                                                                                                                                                                                                                      let rot := (BitVec.slice __opcode 24 1)
                                                                                                                                                                                                                                      let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                                      let S := (BitVec.slice __opcode 20 1)
                                                                                                                                                                                                                                      let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                      let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                                                      let Q := (BitVec.slice __opcode 6 1)
                                                                                                                                                                                                                                      let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                      (decode_aarch32_instrs_VCADD_A1enc_A_txt rot D S Vn Vd N Q M Vm))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 24) == (0xFC#8 : (BitVec 8))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 3912))))) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          writeReg SEE 3912
                                                                                                                                                                                                                                          let S := (BitVec.slice __opcode 23 1)
                                                                                                                                                                                                                                          let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                                          let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                          let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                                                          let Q := (BitVec.slice __opcode 6 1)
                                                                                                                                                                                                                                          let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                          (decode_aarch32_instrs_VFMAL_A1enc_A_txt S D Vn Vd N Q M Vm))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111111100#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 21 21) == (0#1 : (BitVec 1))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 3914))))) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              writeReg SEE 3914
                                                                                                                                                                                                                                              let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                                              let S := (BitVec.slice __opcode 20 1)
                                                                                                                                                                                                                                              let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                              let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                                                              let Q := (BitVec.slice __opcode 6 1)
                                                                                                                                                                                                                                              let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                              (decode_aarch32_instrs_VFMAL_i_A1enc_A_txt D S Vn Vd N Q M Vm))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111111000#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 3916))))) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  writeReg SEE 3916
                                                                                                                                                                                                                                                  let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                                                  let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                  let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                                                                  let Q := (BitVec.slice __opcode 6 1)
                                                                                                                                                                                                                                                  let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                  (decode_aarch32_instrs_VDOT_bf16_A1enc_A_txt D Vn Vd N Q M Vm))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111111100#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 3918))))) : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      writeReg SEE 3918
                                                                                                                                                                                                                                                      let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                                                      let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                      let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                                                                      let Q := (BitVec.slice __opcode 6 1)
                                                                                                                                                                                                                                                      let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                      (decode_aarch32_instrs_VDOT_bf16_i_A1enc_A_txt D Vn Vd N Q M Vm))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111111000#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0xC#4 : (BitVec 4))) && (((Sail.BitVec.extractLsb __opcode 6 6) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1)))))))) <&&> (do
                                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 3920))))) : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          writeReg SEE 3920
                                                                                                                                                                                                                                                          let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                                                          let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                          let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                                                                          let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                          (decode_aarch32_instrs_VMMLA_A1enc_A_txt D Vn Vd N M Vm))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 16) == (0b110011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb __opcode 11 6) == (0b100101#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                                                                                                                                               (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                                 (pure ((← readReg SEE) <b 3924)))))) : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              writeReg SEE 3924
                                                                                                                                                                                                                                                              let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                              let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                              let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                              (decode_aarch32_instrs_VCVTB_bf16_A1enc_A_txt cond D Vd M Vm))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 27 23) == (0b11101#5 : (BitVec 5))) && (((Sail.BitVec.extractLsb __opcode 21 16) == (0b110011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb __opcode 11 6) == (0b100111#6 : (BitVec 6))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                                                                                                                                                   (pure ((BitVec.slice __opcode 28 4) != 0b1111#4)) <&&> (do
                                                                                                                                                                                                                                                                     (pure ((← readReg SEE) <b 3926)))))) : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  writeReg SEE 3926
                                                                                                                                                                                                                                                                  let cond := (BitVec.slice __opcode 28 4)
                                                                                                                                                                                                                                                                  let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                  let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_VCVTT_A1enc_A_txt cond D Vd M Vm))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111111000#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 3928))))) : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      writeReg SEE 3928
                                                                                                                                                                                                                                                                      let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                                                                      let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                      let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                                                                                      let Q := (BitVec.slice __opcode 6 1)
                                                                                                                                                                                                                                                                      let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_VFMA_bf_A1enc_A_txt D Vn Vd N Q M Vm))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111111100#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 3930))))) : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          writeReg SEE 3930
                                                                                                                                                                                                                                                                          let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                                                                          let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                          let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                                                                                          let Q := (BitVec.slice __opcode 6 1)
                                                                                                                                                                                                                                                                          let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                          (decode_aarch32_instrs_VFMA_bfs_A1enc_A_txt D Vn Vd N Q M Vm))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 24) == (0xFC#8 : (BitVec 8))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 6 6) == (1#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 3932))))) : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              writeReg SEE 3932
                                                                                                                                                                                                                                                                              let B := (BitVec.slice __opcode 23 1)
                                                                                                                                                                                                                                                                              let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                                                                              let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                              let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                                                                                              let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                                                                              let U := (BitVec.slice __opcode 4 1)
                                                                                                                                                                                                                                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                              (decode_aarch32_instrs_MMLA_A1enc_A_txt B D Vn Vd N M U Vm))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111111001#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb __opcode 11 8) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))))) <&&> (do
                                                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 3934))))) : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  writeReg SEE 3934
                                                                                                                                                                                                                                                                                  let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                                                                                  let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                                  let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                                                                                                  let Q := (BitVec.slice __opcode 6 1)
                                                                                                                                                                                                                                                                                  let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                                                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                                  (decode_aarch32_instrs_VUSDOT_A1enc_A_txt D Vn Vd N Q M Vm))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 23) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.extractLsb __opcode 21 20) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb __opcode 11 8) == (0xD#4 : (BitVec 4)))))) <&&> (do
                                                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 3936))))) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      writeReg SEE 3936
                                                                                                                                                                                                                                                                                      let D := (BitVec.slice __opcode 22 1)
                                                                                                                                                                                                                                                                                      let Vn := (BitVec.slice __opcode 16 4)
                                                                                                                                                                                                                                                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                                                                      let N := (BitVec.slice __opcode 7 1)
                                                                                                                                                                                                                                                                                      let Q := (BitVec.slice __opcode 6 1)
                                                                                                                                                                                                                                                                                      let M := (BitVec.slice __opcode 5 1)
                                                                                                                                                                                                                                                                                      let U := (BitVec.slice __opcode 4 1)
                                                                                                                                                                                                                                                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                                                                                                                                                                                                                                                      (decode_aarch32_instrs_DOT_A1enc_A_txt D Vn Vd N Q M U Vm))
                                                                                                                                                                                                                                                                                  else (sailThrow ((Error_Undefined ())) : SailM Unit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


