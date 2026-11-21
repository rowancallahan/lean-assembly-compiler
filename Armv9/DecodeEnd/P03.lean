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
def __DecodeA64_BranchExcSys (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 10) == (0b1101010100000011001000#22 : (BitVec 22))) && (((Sail.BitVec.extractLsb __opcode 8 6) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b11111#5 : (BitVec 5)))))) <&&> (do
       (pure ((← readReg SEE) <b 63))))) : Bool)
  then
    (do
      writeReg SEE 63
      let op2 := (BitVec.slice __opcode 5 3)
      let CRm := (BitVec.slice __opcode 8 4)
      (decode_autia_aarch64_instrs_integer_pac_autia_hint op2 CRm))
  else
    (do
      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 10) == (0b1101010100000011001000#22 : (BitVec 22))) && (((Sail.BitVec.extractLsb __opcode 8 6) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b11111#5 : (BitVec 5)))))) <&&> (do
           (pure ((← readReg SEE) <b 65))))) : Bool)
      then
        (do
          writeReg SEE 65
          let op2 := (BitVec.slice __opcode 5 3)
          let CRm := (BitVec.slice __opcode 8 4)
          (decode_autib_aarch64_instrs_integer_pac_autib_hint op2 CRm))
      else
        (do
          if ((←((pure (__opcode == (0xD500405F#32 : (BitVec 32)))) <&&> (do
               (pure ((← readReg SEE) <b 66))))) : Bool)
          then
            (do
              writeReg SEE 66
              let CRm := (BitVec.slice __opcode 8 4)
              if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 0#1)) : Bool)
              then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
              else (decode_axflag_aarch64_instrs_integer_flags_axflag CRm))
          else
            (do
              if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 26) == (0b000101#6 : (BitVec 6)))) <&&> (do
                   (pure ((← readReg SEE) <b 67))))) : Bool)
              then
                (do
                  writeReg SEE 67
                  let imm26 := (BitVec.slice __opcode 0 26)
                  let op := (BitVec.slice __opcode 31 1)
                  (decode_b_uncond_aarch64_instrs_branch_unconditional_immediate imm26 op))
              else
                (do
                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 26) == (0b100101#6 : (BitVec 6)))) <&&> (do
                       (pure ((← readReg SEE) <b 68))))) : Bool)
                  then
                    (do
                      writeReg SEE 68
                      let imm26 := (BitVec.slice __opcode 0 26)
                      let op := (BitVec.slice __opcode 31 1)
                      (decode_bl_aarch64_instrs_branch_unconditional_immediate imm26 op))
                  else
                    (do
                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 24) == (0x54#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (0#1 : (BitVec 1))))) <&&> (do
                           (pure ((← readReg SEE) <b 69))))) : Bool)
                      then
                        (do
                          writeReg SEE 69
                          let cond := (BitVec.slice __opcode 0 4)
                          let imm19 := (BitVec.slice __opcode 5 19)
                          (decode_b_cond_aarch64_instrs_branch_conditional_cond cond imm19))
                      else
                        (do
                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 24) == (0x54#8 : (BitVec 8))) && ((Sail.BitVec.extractLsb __opcode 4 4) == (1#1 : (BitVec 1))))) <&&> (do
                               (pure ((← readReg SEE) <b 70))))) : Bool)
                          then
                            (do
                              writeReg SEE 70
                              let cond := (BitVec.slice __opcode 0 4)
                              let imm19 := (BitVec.slice __opcode 5 19)
                              (decode_bc_cond_aarch64_instrs_branch_conditional_hinted cond imm19))
                          else
                            (do
                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 10) == (0b1101011000111111000000#22 : (BitVec 22))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b00000#5 : (BitVec 5))))) <&&> (do
                                   (pure ((← readReg SEE) <b 90))))) : Bool)
                              then
                                (do
                                  writeReg SEE 90
                                  let Rm := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let M := (BitVec.slice __opcode 10 1)
                                  let A := (BitVec.slice __opcode 11 1)
                                  let op := (BitVec.slice __opcode 21 2)
                                  let Z := (BitVec.slice __opcode 24 1)
                                  (decode_blr_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z))
                              else
                                (do
                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 25) == (0b1101011#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 23 11) == (0b0011111100001#13 : (BitVec 13))))) <&&> (do
                                       (pure ((← readReg SEE) <b 91))))) : Bool)
                                  then
                                    (do
                                      writeReg SEE 91
                                      let Rm := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let M := (BitVec.slice __opcode 10 1)
                                      let A := (BitVec.slice __opcode 11 1)
                                      let op := (BitVec.slice __opcode 21 2)
                                      let Z := (BitVec.slice __opcode 24 1)
                                      (decode_blra_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z))
                                  else
                                    (do
                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 10) == (0b1101011000011111000000#22 : (BitVec 22))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b00000#5 : (BitVec 5))))) <&&> (do
                                           (pure ((← readReg SEE) <b 92))))) : Bool)
                                      then
                                        (do
                                          writeReg SEE 92
                                          let Rm := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let M := (BitVec.slice __opcode 10 1)
                                          let A := (BitVec.slice __opcode 11 1)
                                          let op := (BitVec.slice __opcode 21 2)
                                          let Z := (BitVec.slice __opcode 24 1)
                                          (decode_br_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z))
                                      else
                                        (do
                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 25) == (0b1101011#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb __opcode 23 11) == (0b0001111100001#13 : (BitVec 13))))) <&&> (do
                                               (pure ((← readReg SEE) <b 93))))) : Bool)
                                          then
                                            (do
                                              writeReg SEE 93
                                              let Rm := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let M := (BitVec.slice __opcode 10 1)
                                              let A := (BitVec.slice __opcode 11 1)
                                              let op := (BitVec.slice __opcode 21 2)
                                              let Z := (BitVec.slice __opcode 24 1)
                                              (decode_bra_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z))
                                          else
                                            (do
                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 10) == (0b1101011001011111000000#22 : (BitVec 22))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b00000#5 : (BitVec 5))))) <&&> (do
                                                   (pure ((← readReg SEE) <b 94))))) : Bool)
                                              then
                                                (do
                                                  writeReg SEE 94
                                                  let Rm := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let M := (BitVec.slice __opcode 10 1)
                                                  let A := (BitVec.slice __opcode 11 1)
                                                  let op := (BitVec.slice __opcode 21 2)
                                                  let Z := (BitVec.slice __opcode 24 1)
                                                  (decode_ret_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z))
                                              else
                                                (do
                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 11) == (0b110101100101111100001#21 : (BitVec 21))) && ((Sail.BitVec.extractLsb __opcode 9 0) == (0b1111111111#10 : (BitVec 10))))) <&&> (do
                                                       (pure ((← readReg SEE) <b 95))))) : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 95
                                                      let Rm := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let M := (BitVec.slice __opcode 10 1)
                                                      let A := (BitVec.slice __opcode 11 1)
                                                      let op := (BitVec.slice __opcode 21 2)
                                                      let Z := (BitVec.slice __opcode 24 1)
                                                      (decode_reta_aarch64_instrs_branch_unconditional_register Rm Rn M A op Z))
                                                  else
                                                    (do
                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11010100001#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b00000#5 : (BitVec 5))))) <&&> (do
                                                           (pure ((← readReg SEE) <b 96))))) : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 96
                                                          let imm16 := (BitVec.slice __opcode 5 16)
                                                          (decode_brk_aarch64_instrs_system_exceptions_debug_breakpoint imm16))
                                                      else
                                                        (do
                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 8) == (0xD50324#24 : (BitVec 24))) && ((Sail.BitVec.extractLsb __opcode 5 0) == (0b011111#6 : (BitVec 6))))) <&&> (do
                                                               (pure ((← readReg SEE) <b 97))))) : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 97
                                                              let op2 := (BitVec.slice __opcode 5 3)
                                                              let CRm := (BitVec.slice __opcode 8 4)
                                                              (decode_bti_aarch64_instrs_system_hints op2 CRm))
                                                          else
                                                            (do
                                                              if ((←((pure (__opcode == (0xD503251F#32 : (BitVec 32)))) <&&> (do
                                                                   (pure ((← readReg SEE) <b 98))))) : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 98
                                                                  let op2 := (BitVec.slice __opcode 5 3)
                                                                  let CRm := (BitVec.slice __opcode 8 4)
                                                                  (decode_chkfeat_aarch64_instrs_system_hints op2 CRm))
                                                              else
                                                                (do
                                                                  if ((←((pure (__opcode == (0xD50322DF#32 : (BitVec 32)))) <&&> (do
                                                                       (pure ((← readReg SEE) <b 99))))) : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 99
                                                                      let op2 := (BitVec.slice __opcode 5 3)
                                                                      let CRm := (BitVec.slice __opcode 8 4)
                                                                      (decode_clrbhb_aarch64_instrs_system_hints op2 CRm))
                                                                  else
                                                                    (do
                                                                      if ((←((pure (__opcode == (0xD503229F#32 : (BitVec 32)))) <&&> (do
                                                                           (pure ((← readReg SEE) <b 100))))) : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 100
                                                                          let op2 := (BitVec.slice __opcode 5 3)
                                                                          let CRm := (BitVec.slice __opcode 8 4)
                                                                          (decode_csdb_aarch64_instrs_system_hints op2 CRm))
                                                                      else
                                                                        (do
                                                                          if ((←((pure (__opcode == (0xD50320DF#32 : (BitVec 32)))) <&&> (do
                                                                               (pure ((← readReg SEE) <b 101))))) : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 101
                                                                              let op2 := (BitVec.slice __opcode 5 3)
                                                                              let CRm := (BitVec.slice __opcode 8 4)
                                                                              (decode_dgh_aarch64_instrs_system_hints op2 CRm))
                                                                          else
                                                                            (do
                                                                              if ((←((pure (__opcode == (0xD503221F#32 : (BitVec 32)))) <&&> (do
                                                                                   (pure ((← readReg SEE) <b 102))))) : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 102
                                                                                  let op2 := (BitVec.slice __opcode 5 3)
                                                                                  let CRm := (BitVec.slice __opcode 8 4)
                                                                                  (decode_esb_aarch64_instrs_system_hints op2 CRm))
                                                                              else
                                                                                (do
                                                                                  if ((←((pure (__opcode == (0xD503227F#32 : (BitVec 32)))) <&&> (do
                                                                                       (pure ((← readReg SEE) <b 103))))) : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 103
                                                                                      let op2 := (BitVec.slice __opcode 5 3)
                                                                                      let CRm := (BitVec.slice __opcode 8 4)
                                                                                      (decode_gcsb_aarch64_instrs_system_hints op2 CRm))
                                                                                  else
                                                                                    (do
                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 12) == (0xD5032#20 : (BitVec 20))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b11111#5 : (BitVec 5))))) <&&> (do
                                                                                           (pure ((← readReg SEE) <b 104))))) : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 104
                                                                                          let op2 := (BitVec.slice __opcode 5 3)
                                                                                          let CRm := (BitVec.slice __opcode 8 4)
                                                                                          (decode_hint_aarch64_instrs_system_hints op2 CRm))
                                                                                      else
                                                                                        (do
                                                                                          if ((←((pure (__opcode == (0xD503201F#32 : (BitVec 32)))) <&&> (do
                                                                                               (pure ((← readReg SEE) <b 105))))) : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 105
                                                                                              let op2 := (BitVec.slice __opcode 5 3)
                                                                                              let CRm := (BitVec.slice __opcode 8 4)
                                                                                              (decode_nop_aarch64_instrs_system_hints op2 CRm))
                                                                                          else
                                                                                            (do
                                                                                              if ((←((pure (__opcode == (0xD503223F#32 : (BitVec 32)))) <&&> (do
                                                                                                   (pure ((← readReg SEE) <b 106))))) : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 106
                                                                                                  let op2 := (BitVec.slice __opcode 5 3)
                                                                                                  let CRm := (BitVec.slice __opcode 8 4)
                                                                                                  (decode_psb_aarch64_instrs_system_hints op2 CRm))
                                                                                              else
                                                                                                (do
                                                                                                  if ((←((pure (__opcode == (0xD503209F#32 : (BitVec 32)))) <&&> (do
                                                                                                       (pure ((← readReg SEE) <b 107))))) : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 107
                                                                                                      let op2 := (BitVec.slice __opcode 5 3)
                                                                                                      let CRm := (BitVec.slice __opcode 8 4)
                                                                                                      (decode_sev_aarch64_instrs_system_hints op2 CRm))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((←((pure (__opcode == (0xD50320BF#32 : (BitVec 32)))) <&&> (do
                                                                                                           (pure ((← readReg SEE) <b 108))))) : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 108
                                                                                                          let op2 := (BitVec.slice __opcode 5 3)
                                                                                                          let CRm := (BitVec.slice __opcode 8 4)
                                                                                                          (decode_sevl_aarch64_instrs_system_hints op2 CRm))
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((←((pure (__opcode == (0xD503225F#32 : (BitVec 32)))) <&&> (do
                                                                                                               (pure ((← readReg SEE) <b 109))))) : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 109
                                                                                                              let op2 := (BitVec.slice __opcode 5 3)
                                                                                                              let CRm := (BitVec.slice __opcode 8 4)
                                                                                                              (decode_tsb_aarch64_instrs_system_hints op2 CRm))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((←((pure (__opcode == (0xD503205F#32 : (BitVec 32)))) <&&> (do
                                                                                                                   (pure ((← readReg SEE) <b 110))))) : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 110
                                                                                                                  let op2 := (BitVec.slice __opcode 5 3)
                                                                                                                  let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                  (decode_wfe_aarch64_instrs_system_hints op2 CRm))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((←((pure (__opcode == (0xD503207F#32 : (BitVec 32)))) <&&> (do
                                                                                                                       (pure ((← readReg SEE) <b 111))))) : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 111
                                                                                                                      let op2 := (BitVec.slice __opcode 5 3)
                                                                                                                      let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                      (decode_wfi_aarch64_instrs_system_hints op2 CRm))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if ((←((pure (__opcode == (0xD503203F#32 : (BitVec 32)))) <&&> (do
                                                                                                                           (pure ((← readReg SEE) <b 112))))) : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 112
                                                                                                                          let op2 := (BitVec.slice __opcode 5 3)
                                                                                                                          let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                          (decode_yield_aarch64_instrs_system_hints op2 CRm))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 24) == (0b0110101#7 : (BitVec 7)))) <&&> (do
                                                                                                                               (pure ((← readReg SEE) <b 117))))) : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 117
                                                                                                                              let Rt := (BitVec.slice __opcode 0 5)
                                                                                                                              let imm19 := (BitVec.slice __opcode 5 19)
                                                                                                                              let op := (BitVec.slice __opcode 24 1)
                                                                                                                              let sf := (BitVec.slice __opcode 31 1)
                                                                                                                              (decode_cbnz_aarch64_instrs_branch_conditional_compare Rt imm19 op sf))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 24) == (0b0110100#7 : (BitVec 7)))) <&&> (do
                                                                                                                                   (pure ((← readReg SEE) <b 118))))) : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 118
                                                                                                                                  let Rt := (BitVec.slice __opcode 0 5)
                                                                                                                                  let imm19 := (BitVec.slice __opcode 5 19)
                                                                                                                                  let op := (BitVec.slice __opcode 24 1)
                                                                                                                                  let sf := (BitVec.slice __opcode 31 1)
                                                                                                                                  (decode_cbz_aarch64_instrs_branch_conditional_compare Rt imm19 op sf))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  if ((←((pure (__opcode == (0xD500401F#32 : (BitVec 32)))) <&&> (do
                                                                                                                                       (pure ((← readReg SEE) <b 123))))) : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 123
                                                                                                                                      let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                      if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 0#1)) : Bool)
                                                                                                                                      then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                      else (decode_cfinv_aarch64_instrs_integer_flags_cfinv CRm))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 12) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.extractLsb __opcode 7 0) == (0x5F#8 : (BitVec 8))))) <&&> (do
                                                                                                                                           (pure ((← readReg SEE) <b 124))))) : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 124
                                                                                                                                          let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                          (pure (decode_clrex_aarch64_instrs_system_monitors CRm)))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11010100101#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b00001#5 : (BitVec 5))))) <&&> (do
                                                                                                                                               (pure ((← readReg SEE) <b 192))))) : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 192
                                                                                                                                              let LL := (BitVec.slice __opcode 0 2)
                                                                                                                                              let imm16 := (BitVec.slice __opcode 5 16)
                                                                                                                                              (decode_dcps1_aarch64_instrs_system_exceptions_debug_exception LL imm16))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11010100101#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b00010#5 : (BitVec 5))))) <&&> (do
                                                                                                                                                   (pure ((← readReg SEE) <b 193))))) : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 193
                                                                                                                                                  let LL := (BitVec.slice __opcode 0 2)
                                                                                                                                                  let imm16 := (BitVec.slice __opcode 5 16)
                                                                                                                                                  (decode_dcps2_aarch64_instrs_system_exceptions_debug_exception LL imm16))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11010100101#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b00011#5 : (BitVec 5))))) <&&> (do
                                                                                                                                                       (pure ((← readReg SEE) <b 194))))) : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 194
                                                                                                                                                      let LL := (BitVec.slice __opcode 0 2)
                                                                                                                                                      let imm16 := (BitVec.slice __opcode 5 16)
                                                                                                                                                      (decode_dcps3_aarch64_instrs_system_exceptions_debug_exception LL imm16))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 12) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.extractLsb __opcode 7 0) == (0xBF#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                           (pure ((← readReg SEE) <b 195))))) : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 195
                                                                                                                                                          let opc := (BitVec.slice __opcode 5 2)
                                                                                                                                                          let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                                          (decode_dmb_aarch64_instrs_system_barriers_dmb opc CRm))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          if ((←((pure (__opcode == (0xD6BF03E0#32 : (BitVec 32)))) <&&> (do
                                                                                                                                                               (pure ((← readReg SEE) <b 196))))) : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 196
                                                                                                                                                              (decode_drps_aarch64_instrs_branch_unconditional_dret ()))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 12) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.extractLsb __opcode 7 0) == (0x9F#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                   (pure ((← readReg SEE) <b 197))))) : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 197
                                                                                                                                                                  let opc := (BitVec.slice __opcode 5 2)
                                                                                                                                                                  let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                  (decode_dsb_aarch64_instrs_system_barriers_dsb opc CRm))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 12) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.extractLsb __opcode 9 0) == (0b1000111111#10 : (BitVec 10))))) <&&> (do
                                                                                                                                                                       (pure ((← readReg SEE) <b 198))))) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 198
                                                                                                                                                                      let imm2 := (BitVec.slice __opcode 10 2)
                                                                                                                                                                      (decode_dsb_aarch64_instrs_system_barriers_dsb_nxs imm2))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      if ((←((pure (__opcode == (0xD69F03E0#32 : (BitVec 32)))) <&&> (do
                                                                                                                                                                           (pure ((← readReg SEE) <b 203))))) : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 203
                                                                                                                                                                          let op4 := (BitVec.slice __opcode 0 5)
                                                                                                                                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                          let M := (BitVec.slice __opcode 10 1)
                                                                                                                                                                          let A := (BitVec.slice __opcode 11 1)
                                                                                                                                                                          (decode_eret_aarch64_instrs_branch_unconditional_eret op4 Rn M A))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 11) == (0b110101101001111100001#21 : (BitVec 21))) && ((Sail.BitVec.extractLsb __opcode 9 0) == (0b1111111111#10 : (BitVec 10))))) <&&> (do
                                                                                                                                                                               (pure ((← readReg SEE) <b 204))))) : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 204
                                                                                                                                                                              let op4 := (BitVec.slice __opcode 0 5)
                                                                                                                                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                                                                                                                                              let M := (BitVec.slice __opcode 10 1)
                                                                                                                                                                              let A := (BitVec.slice __opcode 11 1)
                                                                                                                                                                              (decode_ereta_aarch64_instrs_branch_unconditional_eret op4 Rn M A))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11010100010#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b00000#5 : (BitVec 5))))) <&&> (do
                                                                                                                                                                                   (pure ((← readReg SEE) <b 478))))) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 478
                                                                                                                                                                                  let imm16 := (BitVec.slice __opcode 5 16)
                                                                                                                                                                                  (decode_hlt_aarch64_instrs_system_exceptions_debug_halt imm16))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11010100000#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b00010#5 : (BitVec 5))))) <&&> (do
                                                                                                                                                                                       (pure ((← readReg SEE) <b 479))))) : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      writeReg SEE 479
                                                                                                                                                                                      let imm16 := (BitVec.slice __opcode 5 16)
                                                                                                                                                                                      (decode_hvc_aarch64_instrs_system_exceptions_runtime_hvc imm16))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 12) == (0xD5033#20 : (BitVec 20))) && ((Sail.BitVec.extractLsb __opcode 7 0) == (0xDF#8 : (BitVec 8))))) <&&> (do
                                                                                                                                                                                           (pure ((← readReg SEE) <b 483))))) : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          writeReg SEE 483
                                                                                                                                                                                          let opc := (BitVec.slice __opcode 5 2)
                                                                                                                                                                                          let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                                          (decode_isb_aarch64_instrs_system_barriers_isb opc CRm))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 20) == (0xD57#12 : (BitVec 12)))) <&&> (do
                                                                                                                                                                                               (pure ((← readReg SEE) <b 699))))) : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              writeReg SEE 699
                                                                                                                                                                                              let Rt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                              let op2 := (BitVec.slice __opcode 5 3)
                                                                                                                                                                                              let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                                              let CRn := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                              let op1 := (BitVec.slice __opcode 16 3)
                                                                                                                                                                                              let o0 := (BitVec.slice __opcode 19 1)
                                                                                                                                                                                              let L := (BitVec.slice __opcode 21 1)
                                                                                                                                                                                              (decode_mrrs_aarch64_instrs_system_register_system_128 Rt op2 CRm CRn op1 o0 L))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 20) == (0xD55#12 : (BitVec 12)))) <&&> (do
                                                                                                                                                                                                   (pure ((← readReg SEE) <b 700))))) : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  writeReg SEE 700
                                                                                                                                                                                                  let Rt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                  let op2 := (BitVec.slice __opcode 5 3)
                                                                                                                                                                                                  let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                                                  let CRn := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                  let op1 := (BitVec.slice __opcode 16 3)
                                                                                                                                                                                                  let o0 := (BitVec.slice __opcode 19 1)
                                                                                                                                                                                                  let L := (BitVec.slice __opcode 21 1)
                                                                                                                                                                                                  (decode_msrr_aarch64_instrs_system_register_system_128 Rt op2 CRm CRn op1 o0 L))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 20) == (0xD53#12 : (BitVec 12)))) <&&> (do
                                                                                                                                                                                                       (pure ((← readReg SEE) <b 701))))) : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      writeReg SEE 701
                                                                                                                                                                                                      let Rt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                      let op2 := (BitVec.slice __opcode 5 3)
                                                                                                                                                                                                      let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                                                      let CRn := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                      let op1 := (BitVec.slice __opcode 16 3)
                                                                                                                                                                                                      let o0 := (BitVec.slice __opcode 19 1)
                                                                                                                                                                                                      let L := (BitVec.slice __opcode 21 1)
                                                                                                                                                                                                      (decode_mrs_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 20) == (0xD51#12 : (BitVec 12)))) <&&> (do
                                                                                                                                                                                                           (pure ((← readReg SEE) <b 702))))) : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          writeReg SEE 702
                                                                                                                                                                                                          let Rt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                          let op2 := (BitVec.slice __opcode 5 3)
                                                                                                                                                                                                          let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                                                          let CRn := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                          let op1 := (BitVec.slice __opcode 16 3)
                                                                                                                                                                                                          let o0 := (BitVec.slice __opcode 19 1)
                                                                                                                                                                                                          let L := (BitVec.slice __opcode 21 1)
                                                                                                                                                                                                          (decode_msr_reg_aarch64_instrs_system_register_system Rt op2 CRm CRn op1 o0 L))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 19) == (0b1101010100000#13 : (BitVec 13))) && (((Sail.BitVec.extractLsb __opcode 15 12) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b11111#5 : (BitVec 5)))))) <&&> (do
                                                                                                                                                                                                               (pure ((← readReg SEE) <b 703))))) : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              writeReg SEE 703
                                                                                                                                                                                                              let op2 := (BitVec.slice __opcode 5 3)
                                                                                                                                                                                                              let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                                                              let op1 := (BitVec.slice __opcode 16 3)
                                                                                                                                                                                                              (decode_msr_imm_aarch64_instrs_system_register_cpsr op2 CRm op1))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 10) == (0b1101010100000011001000#22 : (BitVec 22))) && (((Sail.BitVec.extractLsb __opcode 8 6) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b11111#5 : (BitVec 5)))))) <&&> (do
                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 712))))) : Bool)
                                                                                                                                                                                                              then
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  writeReg SEE 712
                                                                                                                                                                                                                  let op2 := (BitVec.slice __opcode 5 3)
                                                                                                                                                                                                                  let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                                                                  (decode_pacia_aarch64_instrs_integer_pac_pacia_hint op2 CRm))
                                                                                                                                                                                                              else
                                                                                                                                                                                                                (do
                                                                                                                                                                                                                  if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 10) == (0b1101010100000011001000#22 : (BitVec 22))) && (((Sail.BitVec.extractLsb __opcode 8 6) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b11111#5 : (BitVec 5)))))) <&&> (do
                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 714))))) : Bool)
                                                                                                                                                                                                                  then
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      writeReg SEE 714
                                                                                                                                                                                                                      let op2 := (BitVec.slice __opcode 5 3)
                                                                                                                                                                                                                      let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                                                                      (decode_pacib_aarch64_instrs_integer_pac_pacib_hint op2 CRm))
                                                                                                                                                                                                                  else
                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                      if ((←((pure (__opcode == (0xD50330FF#32 : (BitVec 32)))) <&&> (do
                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 768))))) : Bool)
                                                                                                                                                                                                                      then
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          writeReg SEE 768
                                                                                                                                                                                                                          let opc := (BitVec.slice __opcode 5 2)
                                                                                                                                                                                                                          let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                                                                          if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 0#1)) : Bool)
                                                                                                                                                                                                                          then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                          else (decode_sb_aarch64_instrs_system_barriers_sb opc CRm))
                                                                                                                                                                                                                      else
                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                          if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11010100000#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b00011#5 : (BitVec 5))))) <&&> (do
                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 846))))) : Bool)
                                                                                                                                                                                                                          then
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              writeReg SEE 846
                                                                                                                                                                                                                              let imm16 := (BitVec.slice __opcode 5 16)
                                                                                                                                                                                                                              (decode_smc_aarch64_instrs_system_exceptions_runtime_smc imm16))
                                                                                                                                                                                                                          else
                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                              if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11010100000#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b00001#5 : (BitVec 5))))) <&&> (do
                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 999))))) : Bool)
                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  writeReg SEE 999
                                                                                                                                                                                                                                  let imm16 := (BitVec.slice __opcode 5 16)
                                                                                                                                                                                                                                  (decode_svc_aarch64_instrs_system_exceptions_runtime_svc imm16))
                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 19) == (0b1101010100001#13 : (BitVec 13)))) <&&> (do
                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 1004))))) : Bool)
                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      writeReg SEE 1004
                                                                                                                                                                                                                                      let Rt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                      let op2 := (BitVec.slice __opcode 5 3)
                                                                                                                                                                                                                                      let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                                                                                      let CRn := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                      let op1 := (BitVec.slice __opcode 16 3)
                                                                                                                                                                                                                                      let L := (BitVec.slice __opcode 21 1)
                                                                                                                                                                                                                                      (decode_sys_aarch64_instrs_system_sysops Rt op2 CRm CRn op1 L))
                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 19) == (0b1101010100101#13 : (BitVec 13)))) <&&> (do
                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 1005))))) : Bool)
                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          writeReg SEE 1005
                                                                                                                                                                                                                                          let Rt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                          let op2 := (BitVec.slice __opcode 5 3)
                                                                                                                                                                                                                                          let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                                                                                          let CRn := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                          let op1 := (BitVec.slice __opcode 16 3)
                                                                                                                                                                                                                                          let L := (BitVec.slice __opcode 21 1)
                                                                                                                                                                                                                                          (decode_sysl_aarch64_instrs_system_sysops Rt op2 CRm CRn op1 L))
                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 19) == (0b1101010101001#13 : (BitVec 13)))) <&&> (do
                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 1006))))) : Bool)
                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              writeReg SEE 1006
                                                                                                                                                                                                                                              let Rt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                              let op2 := (BitVec.slice __opcode 5 3)
                                                                                                                                                                                                                                              let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                                                                                              let CRn := (BitVec.slice __opcode 12 4)
                                                                                                                                                                                                                                              let op1 := (BitVec.slice __opcode 16 3)
                                                                                                                                                                                                                                              let L := (BitVec.slice __opcode 21 1)
                                                                                                                                                                                                                                              (decode_sysp_aarch64_instrs_system_sysops_128 Rt op2 CRm CRn op1 L))
                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 24) == (0b0110111#7 : (BitVec 7)))) <&&> (do
                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 1009))))) : Bool)
                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  writeReg SEE 1009
                                                                                                                                                                                                                                                  let Rt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                  let imm14 := (BitVec.slice __opcode 5 14)
                                                                                                                                                                                                                                                  let b40 := (BitVec.slice __opcode 19 5)
                                                                                                                                                                                                                                                  let op := (BitVec.slice __opcode 24 1)
                                                                                                                                                                                                                                                  let b5 := (BitVec.slice __opcode 31 1)
                                                                                                                                                                                                                                                  (decode_tbnz_aarch64_instrs_branch_conditional_test Rt imm14 b40 op b5))
                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 30 24) == (0b0110110#7 : (BitVec 7)))) <&&> (do
                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 1010))))) : Bool)
                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      writeReg SEE 1010
                                                                                                                                                                                                                                                      let Rt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                      let imm14 := (BitVec.slice __opcode 5 14)
                                                                                                                                                                                                                                                      let b40 := (BitVec.slice __opcode 19 5)
                                                                                                                                                                                                                                                      let op := (BitVec.slice __opcode 24 1)
                                                                                                                                                                                                                                                      let b5 := (BitVec.slice __opcode 31 1)
                                                                                                                                                                                                                                                      (decode_tbz_aarch64_instrs_branch_conditional_test Rt imm14 b40 op b5))
                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                      if ((←((pure (((Sail.BitVec.extractLsb __opcode 31 21) == (0b11010100011#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb __opcode 4 0) == (0b00000#5 : (BitVec 5))))) <&&> (do
                                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 1011))))) : Bool)
                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          writeReg SEE 1011
                                                                                                                                                                                                                                                          let imm16 := (BitVec.slice __opcode 5 16)
                                                                                                                                                                                                                                                          (decode_tcancel_aarch64_instrs_system_tme_tcancel imm16))
                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                          if ((←((pure (__opcode == (0xD503307F#32 : (BitVec 32)))) <&&> (do
                                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 1012))))) : Bool)
                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              writeReg SEE 1012
                                                                                                                                                                                                                                                              (decode_tcommit_aarch64_instrs_system_tme_tcommit ()))
                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                              if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 5) == (0b110101010010001100110000011#27 : (BitVec 27)))) <&&> (do
                                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 1015))))) : Bool)
                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  writeReg SEE 1015
                                                                                                                                                                                                                                                                  let Rt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                                  (decode_tstart_aarch64_instrs_system_tme_tstart Rt))
                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                  if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 5) == (0b110101010010001100110001011#27 : (BitVec 27)))) <&&> (do
                                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 1016))))) : Bool)
                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      writeReg SEE 1016
                                                                                                                                                                                                                                                                      let Rt := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                                      (decode_ttest_aarch64_instrs_system_tme_ttest Rt))
                                                                                                                                                                                                                                                                  else
                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                      if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 5) == (0b110101010000001100010000000#27 : (BitVec 27)))) <&&> (do
                                                                                                                                                                                                                                                                           (pure ((← readReg SEE) <b 1028))))) : Bool)
                                                                                                                                                                                                                                                                      then
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          writeReg SEE 1028
                                                                                                                                                                                                                                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                                          (decode_wfet_aarch64_instrs_system_sysinstwithreg_wfet Rd))
                                                                                                                                                                                                                                                                      else
                                                                                                                                                                                                                                                                        (do
                                                                                                                                                                                                                                                                          if ((←((pure ((Sail.BitVec.extractLsb __opcode 31 5) == (0b110101010000001100010000001#27 : (BitVec 27)))) <&&> (do
                                                                                                                                                                                                                                                                               (pure ((← readReg SEE) <b 1029))))) : Bool)
                                                                                                                                                                                                                                                                          then
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              writeReg SEE 1029
                                                                                                                                                                                                                                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                                                                                                                                                                                                                                              (decode_wfit_aarch64_instrs_system_sysinstwithreg_wfit Rd))
                                                                                                                                                                                                                                                                          else
                                                                                                                                                                                                                                                                            (do
                                                                                                                                                                                                                                                                              if ((←((pure (__opcode == (0xD500403F#32 : (BitVec 32)))) <&&> (do
                                                                                                                                                                                                                                                                                   (pure ((← readReg SEE) <b 1030))))) : Bool)
                                                                                                                                                                                                                                                                              then
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  writeReg SEE 1030
                                                                                                                                                                                                                                                                                  let CRm := (BitVec.slice __opcode 8 4)
                                                                                                                                                                                                                                                                                  if ((((((BitVec.join1 [(BitVec.access __opcode 8)]) != 0#1) || ((BitVec.join1 [(BitVec.access __opcode 9)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 10)]) != 0#1)) || ((BitVec.join1 [(BitVec.access __opcode 11)]) != 0#1)) : Bool)
                                                                                                                                                                                                                                                                                  then (sailThrow ((Error_ConstrainedUnpredictable ())) : SailM Unit)
                                                                                                                                                                                                                                                                                  else (decode_xaflag_aarch64_instrs_integer_flags_xaflag CRm))
                                                                                                                                                                                                                                                                              else
                                                                                                                                                                                                                                                                                (do
                                                                                                                                                                                                                                                                                  if ((←((pure (__opcode == (0xD50320FF#32 : (BitVec 32)))) <&&> (do
                                                                                                                                                                                                                                                                                       (pure ((← readReg SEE) <b 1033))))) : Bool)
                                                                                                                                                                                                                                                                                  then
                                                                                                                                                                                                                                                                                    (do
                                                                                                                                                                                                                                                                                      writeReg SEE 1033
                                                                                                                                                                                                                                                                                      (decode_xpac_aarch64_instrs_integer_pac_strip_hint ()))
                                                                                                                                                                                                                                                                                  else (sailThrow ((Error_Undefined ())) : SailM Unit)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


