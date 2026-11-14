import Armv9.SysregsAutogen
set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true
set_option backward.do.legacy true
set_option cleanup.letToHave false
open Sail
open Sail.ConcurrencyInterfaceV1
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

def DBGBCR_write (n : Int) (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let __PSTATE_EL ← (( do (pure (← readReg PSTATE).EL) ) : SailM (BitVec 2) )
  let __MDCR_EL3_TDA ← (( do (pure (_get_MDCR_EL3_Type_TDA (← readReg MDCR_EL3))) ) : SailM (BitVec 1) )
  let __EDSCR_TDA ← (( do (pure (_get_EDSCR_Type_TDA (← (EDSCR_read ())))) ) : SailM (BitVec 1) )
  if ((n ≥b (← readReg NUM_BREAKPOINTS)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then (sailThrow ((Error_Undefined ())) : SailM Unit)
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                     (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                     (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else
                (do
                  if ((←((EL2Enabled ()) <&&> (do
                       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
                       (pure (((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) +++ (_get_MDCR_EL2_Type_TDA (← readReg MDCR_EL2))) != 0b00#2))))) : Bool)
                  then (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x05#8))
                  else
                    (do
                      if ((←((EL2Enabled ()) <&&> (do
                           (ELUsingAArch32 EL2)) <&&> (do
                           (pure (((_get_HDCR_Type_TDE (← (HDCR_read ()))) +++ (_get_HDCR_Type_TDA (← (HDCR_read ())))) != 0b00#2))))) : Bool)
                      then (AArch32_TakeHypTrapException (BitVec.toNat 0x05#8))
                      else
                        (do
                          if (((←((pure (HaveEL EL3)) <&&> (do
                                 (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                          then
                            (do
                              if ((←((Halted ()) <&&> (do
                                   (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                              then (sailThrow ((Error_Undefined ())) : SailM Unit)
                              else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                          else
                            (do
                              if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                     (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                              then (Halt DebugHalt_SoftwareAccess)
                              else (DBGBCR_set n (Mk_DBGBCR_Type (← (R_read t)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if (((←((pure ((← (Halted ())) && (HaveEL EL3))) <&&> (do
                         (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))) <&&> (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'")) <&&> (do
                         (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                  then (sailThrow ((Error_Undefined ())) : SailM Unit)
                  else
                    (do
                      if (((←((pure (HaveEL EL3)) <&&> (do
                             (pure (! (← (ELUsingAArch32 EL3))))))) && (__MDCR_EL3_TDA == 1#1)) : Bool)
                      then
                        (do
                          if ((←((Halted ()) <&&> (do
                               (pure ((_get_EDSCR_Type_SDD (← (EDSCR_read ()))) == 1#1))))) : Bool)
                          then (sailThrow ((Error_Undefined ())) : SailM Unit)
                          else (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x05#8)))
                      else
                        (do
                          if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                                 (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                          then (Halt DebugHalt_SoftwareAccess)
                          else (DBGBCR_set n (Mk_DBGBCR_Type (← (R_read t)))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((←((pure ((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 0#1)) <&&> (do
                             (HaltingAllowed ())))) && (__EDSCR_TDA == 1#1)) : Bool)
                      then (Halt DebugHalt_SoftwareAccess)
                      else (DBGBCR_set n (Mk_DBGBCR_Type (← (R_read t)))))
                  else (pure ())))))

theorem DBGBCR_SysRegWrite32_08e08cceb84c7c71_eq : @DBGBCR_SysRegWrite32_08e08cceb84c7c71 = @DBGBCR_write 8 := by unfold DBGBCR_SysRegWrite32_08e08cceb84c7c71 DBGBCR_write; rfl
theorem DBGBCR_SysRegWrite32_122d009e13ded976_eq : @DBGBCR_SysRegWrite32_122d009e13ded976 = @DBGBCR_write 1 := by unfold DBGBCR_SysRegWrite32_122d009e13ded976 DBGBCR_write; rfl
theorem DBGBCR_SysRegWrite32_28709afae2cd2b96_eq : @DBGBCR_SysRegWrite32_28709afae2cd2b96 = @DBGBCR_write 15 := by unfold DBGBCR_SysRegWrite32_28709afae2cd2b96 DBGBCR_write; rfl
theorem DBGBCR_SysRegWrite32_2d689254949b32aa_eq : @DBGBCR_SysRegWrite32_2d689254949b32aa = @DBGBCR_write 11 := by unfold DBGBCR_SysRegWrite32_2d689254949b32aa DBGBCR_write; rfl
theorem DBGBCR_SysRegWrite32_4811ff3f924f49d2_eq : @DBGBCR_SysRegWrite32_4811ff3f924f49d2 = @DBGBCR_write 6 := by unfold DBGBCR_SysRegWrite32_4811ff3f924f49d2 DBGBCR_write; rfl
theorem DBGBCR_SysRegWrite32_4d31a2bbe5418934_eq : @DBGBCR_SysRegWrite32_4d31a2bbe5418934 = @DBGBCR_write 2 := by unfold DBGBCR_SysRegWrite32_4d31a2bbe5418934 DBGBCR_write; rfl
theorem DBGBCR_SysRegWrite32_56e01e085292f5f1_eq : @DBGBCR_SysRegWrite32_56e01e085292f5f1 = @DBGBCR_write 5 := by unfold DBGBCR_SysRegWrite32_56e01e085292f5f1 DBGBCR_write; rfl
theorem DBGBCR_SysRegWrite32_77964c377a44e2ca_eq : @DBGBCR_SysRegWrite32_77964c377a44e2ca = @DBGBCR_write 3 := by unfold DBGBCR_SysRegWrite32_77964c377a44e2ca DBGBCR_write; rfl
theorem DBGBCR_SysRegWrite32_951097733e549f18_eq : @DBGBCR_SysRegWrite32_951097733e549f18 = @DBGBCR_write 4 := by unfold DBGBCR_SysRegWrite32_951097733e549f18 DBGBCR_write; rfl
theorem DBGBCR_SysRegWrite32_9fe4284f184fd88f_eq : @DBGBCR_SysRegWrite32_9fe4284f184fd88f = @DBGBCR_write 10 := by unfold DBGBCR_SysRegWrite32_9fe4284f184fd88f DBGBCR_write; rfl
theorem DBGBCR_SysRegWrite32_c3126c422a78b6f5_eq : @DBGBCR_SysRegWrite32_c3126c422a78b6f5 = @DBGBCR_write 14 := by unfold DBGBCR_SysRegWrite32_c3126c422a78b6f5 DBGBCR_write; rfl
theorem DBGBCR_SysRegWrite32_c77332e4c2ad23f2_eq : @DBGBCR_SysRegWrite32_c77332e4c2ad23f2 = @DBGBCR_write 0 := by unfold DBGBCR_SysRegWrite32_c77332e4c2ad23f2 DBGBCR_write; rfl
theorem DBGBCR_SysRegWrite32_ca879b07da5bfe93_eq : @DBGBCR_SysRegWrite32_ca879b07da5bfe93 = @DBGBCR_write 7 := by unfold DBGBCR_SysRegWrite32_ca879b07da5bfe93 DBGBCR_write; rfl
theorem DBGBCR_SysRegWrite32_df57cf6a3ef389f5_eq : @DBGBCR_SysRegWrite32_df57cf6a3ef389f5 = @DBGBCR_write 13 := by unfold DBGBCR_SysRegWrite32_df57cf6a3ef389f5 DBGBCR_write; rfl
theorem DBGBCR_SysRegWrite32_e67a829e0c397974_eq : @DBGBCR_SysRegWrite32_e67a829e0c397974 = @DBGBCR_write 12 := by unfold DBGBCR_SysRegWrite32_e67a829e0c397974 DBGBCR_write; rfl
theorem DBGBCR_SysRegWrite32_e9d51eb4b51754d0_eq : @DBGBCR_SysRegWrite32_e9d51eb4b51754d0 = @DBGBCR_write 9 := by unfold DBGBCR_SysRegWrite32_e9d51eb4b51754d0 DBGBCR_write; rfl
