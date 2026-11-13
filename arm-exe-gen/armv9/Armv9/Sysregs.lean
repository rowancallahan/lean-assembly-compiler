import Armv9.Armv9
import Armv9.Flow
import Armv9.Vector
import Armv9.Prelude
import Armv9.V8Base
import Armv9.Stubs
import Armv9.SysregsAutogen

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

def getISR (_ : Unit) : SailM (BitVec 32) := do
  let fiq_nmi ← (( do (undefined_bool ()) ) : SailM Bool )
  let fiq_pending ← (( do (undefined_bool ()) ) : SailM Bool )
  let irq_nmi ← (( do (undefined_bool ()) ) : SailM Bool )
  let irq_pending ← (( do (undefined_bool ()) ) : SailM Bool )
  let value_name : (BitVec 32) := (Zeros (n := 32))
  let value_name : (BitVec 32) :=
    (BitVec.update value_name 8
      (Bit
        (if ((IsPhysicalSErrorPending ()) : Bool)
        then 1#1
        else 0#1)))
  let (irq_nmi, irq_pending) ← (( do
    let (tup__0, tup__1) ← do (IRQPending ())
    let irq_pending : Bool := tup__0
    let irq_nmi : Bool := tup__1
    (pure (irq_nmi, irq_pending)) ) : SailM (Bool × Bool) )
  let (fiq_nmi, fiq_pending) : (Bool × Bool) :=
    let (tup__0, tup__1) := ((FIQPending ()) : (Bool × Bool))
    let fiq_pending : Bool := tup__0
    let fiq_nmi : Bool := tup__1
    (fiq_nmi, fiq_pending)
  let value_name ← (( do
    if ((←((HaveFeatNMI ()) <&&> (do
         (pure (! (← (UsingAArch32 ()))))))) : Bool)
    then
      (let value_name : (BitVec 32) :=
        (BitVec.update value_name 10
          (Bit
            (if ((irq_pending && irq_nmi) : Bool)
            then 1#1
            else 0#1)))
      (pure (BitVec.update value_name 9
          (Bit
            (if ((fiq_pending && fiq_nmi) : Bool)
            then 1#1
            else 0#1)))))
    else (pure value_name) ) : SailM (BitVec 32) )
  let value_name : (BitVec 32) :=
    (BitVec.update value_name 7
      (Bit
        (if (irq_pending : Bool)
        then 1#1
        else 0#1)))
  let value_name : (BitVec 32) :=
    (BitVec.update value_name 6
      (Bit
        (if (fiq_pending : Bool)
        then 1#1
        else 0#1)))
  if ((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
       (EL2Enabled ())) <&&> (do
       (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 0#1))))) : Bool)
  then
    (do
      let value_name ← (( do
        if ((←((HaveFeatNMI ()) <&&> (do
             (pure (! (← (UsingAArch32 ()))))) <&&> (do
             (IsHCRXEL2Enabled ())))) : Bool)
        then
          (do
            let value_name ← (( do
              if ((((_get_HCR_EL2_Type_IMO (← readReg HCR_EL2)) &&& (_get_HCR_EL2_Type_VI (← readReg HCR_EL2))) == 1#1) : Bool)
              then (do (pure (BitVec.update value_name 10 (Bit (_get_HCRX_EL2_Type_VINMI (← readReg HCRX_EL2))))))
              else (pure value_name) ) : SailM (BitVec 32) )
            if ((((_get_HCR_EL2_Type_FMO (← readReg HCR_EL2)) &&& (_get_HCR_EL2_Type_VF (← readReg HCR_EL2))) == 1#1) : Bool)
            then (do (pure (BitVec.update value_name 9 (Bit (_get_HCRX_EL2_Type_VFNMI (← readReg HCRX_EL2))))))
            else (pure value_name))
        else (pure value_name) ) : SailM (BitVec 32) )
      let value_name ← (( do
        if (((_get_HCR_EL2_Type_AMO (← readReg HCR_EL2)) == 1#1) : Bool)
        then (do (pure (BitVec.update value_name 8 (Bit ((BitVec.join1 [(BitVec.access value_name 8)]) ||| (_get_HCR_EL2_Type_VSE (← readReg HCR_EL2)))))))
        else (pure value_name) ) : SailM (BitVec 32) )
      let value_name ← (( do
        if (((_get_HCR_EL2_Type_IMO (← readReg HCR_EL2)) == 1#1) : Bool)
        then (do (pure (BitVec.update value_name 7 (Bit (_get_HCR_EL2_Type_VI (← readReg HCR_EL2))))))
        else (pure value_name) ) : SailM (BitVec 32) )
      if (((_get_HCR_EL2_Type_FMO (← readReg HCR_EL2)) == 1#1) : Bool)
      then (do (pure (BitVec.update value_name 6 (Bit (_get_HCR_EL2_Type_VF (← readReg HCR_EL2))))))
      else (pure value_name))
  else (pure value_name)

/-- Type quantifiers: k_isRNDRRS : Bool -/
def genRandomNum (isRNDRRS : Bool) : SailM (BitVec 64) := do
  writeReg PSTATE { (← readReg PSTATE) with N := (Sail.BitVec.extractLsb 0b0000#4 3 3) }
  writeReg PSTATE { (← readReg PSTATE) with Z := (Sail.BitVec.extractLsb 0b0000#4 2 2) }
  writeReg PSTATE { (← readReg PSTATE) with C := (Sail.BitVec.extractLsb 0b0000#4 1 1) }
  writeReg PSTATE { (← readReg PSTATE) with V := (Sail.BitVec.extractLsb 0b0000#4 0 0) }
  let x ← (( do (pure (integer_subrange (← readReg __cycle_count) 127 0)) ) : SailM (BitVec 128) )
  let y ← (( do (pure (integer_subrange ((← readReg __cycle_count) +i 1) 127 0)) ) : SailM (BitVec 128) )
  let w ← (( do (pure (integer_subrange ((← readReg __cycle_count) +i 2) 127 0)) ) : SailM (BitVec 128) )
  (pure (Sail.BitVec.extractLsb (← (SHA256hash x y w true)) 63 0))

/-- Type quantifiers: k_data_cache : Bool, level : Int -/
def getCacheID (level : Int) (data_cache : Bool) : SailM (BitVec 64) := do
  let range_min := (level *i 3)
  let cache_type ← (( do (pure (BitVec.slice (← readReg CLIDR_EL1) range_min 3)) ) : SailM (BitVec 3) )
  let ccsidr_val ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  match (cache_type : BitVec 3) with
  | 0b000 => (do (__UNKNOWN_bits 64))
  | 0b001 =>
    (do
      if (data_cache : Bool)
      then (__UNKNOWN_bits 64)
      else
        (do
          sail_assert ((0 ≤b level) && (level <b 7)) "src/sysregs.sail:222.59-222.60"
          (pure (GetElem?.getElem! (← readReg __ICACHE_CCSIDR_RESET) level))))
  | 0b010 =>
    (do
      if ((! data_cache) : Bool)
      then (__UNKNOWN_bits 64)
      else
        (do
          sail_assert ((0 ≤b level) && (level <b 7)) "src/sysregs.sail:228.59-228.60"
          (pure (GetElem?.getElem! (← readReg __DCACHE_CCSIDR_RESET) level))))
  | 0b011 =>
    (do
      if (data_cache : Bool)
      then
        (do
          sail_assert ((0 ≤b level) && (level <b 7)) "src/sysregs.sail:234.59-234.60"
          (pure (GetElem?.getElem! (← readReg __DCACHE_CCSIDR_RESET) level)))
      else
        (do
          sail_assert ((0 ≤b level) && (level <b 7)) "src/sysregs.sail:237.59-237.60"
          (pure (GetElem?.getElem! (← readReg __ICACHE_CCSIDR_RESET) level))))
  | 0b100 =>
    (do
      sail_assert ((0 ≤b level) && (level <b 7)) "src/sysregs.sail:242.55-242.56"
      (pure (GetElem?.getElem! (← readReg __DCACHE_CCSIDR_RESET) level)))
  | _ => (pure ccsidr_val)

def CacheConfigRead (cache_sel : (BitVec 4)) : SailM (BitVec 64) := do
  let data_cache : Bool :=
    if (((BitVec.join1 [(BitVec.access cache_sel 0)]) == 0#1) : Bool)
    then true
    else false
  let level := (BitVec.toNat (Sail.BitVec.extractLsb cache_sel 3 1))
  sail_assert (level <b 7) "src/sysregs.sail:253.20-253.21"
  (getCacheID level data_cache)

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int -/
def AArch64_SysRegRead (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) : SailM Unit := SailME.run do
  let index ← (( do (undefined_int ()) ) : SailME Unit Int )
  let n ← (( do (undefined_int ()) ) : SailME Unit Int )
  if ((((op0 == 3) && (op1 == 3)) && (crn == 13)) : Bool)
  then
    (do
      let n := (BitVec.toNat ((BitVec.join1 [(integer_access crm 0)]) +++ (integer_subrange op2 2 0)))
      if ((((integer_subrange crm 3 1) == 0b010#3) || ((integer_subrange crm 3 1) == 0b011#3)) : Bool)
      then
        (do
          if ((n ≥b (BitVec.toNat (_get_AMCGCR_EL0_Type_CG0NC (← readReg AMCGCR_EL0)))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (pure ()))
      else
        (do
          if ((((integer_subrange crm 3 1) == 0b110#3) || ((integer_subrange crm 3 1) == 0b111#3)) : Bool)
          then
            (do
              if ((n ≥b (BitVec.toNat (_get_AMCGCR_EL0_Type_CG1NC (← readReg AMCGCR_EL0)))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ()))
          else (pure ())))
  else (pure ())
  if ((((((op0 == 3) && (op1 == 3)) && (crn == 14)) && (((integer_subrange crm 3 2) == 0b10#2) || ((integer_subrange crm 3 2) == 0b11#2))) && (((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0)) != 0b11111#5)) : Bool)
  then
    (do
      if ((←((pure ((BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b ((← (GetNumEventCounters ())) -i 1))) <||> (do
           (EL2Enabled ()) <&&> (do
             (pure ((← readReg PSTATE).EL == EL1)) <||> (do
               (pure ((← readReg PSTATE).EL == EL0)) <&&> (do
                 (pure ((integer_subrange crm 3 2) == 0b10#2)) <&&> (do
                   (pure (((_get_PMUSERENR_EL0_Type_ER (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) != 0b00#2))) <||> (do
                   (pure ((integer_subrange crm 3 2) == 0b11#2)) <&&> (do
                     (pure ((_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)) == 1#1))))))) <&&> (do
             (pure ((BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b ((← (AArch64_GetNumEventCountersAccessible ())) -i 1))))))) : Bool)
      then
        (do
          if (((BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b ((← (GetNumEventCounters ())) -i 1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
      else (pure ()))
  else (pure ())
  if ((←((pure (((((op0 == 3) && (op1 == 3)) && (crn == 9)) && (crm == 13)) && ((op2 == 1) || (op2 == 2)))) <&&> (do
       (pure ((_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)) != 0b11111#5))))) : Bool)
  then
    (do
      if ((←((pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (GetNumEventCounters ())) -i 1))) <||> (do
           (EL2Enabled ()) <&&> (do
             (pure ((← readReg PSTATE).EL == EL1)) <||> (do
               (pure ((← readReg PSTATE).EL == EL0)) <&&> (do
                 (pure (op2 == 2)) <&&> (do
                   (pure (((_get_PMUSERENR_EL0_Type_ER (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) != 0b00#2))) <||> (do
                   (pure (op2 == 1)) <&&> (do
                     (pure ((_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)) == 1#1))))))) <&&> (do
             (pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (AArch64_GetNumEventCountersAccessible ())) -i 1))))))) : Bool)
      then
        (do
          if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (GetNumEventCounters ())) -i 1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
      else (pure ()))
  else (pure ())
  let temp ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
  (AArch64_AutoGen_SysRegRead (← readReg PSTATE).EL (integer_subrange op0 1 0) (integer_subrange op1 2 0) (integer_subrange crn 3 0) (integer_subrange op2 2 0) (integer_subrange crm 3 0) t)
  if ((((((op0 == 3) && (crn == 10)) && (crm == 5)) && (op2 == 0)) && ((op1 == 0) || (op1 == 5))) : Bool)
  then
    (do
      if ((←((HaveRME ()) <&&> (do
           (pure ((_get_MPAMIDR_EL1_Type_HAS_ALTSP (← readReg MPAMIDR_EL1)) == 1#1))))) : Bool)
      then
        (X_set t 64
          (Sail.BitVec.updateSubrange (← (X_read t 64)) 54 54
            (← (do
              if ((! (← (UsePrimarySpaceEL10 ()))) : Bool)
              then (pure 1#1)
              else (pure 0#1)))))
      else (pure ()))
  else (pure ())
  if ((((((op0 == 3) && (crn == 10)) && (crm == 5)) && (op2 == 0)) && (op1 == 4)) : Bool)
  then
    (do
      if ((←((HaveRME ()) <&&> (do
           (pure ((_get_MPAMIDR_EL1_Type_HAS_ALTSP (← readReg MPAMIDR_EL1)) == 1#1))))) : Bool)
      then
        (X_set t 64
          (Sail.BitVec.updateSubrange (← (X_read t 64)) 54 54
            (← (do
              if ((! (← (UsePrimarySpaceEL2 ()))) : Bool)
              then (pure 1#1)
              else (pure 0#1)))))
      else (pure ()))
  else (pure ())
  if ((((((op0 == 3) && (crn == 9)) && (op1 == 0)) && (op2 == 7)) && (crm == 10)) : Bool)
  then (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 4 4 (← (SPE_PMBIDR_P_Read ()))))
  else (pure ())
  if ((((op0 == 3) && (crn == 9)) && (((((op1 == 3) && (op2 == 3)) && ((crm == 12) || (crm == 14))) || (((op1 == 3) && ((op2 == 1) || (op2 == 2))) && (crm == 12))) || (((op1 == 0) && ((op2 == 1) || (op2 == 2))) && (crm == 14)))) : Bool)
  then
    (do
      let mask ← (( do (PMUCounterMask ()) ) : SailME Unit (BitVec 64) )
      (X_set t 64 ((← (X_read t 64)) &&& mask)))
  else (pure ())
  if ((((((op0 == 3) && (op1 == 3)) && (crn == 9)) && (crm == 13)) && ((op2 == 1) || (op2 == 2))) : Bool)
  then
    (do
      if ((op2 == 1) : Bool)
      then
        (do
          if ((←((EL2Enabled ()) <&&> (do
               (pure ((← readReg PSTATE).EL == EL0)) <||> (do
                 (pure ((← readReg PSTATE).EL == EL1)))) <&&> (do
               (pure ((_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)) != 0b11111#5))) <&&> (do
               (pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (AArch64_GetNumEventCountersAccessible ())) -i 1)))))) : Bool)
          then
            (do
              if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (GetNumEventCounters ())) -i 1)) : Bool)
              then
                (do
                  (X_set t 64 temp)
                  (sailThrow ((Error_Undefined ())) : SailM Unit))
              else
                (do
                  (X_set t 64 temp)
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
          else
            (do
              if (((_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)) == 0b11111#5) : Bool)
              then (X_set t 64 (← readReg PMCCFILTR_EL0))
              else
                (do
                  let pmselr_el0 ← do (pure (BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))))
                  sail_assert (pmselr_el0 <b 31) "src/sysregs.sail:335.38-335.39"
                  (X_set t 64 (GetElem?.getElem! (← readReg PMEVTYPER_EL0) pmselr_el0)))))
      else (pure ())
      if ((op2 == 2) : Bool)
      then
        (do
          if ((←((pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (GetNumEventCounters ())) -i 1))) <&&> (do
               (pure ((_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)) != 0b11111#5))) <||> (do
               (EL2Enabled ()) <&&> (do
                 (pure ((← readReg PSTATE).EL == EL0)) <||> (do
                   (pure ((← readReg PSTATE).EL == EL1)))) <&&> (do
                 (pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (AArch64_GetNumEventCountersAccessible ())) -i 1))))))) : Bool)
          then
            (do
              if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (GetNumEventCounters ())) -i 1)) : Bool)
              then
                (do
                  (X_set t 64 temp)
                  (sailThrow ((Error_Undefined ())) : SailM Unit))
              else
                (do
                  (X_set t 64 temp)
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
          else
            (do
              let pmselr_el0 ← do (pure (BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))))
              sail_assert (pmselr_el0 <b 31) "src/sysregs.sail:350.38-350.39"
              (X_set t 64 (GetElem?.getElem! (← readReg PMEVCNTR_EL0) pmselr_el0))))
      else (pure ()))
  else (pure ())
  if ((((((op0 == 3) && (crn == 9)) && (op1 == 3)) && (op2 == 0)) && (crm == 12)) : Bool)
  then (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 15 11 (integer_subrange (← (AArch64_GetNumEventCountersAccessible ())) 4 0)))
  else (pure ())
  if (((((op0 == 3) && (crn == 14)) && (op1 == 3)) && (((integer_subrange crm 3 2) == 0b10#2) || (((integer_subrange crm 3 2) == 0b11#2) && (((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0)) != 0b11111#5)))) : Bool)
  then
    (do
      if ((←((pure (((BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b ((← (GetNumEventCounters ())) -i 1)) && (((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0)) != 0b11111#5))) <||> (do
           (EL2Enabled ()) <&&> (do
             (pure ((← readReg PSTATE).EL == EL0)) <||> (do
               (pure ((← readReg PSTATE).EL == EL1)))) <&&> (do
             (pure ((BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b ((← (AArch64_GetNumEventCountersAccessible ())) -i 1))))))) : Bool)
      then
        (do
          if (((BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b ((← (GetNumEventCounters ())) -i 1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              (X_set t 64 temp)
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
      else (pure ()))
  else (pure ())
  if (((((op0 == 2) && (op1 == 0)) && (crn == 7)) && (op2 == 6)) : Bool)
  then
    (do
      if ((crm == 8) : Bool)
      then SailME.throw (← (do (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 7 0 0b11111111#8))))
      else
        (do
          if ((crm == 9) : Bool)
          then SailME.throw (← (do (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 7 0 (Sail.BitVec.extractLsb (← readReg DBGCLAIMCLR_EL1) 7 0)))))
          else (pure ())))
  else (pure ())
  if (((((op0 == 2) && (op1 == 1)) && (crn == 7)) && (op2 == 6)) : Bool)
  then
    (do
      if ((crm == 8) : Bool)
      then SailME.throw (← (do (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 31 0 (← readReg __trcclaim_tags)))))
      else
        (do
          if ((crm == 9) : Bool)
          then SailME.throw (← (do (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 31 0 (← readReg __trcclaim_tags)))))
          else (pure ())))
  else (pure ())
  if ((((((op0 == 3) && (op1 == 0)) && ((crn == (BitVec.toNat 0xA#4)) : Bool)) && (op2 == 0)) && (crm == 5)) : Bool)
  then
    (do
      if ((BEq.beq (← (CurrentSecurityState ())) SS_Secure) : Bool)
      then (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 60 60 (_get_MPAM3_EL3_Type_FORCE_NS (← (MPAM3_EL3_read ())))))
      else (pure ()))
  else
    (do
      if ((((((op0 == 3) && ((crn == (BitVec.toNat 0xC#4)) : Bool)) && (op1 == 0)) && (op2 == 0)) && (crm == 1)) : Bool)
      then (do (X_set t 64 (Sail.BitVec.zeroExtend (← (getISR ())) 64)))
      else
        (do
          if ((((((op0 == 3) && (crn == 0)) && (op1 == 1)) && ((op2 == 0) || (op2 == 2))) && (crm == 0)) : Bool)
          then
            (do
              if ((op2 == 0) : Bool)
              then (do (X_set t 64 (← (CacheConfigRead (Sail.BitVec.extractLsb (← readReg CSSELR_EL1) 3 0)))))
              else (do (X_set t 64 (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb (← (CacheConfigRead (Sail.BitVec.extractLsb (← readReg CSSELR_EL1) 3 0))) 63 32) 64))))
          else
            (do
              if ((((((op0 == 3) && (crn == 0)) && (op1 == 3)) && (op2 == 7)) && (crm == 0)) : Bool)
              then
                (do
                  if (((← readReg PSTATE).EL == EL0) : Bool)
                  then
                    (do
                      if ((← (IsInHost ())) : Bool)
                      then
                        (X_set t 64
                          (Sail.BitVec.updateSubrange (← (X_read t 64)) 4 4
                            (← (do
                              if (((_get_SCTLR_EL2_Type_DZE (← readReg SCTLR_EL2)) == 0#1) : Bool)
                              then (pure 1#1)
                              else (pure 0#1)))))
                      else
                        (X_set t 64
                          (Sail.BitVec.updateSubrange (← (X_read t 64)) 4 4
                            (← (do
                              if ((←((pure ((_get_SCTLR_EL1_Type_DZE (← readReg SCTLR_EL1)) == 0#1)) <||> (do
                                   (EL2Enabled ()) <&&> (do
                                     (pure ((_get_HCR_EL2_Type_TDZ (← readReg HCR_EL2)) == 1#1)))))) : Bool)
                              then (pure 1#1)
                              else (pure 0#1))))))
                  else
                    (do
                      if (((← readReg PSTATE).EL == EL1) : Bool)
                      then
                        (X_set t 64
                          (Sail.BitVec.updateSubrange (← (X_read t 64)) 4 4
                            (← (do
                              if ((←((EL2Enabled ()) <&&> (do
                                   (pure ((_get_HCR_EL2_Type_TDZ (← readReg HCR_EL2)) == 1#1))))) : Bool)
                              then (pure 1#1)
                              else (pure 0#1)))))
                      else (pure ())))
              else
                (do
                  if ((← (AArch64_CheckNVCondsIfCurrentEL op0 op1 crn crm op2)) : Bool)
                  then (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 3 2 0b10#2))
                  else (pure ())
                  if ((((((op0 == 3) && (crn == 2)) && (crm == 4)) && (op1 == 3)) && ((op2 == 0) || (op2 == 1))) : Bool)
                  then
                    (X_set t 64
                      (← (do
                        if ((op2 == 0) : Bool)
                        then (genRandomNum false)
                        else (genRandomNum true))))
                  else (pure ())
                  if (((((op0 == 2) && (op1 == 1)) && (crn == 8)) && ((op2 == 0) || ((op2 == 1) || ((op2 == 2) || ((op2 == 4) || ((op2 == 5) || (op2 == 6))))))) : Bool)
                  then
                    (do
                      let recordIdx ← do (pure (BitVec.toNat (((_get_BRBFCR_EL1_Type_BANK (← readReg BRBFCR_EL1)) +++ (BitVec.join1 [(integer_access op2 2)])) +++ (integer_subrange crm 3 0))))
                      if ((recordIdx <b (← (GetBRBENumRecords ()))) : Bool)
                      then
                        (do
                          if (((op2 == 0) || (op2 == 4)) : Bool)
                          then
                            (do
                              sail_assert ((0 ≤b recordIdx) && (recordIdx <b 64)) "src/sysregs.sail:443.70-443.71"
                              (X_set t 64 (GetElem?.getElem! (← readReg Records_INF) recordIdx)))
                          else (pure ())
                          if (((op2 == 1) || (op2 == 5)) : Bool)
                          then
                            (do
                              sail_assert ((0 ≤b recordIdx) && (recordIdx <b 64)) "src/sysregs.sail:447.70-447.71"
                              (X_set t 64 (GetElem?.getElem! (← readReg Records_SRC) recordIdx)))
                          else (pure ())
                          if (((op2 == 2) || (op2 == 6)) : Bool)
                          then
                            (do
                              sail_assert ((0 ≤b recordIdx) && (recordIdx <b 64)) "src/sysregs.sail:451.70-451.71"
                              (X_set t 64 (GetElem?.getElem! (← readReg Records_TGT) recordIdx)))
                          else (pure ()))
                      else (X_set t 64 (Zeros (n := 64))))
                  else (pure ())
                  if ((((((op0 == 3) && (crn == 5)) && (op1 == 0)) && (op2 == 0)) && (crm == 4)) : Bool)
                  then
                    (do
                      if ((←((pure ((BitVec.toNat (_get_ERRIDR_EL1_Type_NUM (← readReg ERRIDR_EL1))) == (BitVec.toNat 0x0#4))) <||> (do
                           (pure ((BitVec.toNat (_get_ERRSELR_EL1_Type_SEL (← readReg ERRSELR_EL1))) ≥b (BitVec.toNat (_get_ERRIDR_EL1_Type_NUM (← readReg ERRIDR_EL1)))))))) : Bool)
                      then (X_set t 64 (Zeros (n := 64)))
                      else
                        (do
                          let index ← do (pure (BitVec.toNat (_get_ERRSELR_EL1_Type_SEL (← readReg ERRSELR_EL1))))
                          sail_assert ((0 ≤b index) && (index <b 4)) "src/sysregs.sail:464.57-464.58"
                          (X_set t 64 (GetElem?.getElem! (← readReg ERRnFR) index))))
                  else (pure ())
                  if ((((((op0 == 2) && (crn == 7)) && (op1 == 0)) && (op2 == 6)) && (crm == 14)) : Bool)
                  then
                    (do
                      if ((HaveEL EL3) : Bool)
                      then
                        (do
                          if ((← (ExternalInvasiveDebugEnabled ())) : Bool)
                          then (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 1 0 0b11#2))
                          else (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 1 0 0b10#2))
                          (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 3 2 0b11#2))
                          if ((← (ExternalSecureInvasiveDebugEnabled ())) : Bool)
                          then (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 5 4 0b11#2))
                          else (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 5 4 0b10#2))
                          (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 7 6 (Sail.BitVec.extractLsb (← (X_read t 64)) 5 4))))
                      else (pure ()))
                  else
                    (do
                      if ((((((op0 == 2) && (crn == 0)) && (op1 == 3)) && (op2 == 0)) && (crm == 5)) : Bool)
                      then
                        (do
                          (DBGDSCRint_write (_update_DBGDSCRint_Type_RXfull (← (DBGDSCRint_read ())) 0#1))
                          writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange (← readReg MDCCSR_EL0) 30 30 0#1)
                          (DBGDSCRext_write (_update_DBGDSCRext_Type_RXfull (← (DBGDSCRext_read ())) 0#1))
                          (EDSCR_write (_update_EDSCR_Type_RXfull (← (EDSCR_read ())) 0#1)))
                      else (pure ())
                      if ((((((op0 == 2) && (crn == 0)) && (op1 == 3)) && (op2 == 0)) && (crm == 4)) : Bool)
                      then
                        (do
                          (DBGDSCRint_write (_update_DBGDSCRint_Type_RXfull (← (DBGDSCRint_read ())) 0#1))
                          writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange (← readReg MDCCSR_EL0) 30 30 0#1)
                          (DBGDSCRext_write (_update_DBGDSCRext_Type_RXfull (← (DBGDSCRext_read ())) 0#1))
                          (EDSCR_write (_update_EDSCR_Type_RXfull (← (EDSCR_read ())) 0#1))
                          (X_set t 64 (set_slice 32 (← (X_read t 64)) 32 (BitVec.slice (← readReg DBGDTRTX_EL0) 0 32)))
                          (X_set t 64 (set_slice 32 (← (X_read t 64)) 0 (BitVec.slice (← readReg DBGDTRRX_EL0) 0 32))))
                      else (pure ())
                      if ((((((op0 == 3) && (crn == 12)) && (op1 == 4)) && (op2 == 7)) && (crm == 11)) : Bool)
                      then
                        (do
                          if ((←((pure ((← readReg PSTATE).EL == EL2)) <||> (do
                               (pure ((← readReg PSTATE).EL == EL3))))) : Bool)
                          then (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 26 24 0b000#3))
                          else (pure ()))
                      else (pure ())
                      if ((((((op0 == 3) && (crn == 4)) && (op1 == 0)) && (op2 == 0)) && (crm == 6)) : Bool)
                      then (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 2 0 0b000#3))
                      else (pure ())
                      if ((((((op0 == 3) && (crn == 1)) && (op1 == 4)) && (op2 == 0)) && (crm == 1)) : Bool)
                      then
                        (do
                          if ((←((pure (! (← (ELUsingAArch32 EL1)))) <&&> (do
                               (pure ((← readReg PSTATE).EL != EL1))))) : Bool)
                          then (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 31 31 1#1))
                          else (pure ()))
                      else (pure ())
                      if ((((((op0 == 3) && (crn == 12)) && (op1 == 6)) && (op2 == 2)) && (crm == 0)) : Bool)
                      then
                        (do
                          if (((_get_ID_AA64PFR0_EL1_Type_EL3 (← readReg ID_AA64PFR0_EL1)) == 0b0001#4) : Bool)
                          then (X_set t 64 (Sail.BitVec.updateSubrange (← (X_read t 64)) 0 0 1#1))
                          else (pure ()))
                      else (pure ()))))))

def SetResetVector (value_name : (BitVec 64)) : SailM Unit := do
  if ((! (← (HaveAArch64 ()))) : Bool)
  then
    (do
      if ((HaveEL EL3) : Bool)
      then writeReg MVBAR (Mk_MVBAR_Type ((Sail.BitVec.extractLsb value_name 31 1) +++ 1#1))
      else writeReg RVBAR ((Sail.BitVec.extractLsb value_name 31 1) +++ 1#1))
  else
    (do
      if (((HighestEL ()) == EL3) : Bool)
      then writeReg RVBAR_EL3 (Mk_RVBAR_EL3_Type value_name)
      else
        (do
          if (((HighestEL ()) == EL2) : Bool)
          then writeReg RVBAR_EL2 (Mk_RVBAR_EL2_Type value_name)
          else writeReg RVBAR_EL1 (Mk_RVBAR_EL1_Type value_name)))

/-- Type quantifiers: k_cold : Bool -/
def TakeReset (cold : Bool) : SailM Unit := do
  sail_assert (((HighestEL ()) == EL1) || (((HighestEL ()) == EL2) || ((HighestEL ()) == EL3))) "src/reset.sail:1400.71-1400.72"
  writeReg FEAT_DoubleLock_IMPLEMENTED false
  writeReg FEAT_EPAC_IMPLEMENTED false
  (InitVariantImplemented ())
  (InitFeatureImpl ())
  if (cold : Bool)
  then
    (do
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 15 12 CFG_ID_AA64PFR0_EL1_EL3)
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 11 8 CFG_ID_AA64PFR0_EL1_EL2)
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 7 4 CFG_ID_AA64PFR0_EL1_EL1)
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AA64PFR0_EL1) 3 0 CFG_ID_AA64PFR0_EL1_EL0)
      writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange (← readReg OSLSR_EL1) 1 1 1#1)
      writeReg RMR_EL3 (Sail.BitVec.updateSubrange (← readReg RMR_EL3) 0 0 (← readReg CFG_RMR_AA64)))
  else (pure ())
  if (((_get_RMR_EL3_Type_AA64 (← readReg RMR_EL3)) == 1#1) : Bool)
  then
    (do
      writeReg __highest_el_aarch32 false
      (SetResetVector (← readReg CFG_RVBAR))
      (AArch64_TakeReset cold))
  else
    (do
      let questionMark := (HighestEL ())
      if ((questionMark == EL3) : Bool)
      then sail_assert ((_get_ID_AA64PFR0_EL1_Type_EL3 (← readReg ID_AA64PFR0_EL1)) == 0b0010#4) "src/reset.sail:1420.51-1420.52"
      else
        (do
          if ((questionMark == EL2) : Bool)
          then sail_assert ((_get_ID_AA64PFR0_EL1_Type_EL2 (← readReg ID_AA64PFR0_EL1)) == 0b0010#4) "src/reset.sail:1423.51-1423.52"
          else
            (do
              if ((questionMark == EL1) : Bool)
              then sail_assert ((_get_ID_AA64PFR0_EL1_Type_EL1 (← readReg ID_AA64PFR0_EL1)) == 0b0010#4) "src/reset.sail:1426.51-1426.52"
              else (pure ())))
      writeReg __highest_el_aarch32 true
      writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA64EL0) false)
      writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA64EL1) false)
      writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA64EL2) false)
      writeReg FeatureImpl (vectorUpdate (← readReg FeatureImpl) (num_of_Feature FEAT_AA64EL3) false)
      if ((← readReg __ignore_rvbar_in_aarch32) : Bool)
      then (SetResetVector (Sail.BitVec.zeroExtend 0x0#4 64))
      else (SetResetVector (← readReg CFG_RVBAR))
      if ((HaveEL EL3) : Bool)
      then writeReg SCR (Sail.BitVec.updateSubrange (← readReg SCR) 0 0 0#1)
      else (pure ())
      (AArch32_TakeReset cold))
  if (((← readReg ZCR_EL3_LEN_VALUE) != (Neg.neg 1)) : Bool)
  then writeReg ZCR_EL3 (Sail.BitVec.updateSubrange (← readReg ZCR_EL3) 3 0 (integer_subrange (← readReg ZCR_EL3_LEN_VALUE) 3 0))
  else (pure ())
  if (((← readReg CPTR_EL3_EZ_VALUE) != (Neg.neg 1)) : Bool)
  then writeReg CPTR_EL3 (Sail.BitVec.updateSubrange (← readReg CPTR_EL3) 8 8 (BitVec.join1 [(integer_access (← readReg CPTR_EL3_EZ_VALUE) 0)]))
  else (pure ())
  if (((← readReg CPTR_EL3_ESM_VALUE) != (Neg.neg 1)) : Bool)
  then writeReg CPTR_EL3 (Sail.BitVec.updateSubrange (← readReg CPTR_EL3) 12 12 (BitVec.join1 [(integer_access (← readReg CPTR_EL3_ESM_VALUE) 0)]))
  else (pure ())
  if (((← readReg SMCR_EL3_LEN_VALUE) != (Neg.neg 1)) : Bool)
  then writeReg SMCR_EL3 (Sail.BitVec.updateSubrange (← readReg SMCR_EL3) 3 0 (integer_subrange (← readReg SMCR_EL3_LEN_VALUE) 3 0))
  else (pure ())

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int -/
def AArch64_SysRegWrite (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) : SailM Unit := SailME.run do
  let n ← (( do (undefined_int ()) ) : SailME Unit Int )
  let tempxt ← (( do (X_read t 64) ) : SailME Unit (BitVec 64) )
  let tempxt : (BitVec 64) :=
    if (((((op0 == 2) && (crn == 0)) && (op1 == 0)) && (op2 == 5)) : Bool)
    then
      (let tempxt : (BitVec 64) := (BitVec.update tempxt 8 (Bit (BitVec.join1 [(BitVec.access tempxt 7)])))
      (BitVec.update tempxt 6 (Bit (BitVec.join1 [(BitVec.access tempxt 5)]))))
    else tempxt
  let tempxt ← (( do
    if ((((((op0 == 3) && (crn == 12)) && (op1 == 0)) && (op2 == 4)) && (crm == 12)) : Bool)
    then
      (do
        let tempxt ← (pure (BitVec.update tempxt 19 (Bit (_get_ICV_CTLR_EL1_Type_ExtRange (← readReg ICV_CTLR_EL1)))))
        let tempxt ← (pure (Sail.BitVec.updateSubrange tempxt 13 11 (_get_ICV_CTLR_EL1_Type_IDbits (← readReg ICV_CTLR_EL1))))
        let tempxt ← (pure (Sail.BitVec.updateSubrange tempxt 10 8 (_get_ICV_CTLR_EL1_Type_PRIbits (← readReg ICV_CTLR_EL1))))
        let tempxt ← (pure (BitVec.update tempxt 15 (Bit (_get_ICV_CTLR_EL1_Type_A3V (← readReg ICV_CTLR_EL1)))))
        (pure (BitVec.update tempxt 14 (Bit (_get_ICV_CTLR_EL1_Type_SEIS (← readReg ICV_CTLR_EL1))))))
    else (pure tempxt) ) : SailME Unit (BitVec 64) )
  let tempxt ← (( do
    if ((((((op0 == 3) && (crn == 12)) && (op1 == 6)) && (op2 == 4)) && (crm == 12)) : Bool)
    then
      (do
        let tempxt ← (pure (BitVec.update tempxt 19 (Bit (_get_ICC_CTLR_EL3_Type_ExtRange (← readReg ICC_CTLR_EL3)))))
        let tempxt ← (pure (Sail.BitVec.updateSubrange tempxt 13 11 (_get_ICC_CTLR_EL3_Type_IDbits (← readReg ICC_CTLR_EL3))))
        let tempxt ← (pure (Sail.BitVec.updateSubrange tempxt 10 8 (_get_ICC_CTLR_EL3_Type_PRIbits (← readReg ICC_CTLR_EL3))))
        let tempxt ← (pure (BitVec.update tempxt 17 (Bit (_get_ICC_CTLR_EL3_Type_nDS (← readReg ICC_CTLR_EL3)))))
        let tempxt ← (pure (BitVec.update tempxt 15 (Bit (_get_ICC_CTLR_EL3_Type_A3V (← readReg ICC_CTLR_EL3)))))
        (pure (BitVec.update tempxt 14 (Bit (_get_ICC_CTLR_EL3_Type_SEIS (← readReg ICC_CTLR_EL3))))))
    else (pure tempxt) ) : SailME Unit (BitVec 64) )
  let tempxt ← (( do
    if ((((((op0 == 3) && (crn == 12)) && (op1 == 4)) && (op2 == 7)) && (crm == 11)) : Bool)
    then
      (do
        if ((←((pure ((← readReg PSTATE).EL == EL2)) <||> (do
             (pure ((← readReg PSTATE).EL == EL3))))) : Bool)
        then
          (do
            let tempxt ← (( do
              if (((BitVec.toNat (Sail.BitVec.extractLsb tempxt 23 21)) <b (6 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2))))) : Bool)
              then (do (pure (Sail.BitVec.updateSubrange tempxt 23 21 (integer_subrange (6 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))) 2 0))))
              else (pure tempxt) ) : SailME Unit (BitVec 64) )
            let tempxt ← (( do
              if ((BEq.beq (← (CurrentSecurityState ())) SS_Secure) : Bool)
              then
                (do
                  if (((BitVec.toNat (Sail.BitVec.extractLsb tempxt 20 18)) <b (6 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2))))) : Bool)
                  then (do (pure (Sail.BitVec.updateSubrange tempxt 20 18 (integer_subrange (6 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))) 2 0))))
                  else (pure tempxt))
              else
                (do
                  if (((BitVec.toNat (Sail.BitVec.extractLsb tempxt 20 18)) <b (7 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2))))) : Bool)
                  then (do (pure (Sail.BitVec.updateSubrange tempxt 20 18 (integer_subrange (7 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))) 2 0))))
                  else (pure tempxt)) ) : SailME Unit (BitVec 64) )
            if (((_get_ICC_SRE_EL1_Type_SRE (← readReg ICC_SRE_EL1_NS)) == 1#1) : Bool)
            then (pure (Sail.BitVec.updateSubrange tempxt 3 2 0b10#2))
            else (pure tempxt))
        else (pure tempxt))
    else (pure tempxt) ) : SailME Unit (BitVec 64) )
  let tempxt ← (( do
    if ((((((op0 == 3) && (crn == 12)) && (op1 == 0)) && (op2 == 3)) && (crm == 8)) : Bool)
    then
      (do
        if (((BitVec.toNat (Sail.BitVec.extractLsb tempxt 2 0)) <b (6 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2))))) : Bool)
        then (do (pure (Sail.BitVec.updateSubrange tempxt 2 0 (integer_subrange (6 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))) 2 0))))
        else (pure tempxt))
    else (pure tempxt) ) : SailME Unit (BitVec 64) )
  let tempxt ← (( do
    if ((((((op0 == 3) && (crn == 12)) && (op1 == 0)) && (op2 == 3)) && (crm == 12)) : Bool)
    then
      (do
        if (((_get_ICV_CTLR_EL1_Type_CBPR (← readReg ICV_CTLR_EL1)) == 0#1) : Bool)
        then
          (do
            if ((BEq.beq (← (CurrentSecurityState ())) SS_Secure) : Bool)
            then
              (do
                if (((BitVec.toNat (Sail.BitVec.extractLsb tempxt 2 0)) <b (6 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2))))) : Bool)
                then (do (pure (Sail.BitVec.updateSubrange tempxt 2 0 (integer_subrange (6 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))) 2 0))))
                else (pure tempxt))
            else
              (do
                if (((BitVec.toNat (Sail.BitVec.extractLsb tempxt 2 0)) <b (7 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2))))) : Bool)
                then (do (pure (Sail.BitVec.updateSubrange tempxt 2 0 (integer_subrange (7 -i (BitVec.toNat (_get_ICH_VTR_EL2_Type_PREbits (← readReg ICH_VTR_EL2)))) 2 0))))
                else (pure tempxt)))
        else (do (pure (Sail.BitVec.updateSubrange tempxt 2 0 (_get_ICV_BPR1_EL1_Type_BinaryPoint (← readReg ICV_BPR1_EL1))))))
    else (pure tempxt) ) : SailME Unit (BitVec 64) )
  if ((((op0 == 3) && (op1 == 3)) && (crn == 13)) : Bool)
  then
    (do
      let n := (BitVec.toNat ((BitVec.join1 [(integer_access crm 0)]) +++ (integer_subrange op2 2 0)))
      if ((((integer_subrange crm 3 1) == 0b010#3) || ((integer_subrange crm 3 1) == 0b011#3)) : Bool)
      then
        (do
          if ((n ≥b (BitVec.toNat (_get_AMCGCR_EL0_Type_CG0NC (← readReg AMCGCR_EL0)))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (pure ()))
      else
        (do
          if ((((integer_subrange crm 3 1) == 0b110#3) || ((integer_subrange crm 3 1) == 0b111#3)) : Bool)
          then
            (do
              if ((n ≥b (BitVec.toNat (_get_AMCGCR_EL0_Type_CG1NC (← readReg AMCGCR_EL0)))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ()))
          else (pure ())))
  else (pure ())
  let mask ← (( do (PMUCounterMask ()) ) : SailME Unit (BitVec 64) )
  let tempxt ← (( do
    if ((((((op0 == 3) && (crn == 9)) && (op1 == 3)) && (op2 == 3)) && ((crm == 12) || (crm == 14))) : Bool)
    then
      (do
        let tempxt ← (( do
          if ((crm == 12) : Bool)
          then (do (pure ((← readReg PMOVSSET_EL0) &&& (Complement.complement (tempxt &&& mask)))))
          else (pure tempxt) ) : SailME Unit (BitVec 64) )
        if ((crm == 14) : Bool)
        then (do (pure ((← readReg PMOVSSET_EL0) ||| (tempxt &&& mask))))
        else (pure tempxt))
    else (pure tempxt) ) : SailME Unit (BitVec 64) )
  let tempxt ← (( do
    if ((((((op0 == 3) && (crn == 9)) && (op1 == 3)) && ((op2 == 1) || (op2 == 2))) && (crm == 12)) : Bool)
    then
      (do
        let tempxt ← (( do
          if ((op2 == 2) : Bool)
          then (do (pure ((← readReg PMCNTENSET_EL0) &&& (Complement.complement (tempxt &&& mask)))))
          else (pure tempxt) ) : SailME Unit (BitVec 64) )
        if ((op2 == 1) : Bool)
        then (do (pure ((← readReg PMCNTENSET_EL0) ||| (tempxt &&& mask))))
        else (pure tempxt))
    else (pure tempxt) ) : SailME Unit (BitVec 64) )
  let tempxt ← (( do
    if ((((((op0 == 3) && (crn == 9)) && (op1 == 0)) && ((op2 == 1) || (op2 == 2))) && (crm == 14)) : Bool)
    then
      (do
        let tempxt ← (( do
          if ((op2 == 2) : Bool)
          then (do (pure ((← readReg PMINTENSET_EL1) &&& (Complement.complement (tempxt &&& mask)))))
          else (pure tempxt) ) : SailME Unit (BitVec 64) )
        if ((op2 == 1) : Bool)
        then (do (pure ((← readReg PMINTENSET_EL1) ||| (tempxt &&& mask))))
        else (pure tempxt))
    else (pure tempxt) ) : SailME Unit (BitVec 64) )
  if ((((((op0 == 3) && (crn == 9)) && (op1 == 3)) && (op2 == 0)) && (crm == 12)) : Bool)
  then
    (do
      if ((←((pure ((BitVec.join1 [(BitVec.access tempxt 3)]) == 1#1)) <&&> (do
           (pure ((_get_PMCR_EL0_Type_D (← readReg PMCR_EL0)) == 0#1))))) : Bool)
      then writeReg __clock_divider 63
      else (pure ()))
  else (pure ())
  if (((((op0 == 3) && (crn == 14)) && (op1 == 3)) && (((integer_subrange crm 3 2) == 0b10#2) || (((integer_subrange crm 3 2) == 0b11#2) && (((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0)) != 0b11111#5)))) : Bool)
  then
    (do
      if ((←((pure (((BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b ((← (GetNumEventCounters ())) -i 1)) && (((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0)) != 0b11111#5))) <||> (do
           (EL2Enabled ()) <&&> (do
             (pure ((← readReg PSTATE).EL == EL0)) <||> (do
               (pure ((← readReg PSTATE).EL == EL1)))) <&&> (do
             (pure ((_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)) == 1#1))) <&&> (do
             (pure ((BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b ((← (AArch64_GetNumEventCountersAccessible ())) -i 1))))))) : Bool)
      then
        (do
          if (((BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0))) >b ((← (GetNumEventCounters ())) -i 1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
      else (pure ()))
  else (pure ())
  if ((←((pure ((((op0 == 3) && (op1 == 3)) && (crn == 9)) && (crm == 13))) <&&> (do
       (pure (op2 == 2)) <||> (do
         (pure (op2 == 1)) <&&> (do
           (pure ((_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)) != 0b11111#5))))))) : Bool)
  then
    (do
      if ((←((pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (GetNumEventCounters ())) -i 1))) <&&> (do
           (pure ((_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)) != 0b11111#5))) <||> (do
           (EL2Enabled ()) <&&> (do
             (pure ((← readReg PSTATE).EL == EL0)) <||> (do
               (pure ((← readReg PSTATE).EL == EL1)))) <&&> (do
             (pure ((_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)) == 1#1))) <&&> (do
             (pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (AArch64_GetNumEventCountersAccessible ())) -i 1))))))) : Bool)
      then
        (do
          if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (GetNumEventCounters ())) -i 1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
      else (pure ()))
  else (pure ())
  let tempxt ← (( do
    if (((((op0 == 2) && (op1 == 0)) && (crn == 7)) && (op2 == 6)) : Bool)
    then
      (do
        let tempxt ← (( do
          if ((crm == 8) : Bool)
          then (do (pure (Sail.BitVec.updateSubrange tempxt 7 0 ((Sail.BitVec.extractLsb (← readReg DBGCLAIMCLR_EL1) 7 0) ||| (Sail.BitVec.extractLsb tempxt 7 0)))))
          else (pure tempxt) ) : SailME Unit (BitVec 64) )
        if ((crm == 9) : Bool)
        then (do (pure (Sail.BitVec.updateSubrange tempxt 7 0 ((Sail.BitVec.extractLsb (← readReg DBGCLAIMCLR_EL1) 7 0) &&& (Complement.complement (Sail.BitVec.extractLsb tempxt 7 0))))))
        else (pure tempxt))
    else (pure tempxt) ) : SailME Unit (BitVec 64) )
  let tempxt2 ← (( do (undefined_bitvector 64) ) : SailME Unit (BitVec 64) )
  let restore_xt ← (( do (undefined_bool ()) ) : SailME Unit Bool )
  let (restore_xt, tempxt2) ← (( do
    if ((tempxt != (← (X_read t 64))) : Bool)
    then
      (do
        let tempxt2 ← (X_read t 64)
        (X_set t 64 tempxt)
        let restore_xt : Bool := true
        (pure (restore_xt, tempxt2)))
    else
      (let restore_xt : Bool := false
      (pure (restore_xt, tempxt2))) ) : SailME Unit (Bool × (BitVec 64)) )
  (AArch64_AutoGen_SysRegWrite (← readReg PSTATE).EL (integer_subrange op0 1 0) (integer_subrange op1 2 0) (integer_subrange crn 3 0) (integer_subrange op2 2 0) (integer_subrange crm 3 0) t)
  if (restore_xt : Bool)
  then (X_set t 64 tempxt2)
  else (pure ())
  if ((((((op0 == 2) && (op1 == 0)) && (crn == 7)) && (op2 == 6)) && (crm == 8)) : Bool)
  then writeReg DBGCLAIMCLR_EL1 (Sail.BitVec.updateSubrange (← readReg DBGCLAIMCLR_EL1) 7 0 (Sail.BitVec.extractLsb tempxt 7 0))
  else (pure ())
  if ((((((crm == 0) && (crn == 1)) && (op0 == 2)) && (op1 == 0)) && (op2 == 4)) : Bool)
  then
    (do
      if ((←((pure ((_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)) == 1#1)) <&&> (do
           (pure ((_get_OSLAR_EL1_Type_OSLK (← readReg OSLAR_EL1)) == 0#1))))) : Bool)
      then (CheckOSUnlockCatch ())
      else (pure ())
      writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange (← readReg OSLSR_EL1) 1 1 (_get_OSLAR_EL1_Type_OSLK (← readReg OSLAR_EL1)))
      writeReg EDPRSR (Sail.BitVec.updateSubrange (← readReg EDPRSR) 5 5 (_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)))
      (DBGOSLSR_write (_update_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ())) (_get_OSLSR_EL1_Type_OSLK (← readReg OSLSR_EL1)))))
  else (pure ())
  if (((((op0 == 2) && (op1 == 1)) && (crn == 7)) && (op2 == 6)) : Bool)
  then
    (do
      if ((crm == 8) : Bool)
      then SailME.throw (← (do writeReg __trcclaim_tags ((← readReg __trcclaim_tags) ||| (Sail.BitVec.extractLsb tempxt 31 0))))
      else
        (do
          if ((crm == 9) : Bool)
          then SailME.throw (← (do writeReg __trcclaim_tags ((← readReg __trcclaim_tags) &&& (Complement.complement (Sail.BitVec.extractLsb tempxt 31 0)))))
          else (pure ())))
  else (pure ())
  if (((((((op0 == 3) && ((crn == (BitVec.toNat 0xC#4)) : Bool)) && (((op1 == 6) || (op1 == 4)) || (op1 == 0))) && (op2 == 2)) && (crm == 0)) && ((BitVec.join1 [(BitVec.access tempxt 1)]) == 1#1)) : Bool)
  then (TakeReset false)
  else (pure ())
  if ((((((op0 == 3) && (crn == 9)) && (op1 == 3)) && (op2 == 3)) && ((crm == 12) || (crm == 14))) : Bool)
  then
    (do
      if ((crm == 12) : Bool)
      then writeReg PMOVSSET_EL0 (Mk_PMOVSSET_EL0_Type tempxt)
      else (pure ())
      if ((crm == 14) : Bool)
      then writeReg PMOVSCLR_EL0 (Mk_PMOVSCLR_EL0_Type tempxt)
      else (pure ()))
  else (pure ())
  if ((((((op0 == 3) && (crn == 9)) && (op1 == 3)) && ((op2 == 1) || (op2 == 2))) && (crm == 12)) : Bool)
  then
    (do
      if ((op2 == 2) : Bool)
      then writeReg PMCNTENSET_EL0 (Mk_PMCNTENSET_EL0_Type tempxt)
      else (pure ())
      if ((op2 == 1) : Bool)
      then writeReg PMCNTENCLR_EL0 (Mk_PMCNTENCLR_EL0_Type tempxt)
      else (pure ()))
  else (pure ())
  if ((((((op0 == 3) && (crn == 9)) && (op1 == 0)) && ((op2 == 1) || (op2 == 2))) && (crm == 14)) : Bool)
  then
    (do
      if ((op2 == 2) : Bool)
      then writeReg PMINTENSET_EL1 (Mk_PMINTENSET_EL1_Type tempxt)
      else (pure ())
      if ((op2 == 1) : Bool)
      then writeReg PMINTENCLR_EL1 (Mk_PMINTENCLR_EL1_Type tempxt)
      else (pure ()))
  else (pure ())
  if ((((((op0 == 3) && (crn == 9)) && (op1 == 3)) && (op2 == 0)) && (crm == 12)) : Bool)
  then
    (do
      if (((BitVec.join1 [(BitVec.access tempxt 2)]) == 1#1) : Bool)
      then writeReg PMCCNTR_EL0 (Mk_PMCCNTR_EL0_Type (Zeros (n := 64)))
      else (pure ())
      if (((BitVec.join1 [(BitVec.access tempxt 1)]) == 1#1) : Bool)
      then (AArch64_ClearEventCounters ())
      else (pure ()))
  else (pure ())
  if ((((((op0 == 3) && (op1 == 3)) && (crn == 9)) && (crm == 13)) && ((op2 == 1) || (op2 == 2))) : Bool)
  then
    (do
      if ((op2 == 1) : Bool)
      then
        (do
          if (((_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)) == 0b11111#5) : Bool)
          then writeReg PMCCFILTR_EL0 (__get_PMCCFILTR_EL0 (Mk_PMCCFILTR_EL0_Type tempxt))
          else
            (do
              let pmselr_el0 ← do (pure (BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))))
              sail_assert (pmselr_el0 <b 31) "src/sysregs.sail:748.38-748.39"
              writeReg PMEVTYPER_EL0 (vectorUpdate (← readReg PMEVTYPER_EL0) pmselr_el0 (__get_PMEVTYPER_EL0 (Mk_PMEVTYPER_EL0_Type tempxt)))))
      else (pure ())
      if ((op2 == 2) : Bool)
      then
        (do
          let pmselr_el0 ← do (pure (BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))))
          sail_assert (pmselr_el0 <b 31) "src/sysregs.sail:754.34-754.35"
          writeReg PMEVCNTR_EL0 (vectorUpdate (← readReg PMEVCNTR_EL0) pmselr_el0 tempxt))
      else (pure ()))
  else (pure ())
  if (((((op0 == 3) && (op1 == 3)) && (crn == 14)) && ((integer_subrange crm 3 2) == 0b11#2)) : Bool)
  then
    (do
      let index := (BitVec.toNat ((integer_subrange crm 1 0) +++ (integer_subrange op2 2 0)))
      if ((index == 31) : Bool)
      then writeReg PMCCFILTR_EL0 (__get_PMCCFILTR_EL0 (Mk_PMCCFILTR_EL0_Type tempxt))
      else writeReg PMEVTYPER_EL0 (vectorUpdate (← readReg PMEVTYPER_EL0) index (__get_PMEVTYPER_EL0 (Mk_PMEVTYPER_EL0_Type tempxt))))
  else (pure ())
  if ((((((op0 == 3) && (crn == 9)) && (op1 == 3)) && (op2 == 4)) && (crm == 12)) : Bool)
  then (AArch64_PMUSwIncrement (Sail.BitVec.extractLsb tempxt 31 0))
  else (pure ())
  if ((((((op0 == 2) && (crn == 0)) && (op1 == 3)) && (op2 == 0)) && (crm == 5)) : Bool)
  then
    (do
      (DBGDSCRint_write (_update_DBGDSCRint_Type_TXfull (← (DBGDSCRint_read ())) 1#1))
      writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange (← readReg MDCCSR_EL0) 29 29 1#1)
      (DBGDSCRext_write (_update_DBGDSCRext_Type_TXfull (← (DBGDSCRext_read ())) 1#1))
      (EDSCR_write (_update_EDSCR_Type_TXfull (← (EDSCR_read ())) 1#1)))
  else (pure ())
  if ((((((op0 == 2) && (crn == 0)) && (op1 == 3)) && (op2 == 0)) && (crm == 4)) : Bool)
  then
    (do
      (DBGDSCRint_write (_update_DBGDSCRint_Type_TXfull (← (DBGDSCRint_read ())) 1#1))
      writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange (← readReg MDCCSR_EL0) 29 29 1#1)
      (DBGDSCRext_write (_update_DBGDSCRext_Type_TXfull (← (DBGDSCRext_read ())) 1#1))
      (EDSCR_write (_update_EDSCR_Type_TXfull (← (EDSCR_read ())) 1#1))
      writeReg DBGDTRTX_EL0 (Sail.BitVec.updateSubrange (← readReg DBGDTRTX_EL0) 31 0 (BitVec.slice (← (DBGDTR_EL0_read__1 ())) 0 32))
      writeReg DBGDTRRX_EL0 (Sail.BitVec.updateSubrange (← readReg DBGDTRRX_EL0) 31 0 (BitVec.slice (← (DBGDTR_EL0_read__1 ())) 32 32)))
  else (pure ())
  if ((((((op0 == 3) && (crn == 12)) && (op1 == 4)) && (op2 == 7)) && (crm == 11)) : Bool)
  then
    (do
      writeReg ICV_PMR_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_PMR_EL1) 7 0 (_get_ICH_VMCR_EL2_Type_VPMR (← readReg ICH_VMCR_EL2)))
      writeReg ICV_BPR0_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_BPR0_EL1) 2 0 (_get_ICH_VMCR_EL2_Type_VBPR0 (← readReg ICH_VMCR_EL2)))
      writeReg ICV_BPR1_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_BPR1_EL1) 2 0 (_get_ICH_VMCR_EL2_Type_VBPR1 (← readReg ICH_VMCR_EL2)))
      writeReg ICV_IGRPEN0_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_IGRPEN0_EL1) 0 0 (_get_ICH_VMCR_EL2_Type_VENG0 (← readReg ICH_VMCR_EL2)))
      writeReg ICV_IGRPEN1_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_IGRPEN1_EL1) 0 0 (_get_ICH_VMCR_EL2_Type_VENG1 (← readReg ICH_VMCR_EL2)))
      writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_CTLR_EL1) 1 1 (_get_ICH_VMCR_EL2_Type_VEOIM (← readReg ICH_VMCR_EL2)))
      writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_CTLR_EL1) 0 0 (_get_ICH_VMCR_EL2_Type_VCBPR (← readReg ICH_VMCR_EL2))))
  else (pure ())
  if ((((((op0 == 3) && (crn == 4)) && (op1 == 0)) && (op2 == 0)) && (crm == 6)) : Bool)
  then writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 31 24 (_get_ICV_PMR_EL1_Type_Priority (← readReg ICV_PMR_EL1)))
  else (pure ())
  if ((((((op0 == 3) && (crn == 12)) && (op1 == 0)) && (op2 == 3)) && (crm == 8)) : Bool)
  then writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 23 21 (_get_ICV_BPR0_EL1_Type_BinaryPoint (← readReg ICV_BPR0_EL1)))
  else (pure ())
  if ((((((op0 == 3) && (crn == 12)) && (op1 == 0)) && (op2 == 3)) && (crm == 12)) : Bool)
  then writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 20 18 (_get_ICV_BPR1_EL1_Type_BinaryPoint (← readReg ICV_BPR1_EL1)))
  else (pure ())
  if ((((((op0 == 3) && (crn == 12)) && (op1 == 0)) && (op2 == 4)) && (crm == 12)) : Bool)
  then
    (do
      writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 9 9 (_get_ICV_CTLR_EL1_Type_EOImode (← readReg ICV_CTLR_EL1)))
      writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 4 4 (_get_ICV_CTLR_EL1_Type_CBPR (← readReg ICV_CTLR_EL1))))
  else (pure ())
  if ((((((op0 == 3) && (crn == 12)) && (op1 == 0)) && (op2 == 6)) && (crm == 12)) : Bool)
  then writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 0 0 (_get_ICV_IGRPEN0_EL1_Type_Enable (← readReg ICV_IGRPEN0_EL1)))
  else (pure ())
  if ((((((op0 == 3) && (crn == 12)) && (op1 == 0)) && (op2 == 7)) && (crm == 12)) : Bool)
  then writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 1 1 (_get_ICV_IGRPEN1_EL1_Type_Enable (← readReg ICV_IGRPEN1_EL1)))
  else (pure ())

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int -/
def AArch64_SysInstr (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) : SailM Unit := do
  (AArch64_AutoGen_SysOpsWrite (← readReg PSTATE).EL (integer_subrange op0 1 0) (integer_subrange op1 2 0) (integer_subrange crn 3 0) (integer_subrange op2 2 0) (integer_subrange crm 3 0) t)

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int -/
def AArch64_SysInstrWithResult (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) : SailM Unit := do
  (AArch64_AutoGen_SysInstrWithResult (← readReg PSTATE).EL (integer_subrange op0 1 0) (integer_subrange op1 2 0) (integer_subrange crn 3 0) (integer_subrange op2 2 0) (integer_subrange crm 3 0) t)

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int, t2 : Int -/
def AArch64_SysRegRead128 (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) (t2 : Int) : SailM Unit := do
  (AArch64_AutoGen_SysRegRead128 (← readReg PSTATE).EL (integer_subrange op0 1 0) (integer_subrange op1 2 0) (integer_subrange crn 3 0) (integer_subrange op2 2 0) (integer_subrange crm 3 0) t t2)

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int, t2 : Int -/
def AArch64_SysRegWrite128 (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) (t2 : Int) : SailM Unit := do
  (AArch64_AutoGen_SysRegWrite128 (← readReg PSTATE).EL (integer_subrange op0 1 0) (integer_subrange op1 2 0) (integer_subrange crn 3 0) (integer_subrange op2 2 0) (integer_subrange crm 3 0) t t2)

/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int, t2 : Int -/
def AArch64_SysInstr128 (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) (t2 : Int) : SailM Unit := do
  (AArch64_AutoGen_SysOpsWrite128 (← readReg PSTATE).EL (integer_subrange op0 1 0) (integer_subrange op1 2 0) (integer_subrange crn 3 0) (integer_subrange op2 2 0) (integer_subrange crm 3 0) t t2)

/-- Type quantifiers: cp_num : Int -/
def AArch32_SysRegRead (cp_num : Int) (instr : (BitVec 32)) (address : (BitVec 32)) : SailM Unit := do
  let CRd : (BitVec 4) := (Sail.BitVec.extractLsb instr 15 12)
  if (((CRd == 0b0101#4) && ((cp_num == (BitVec.toNat 0xE#4)) : Bool)) : Bool)
  then (AArch32_STC (integer_subrange cp_num 3 0) CRd address)
  else (pure ())

/-- Type quantifiers: cp_num : Int, t : Int -/
def AArch32_SysRegRead__1 (cp_num : Int) (instr : (BitVec 32)) (t : Int) : SailM Unit := do
  let el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let index ← (( do (undefined_int ()) ) : SailM Int )
  let n ← (( do (undefined_int ()) ) : SailM Int )
  let el ← (( do
    let (_, __tup_1) ← do (ELFromM32 (← readReg PSTATE).M)
    (pure __tup_1) ) : SailM (BitVec 2) )
  let opc1 : (BitVec 3) := (BitVec.slice instr 21 3)
  let CRn : (BitVec 4) := (BitVec.slice instr 16 4)
  let CRm : (BitVec 4) := (BitVec.slice instr 0 4)
  let opc2 : (BitVec 3) := (BitVec.slice instr 5 3)
  let opc2 : (BitVec 3) :=
    if ((((((cp_num == 15) && (opc1 == 0b000#3)) && ((opc2 == 0b100#3) || (opc2 == 0b111#3))) && (CRn == 0b0000#4)) && (CRm == 0b0000#4)) : Bool)
    then 0b000#3
    else opc2
  if ((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1101#4)) : Bool)
  then
    (do
      let n := (BitVec.toNat ((BitVec.join1 [(BitVec.access CRm 0)]) +++ opc2))
      if (((Sail.BitVec.extractLsb CRm 3 1) == 0b011#3) : Bool)
      then
        (do
          if ((n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG0NC (← (AMCGCR_read ()))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (pure ()))
      else (pure ())
      if (((Sail.BitVec.extractLsb CRm 3 1) == 0b111#3) : Bool)
      then
        (do
          if ((n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG1NC (← (AMCGCR_read ()))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (pure ()))
      else (pure ()))
  else (pure ())
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1110#4)) && (((Sail.BitVec.extractLsb CRm 3 2) == 0b10#2) || ((Sail.BitVec.extractLsb CRm 3 2) == 0b11#2))) && (((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0)) != 0b11111#5)) : Bool)
  then
    (do
      if ((←((pure ((BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (GetNumEventCounters ())) -i 1))) <||> (do
           (EL2Enabled ()) <&&> (do
             (pure ((← readReg PSTATE).EL == EL1)) <||> (do
               (pure ((← readReg PSTATE).EL == EL0)) <&&> (do
                 (pure ((Sail.BitVec.extractLsb CRm 3 2) == 0b10#2)) <&&> (do
                   (pure (((_get_PMUSERENR_EL0_Type_ER (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) != 0b00#2))) <||> (do
                   (pure ((Sail.BitVec.extractLsb CRm 3 2) == 0b11#2)) <&&> (do
                     (pure ((_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)) == 1#1))))))) <&&> (do
             (pure ((BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (AArch32_GetNumEventCountersAccessible ())) -i 1))))))) : Bool)
      then
        (do
          if (((BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (GetNumEventCounters ())) -i 1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((← (ELUsingAArch32 EL2)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
      else (pure ()))
  else (pure ())
  if ((←((pure (((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1001#4)) && (CRm == 0b1101#4)) && ((opc2 == 0b001#3) || (opc2 == 0b010#3)))) <&&> (do
       (pure ((_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0)) != 0b11111#5))))) : Bool)
  then
    (do
      if ((←((pure ((BitVec.toNat (_get_PMSELR_EL0_Type_SEL (← readReg PMSELR_EL0))) >b ((← (GetNumEventCounters ())) -i 1))) <||> (do
           (EL2Enabled ()) <&&> (do
             (pure ((← readReg PSTATE).EL == EL1)) <||> (do
               (pure ((← readReg PSTATE).EL == EL0)) <&&> (do
                 (pure (opc2 == 0b010#3)) <&&> (do
                   (pure (((_get_PMUSERENR_EL0_Type_ER (← readReg PMUSERENR_EL0)) +++ (_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0))) != 0b00#2))) <||> (do
                   (pure (opc2 == 0b001#3)) <&&> (do
                     (pure ((_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)) == 1#1))))))) <&&> (do
             (pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (AArch32_GetNumEventCountersAccessible ())) -i 1))))))) : Bool)
      then
        (do
          if (((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (GetNumEventCounters ())) -i 1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((← (ELUsingAArch32 EL2)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
      else (pure ()))
  else (pure ())
  let temp ← (( do (R_read t) ) : SailM (BitVec 32) )
  (AArch32_AutoGen_SysRegRead32 el (integer_subrange cp_num 3 0) opc1 CRn opc2 CRm t)
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1001#4)) && ((CRm == 0b1100#4) || (CRm == 0b1110#4))) && ((opc2 == 0b001#3) || ((opc2 == 0b010#3) || (opc2 == 0b011#3)))) : Bool)
  then
    (do
      let mask ← (( do (pure (Sail.BitVec.extractLsb (← (PMUCounterMask ())) 31 0)) ) : SailM (BitVec 32) )
      (R_set t ((← (R_read t)) &&& mask)))
  else (pure ())
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1001#4)) && (CRm == 0b1101#4)) && ((opc2 == 0b001#3) || (opc2 == 0b010#3))) : Bool)
  then
    (do
      if ((opc2 == 0b001#3) : Bool)
      then
        (do
          let pmselr ← do (pure (BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))))
          if ((←((EL2Enabled ()) <&&> (do
               (pure ((← readReg PSTATE).EL == EL0)) <||> (do
                 (pure ((← readReg PSTATE).EL == EL1)))) <&&> (do
               (pure ((_get_PMSELR_Type_SEL (← (PMSELR_read ()))) != 0b11111#5))) <&&> (do
               (pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (AArch32_GetNumEventCountersAccessible ())) -i 1)))))) : Bool)
          then
            (do
              if (((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (GetNumEventCounters ())) -i 1)) : Bool)
              then
                (do
                  (R_set t temp)
                  (sailThrow ((Error_Undefined ())) : SailM Unit))
              else
                (do
                  if ((← (ELUsingAArch32 EL2)) : Bool)
                  then
                    (do
                      (R_set t temp)
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      (R_set t temp)
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
          else
            (do
              if ((pmselr == 31) : Bool)
              then (R_set t (← (PMCCFILTR_read ())))
              else (R_set t (← (PMEVTYPER_read pmselr)))))
      else (pure ())
      if ((opc2 == 0b010#3) : Bool)
      then
        (do
          if ((←((pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (GetNumEventCounters ())) -i 1))) <||> (do
               (EL2Enabled ()) <&&> (do
                 (pure ((← readReg PSTATE).EL == EL0)) <||> (do
                   (pure ((← readReg PSTATE).EL == EL1)))) <&&> (do
                 (pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (AArch32_GetNumEventCountersAccessible ())) -i 1))))))) : Bool)
          then
            (do
              if (((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (GetNumEventCounters ())) -i 1)) : Bool)
              then
                (do
                  (R_set t temp)
                  (sailThrow ((Error_Undefined ())) : SailM Unit))
              else
                (do
                  if ((← (ELUsingAArch32 EL2)) : Bool)
                  then
                    (do
                      (R_set t temp)
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                  else
                    (do
                      (R_set t temp)
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
          else
            (do
              let pmselr ← do (pure (BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))))
              sail_assert (pmselr <b 31) "src/sysregs.sail:1058.34-1058.35"
              (R_set t (Sail.BitVec.extractLsb (← (PMEVCNTR_read pmselr)) 31 0))))
      else (pure ()))
  else (pure ())
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (opc2 == 0b000#3)) && (CRn == 0b1001#4)) && (CRm == 0b1100#4)) : Bool)
  then (R_set t (Sail.BitVec.updateSubrange (← (R_read t)) 15 11 (integer_subrange (← (AArch32_GetNumEventCountersAccessible ())) 4 0)))
  else (pure ())
  if (((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1110#4)) && (((Sail.BitVec.extractLsb CRm 3 2) == 0b10#2) || (((Sail.BitVec.extractLsb CRm 3 2) == 0b11#2) && (((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0)) != 0b11111#5)))) : Bool)
  then
    (do
      if ((←((pure ((BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (GetNumEventCounters ())) -i 1))) <||> (do
           (EL2Enabled ()) <&&> (do
             (pure ((← readReg PSTATE).EL == EL0)) <||> (do
               (pure ((← readReg PSTATE).EL == EL1)))) <&&> (do
             (pure ((BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (AArch32_GetNumEventCountersAccessible ())) -i 1))))))) : Bool)
      then
        (do
          if (((BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (GetNumEventCounters ())) -i 1)) : Bool)
          then
            (do
              (R_set t temp)
              (sailThrow ((Error_Undefined ())) : SailM Unit))
          else
            (do
              if ((← (ELUsingAArch32 EL2)) : Bool)
              then
                (do
                  (R_set t temp)
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  (R_set t temp)
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
      else (pure ()))
  else (pure ())
  if (((((cp_num == 14) && (opc1 == 0b000#3)) && (opc2 == 0b110#3)) && (CRn == 0b0111#4)) : Bool)
  then
    (do
      if ((CRm == 0b1000#4) : Bool)
      then (R_set t (Sail.BitVec.updateSubrange (← (R_read t)) 7 0 0b11111111#8))
      else (pure ())
      if ((CRm == 0b1001#4) : Bool)
      then (R_set t (Sail.BitVec.updateSubrange (← (R_read t)) 7 0 (Sail.BitVec.extractLsb (← (DBGCLAIMCLR_read ())) 7 0)))
      else (pure ()))
  else
    (do
      if ((((((cp_num == 14) && (opc1 == 0b000#3)) && (opc2 == 0b010#3)) && (CRn == 0b0000#4)) && (CRm == 0b0010#4)) : Bool)
      then
        (do
          (R_set t
            (Sail.BitVec.updateSubrange (← (R_read t)) 18 18
              (← (do
                if ((BEq.beq (← (CurrentSecurityState ())) SS_NonSecure) : Bool)
                then (pure 1#1)
                else (pure 0#1)))))
          if ((HaveEL EL3) : Bool)
          then
            (do
              if ((←((ELUsingAArch32 EL3) <&&> (do
                   (pure ((_get_SDCR_Type_SPME (← readReg SDCR)) == 1#1))))) : Bool)
              then (R_set t (Sail.BitVec.updateSubrange (← (R_read t)) 17 17 0#1))
              else
                (do
                  if ((←((pure (! (← (ELUsingAArch32 EL3)))) <&&> (do
                       (pure ((_get_MDCR_EL3_Type_SPME (← readReg MDCR_EL3)) == 1#1))))) : Bool)
                  then (R_set t (Sail.BitVec.updateSubrange (← (R_read t)) 17 17 0#1))
                  else (R_set t (Sail.BitVec.updateSubrange (← (R_read t)) 17 17 1#1))))
          else (pure ()))
      else
        (do
          if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (opc2 == 0b000#3)) && (CRn == 0b1100#4)) && (CRm == 0b0001#4)) : Bool)
          then (do (R_set t (← (getISR ()))))
          else
            (do
              if ((((((cp_num == 15) && (opc1 == 0b001#3)) && ((opc2 == 0b000#3) || (opc2 == 0b010#3))) && (CRn == 0b0000#4)) && (CRm == 0b0000#4)) : Bool)
              then
                (do
                  if ((opc2 == 0b000#3) : Bool)
                  then (do (R_set t (Sail.BitVec.extractLsb (← (CacheConfigRead (Sail.BitVec.extractLsb (← (CSSELR_read ())) 3 0))) 31 0)))
                  else (do (R_set t (Sail.BitVec.extractLsb (← (CacheConfigRead (Sail.BitVec.extractLsb (← (CSSELR_read ())) 3 0))) 63 32))))
              else
                (do
                  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b0101#4)) && (CRm == 0b0100#4)) && ((opc2 == 0b000#3) || (opc2 == 0b100#3))) : Bool)
                  then
                    (do
                      if ((←((pure ((BitVec.toNat (_get_ERRIDR_Type_NUM (← (ERRIDR_read ())))) == (BitVec.toNat 0x0#4))) <||> (do
                           (pure ((BitVec.toNat (_get_ERRSELR_Type_SEL (← (ERRSELR_read ())))) ≥b (BitVec.toNat (_get_ERRIDR_Type_NUM (← (ERRIDR_read ()))))))))) : Bool)
                      then (R_set t (Zeros (n := 32)))
                      else
                        (do
                          let index ← do (pure (BitVec.toNat (_get_ERRSELR_Type_SEL (← (ERRSELR_read ())))))
                          if ((opc2 == 0b000#3) : Bool)
                          then
                            (do
                              sail_assert ((0 ≤b index) && (index <b 4)) "src/sysregs.sail:1125.61-1125.62"
                              (R_set t (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg ERRnFR) index) 31 0)))
                          else
                            (do
                              sail_assert ((0 ≤b index) && (index <b 4)) "src/sysregs.sail:1128.61-1128.62"
                              (R_set t (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg ERRnFR) index) 63 32)))))
                  else (pure ())
                  if ((((((cp_num == 14) && (opc1 == 0b000#3)) && (CRn == 0b0000#4)) && (CRm == 0b0101#4)) && (opc2 == 0b000#3)) : Bool)
                  then
                    (do
                      (DBGDSCRint_write (_update_DBGDSCRint_Type_RXfull (← (DBGDSCRint_read ())) 0#1))
                      writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange (← readReg MDCCSR_EL0) 30 30 0#1)
                      (DBGDSCRext_write (_update_DBGDSCRext_Type_RXfull (← (DBGDSCRext_read ())) 0#1))
                      (EDSCR_write (_update_EDSCR_Type_RXfull (← (EDSCR_read ())) 0#1)))
                  else (pure ())
                  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b0001#4)) && (CRm == 0b0000#4)) && (opc2 == 0b010#3)) : Bool)
                  then
                    (do
                      if ((←((pure ((BEq.beq (← (CurrentSecurityState ())) SS_NonSecure) && (HaveEL EL3))) <&&> (do
                           (ELUsingAArch32 EL3)) <&&> (do
                           (pure ((_get_NSACR_Type_cp10 (← readReg NSACR)) == 0#1))))) : Bool)
                      then (R_set t (Sail.BitVec.updateSubrange (← (R_read t)) 23 20 0b0000#4))
                      else (pure ()))
                  else (pure ())))))

/-- Type quantifiers: cp_num : Int -/
def AArch32_SysRegWriteM (cp_num : Int) (instr : (BitVec 32)) (address : (BitVec 32)) : SailM Unit := do
  let CRd : (BitVec 4) := (Sail.BitVec.extractLsb instr 15 12)
  if (((CRd == 0b0101#4) && ((cp_num == (BitVec.toNat 0xE#4)) : Bool)) : Bool)
  then (AArch32_LDC (integer_subrange cp_num 3 0) CRd address)
  else (pure ())

/-- Type quantifiers: cp_num : Int, t : Int, t2 : Int -/
def AArch32_SysRegRead64 (cp_num : Int) (instr : (BitVec 32)) (t : Int) (t2 : Int) : SailM Unit := do
  let el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let n ← (( do (undefined_int ()) ) : SailM Int )
  let el ← (( do
    let (_, __tup_1) ← do (ELFromM32 (← readReg PSTATE).M)
    (pure __tup_1) ) : SailM (BitVec 2) )
  let opc1 : (BitVec 4) := (BitVec.slice instr 4 4)
  let CRm : (BitVec 4) := (BitVec.slice instr 0 4)
  if ((((cp_num == 15) && (let b__0 := (Sail.BitVec.extractLsb CRm 3 1)
         if ((((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
         then true
         else false : Bool)) && ((BitVec.join1 [(BitVec.access opc1 3)]) == 0#1)) : Bool)
  then
    (do
      let n := (BitVec.toNat ((BitVec.join1 [(BitVec.access CRm 0)]) +++ (Sail.BitVec.extractLsb opc1 2 0)))
      if (((Sail.BitVec.extractLsb CRm 3 1) == 0b000#3) : Bool)
      then
        (do
          if ((n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG0NC (← (AMCGCR_read ()))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (pure ()))
      else
        (do
          if (((Sail.BitVec.extractLsb CRm 3 1) == 0b010#3) : Bool)
          then
            (do
              if ((n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG1NC (← (AMCGCR_read ()))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ()))
          else (pure ())))
  else (pure ())
  (AArch32_AutoGen_SysRegRead64 el (integer_subrange cp_num 3 0) opc1 CRm t t2)

/-- Type quantifiers: cp_num : Int, t : Int -/
def AArch32_SysRegWrite (cp_num : Int) (instr : (BitVec 32)) (t : Int) : SailM Unit := do
  let el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let temprt ← (( do (R_read t) ) : SailM (BitVec 32) )
  let el ← (( do
    let (_, __tup_1) ← do (ELFromM32 (← readReg PSTATE).M)
    (pure __tup_1) ) : SailM (BitVec 2) )
  let opc1 : (BitVec 3) := (BitVec.slice instr 21 3)
  let CRn : (BitVec 4) := (BitVec.slice instr 16 4)
  let CRm : (BitVec 4) := (BitVec.slice instr 0 4)
  let opc2 : (BitVec 3) := (BitVec.slice instr 5 3)
  let temprt : (BitVec 32) :=
    if (((((cp_num == 14) && (opc1 == 0b000#3)) && (CRn == 0b0000#4)) && (opc2 == 0b101#3)) : Bool)
    then
      (let temprt : (BitVec 32) := (BitVec.update temprt 8 (Bit (BitVec.join1 [(BitVec.access temprt 7)])))
      (BitVec.update temprt 6 (Bit (BitVec.join1 [(BitVec.access temprt 5)]))))
    else temprt
  let temprt ← (( do
    if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b0001#4)) && (CRm == 0b0000#4)) && (opc2 == 0b010#3)) : Bool)
    then
      (do
        if ((←((pure ((BEq.beq (← (CurrentSecurityState ())) SS_NonSecure) && (HaveEL EL3))) <&&> (do
             (ELUsingAArch32 EL3)) <&&> (do
             (pure ((_get_NSACR_Type_cp10 (← readReg NSACR)) == 0#1))))) : Bool)
        then
          (do
            let temprt ← (pure (Sail.BitVec.updateSubrange temprt 23 22 (_get_CPACR_Type_cp11 (← (CPACR_read__1 ())))))
            (pure (Sail.BitVec.updateSubrange temprt 21 20 (_get_CPACR_Type_cp10 (← (CPACR_read__1 ()))))))
        else (pure temprt))
    else (pure temprt) ) : SailM (BitVec 32) )
  let temprt ← (( do
    if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1001#4)) && ((CRm == 0b1100#4) || (CRm == 0b1110#4))) && ((opc2 == 0b001#3) || ((opc2 == 0b010#3) || (opc2 == 0b011#3)))) : Bool)
    then
      (do
        let mask ← (( do (pure (Sail.BitVec.extractLsb (← (PMUCounterMask ())) 31 0)) ) : SailM (BitVec 32) )
        let temprt ← (( do
          if (((opc2 == 0b011#3) && (CRm == 0b1100#4)) : Bool)
          then (do (pure ((← (PMOVSSET_read ())) &&& (Complement.complement (temprt &&& mask)))))
          else (pure temprt) ) : SailM (BitVec 32) )
        let temprt ← (( do
          if (((opc2 == 0b011#3) && (CRm == 0b1110#4)) : Bool)
          then (do (pure ((← (PMOVSSET_read ())) ||| (temprt &&& mask))))
          else (pure temprt) ) : SailM (BitVec 32) )
        let temprt ← (( do
          if (((opc2 == 0b010#3) && (CRm == 0b1100#4)) : Bool)
          then (do (pure ((← (PMCNTENSET_read ())) &&& (Complement.complement (temprt &&& mask)))))
          else (pure temprt) ) : SailM (BitVec 32) )
        let temprt ← (( do
          if (((opc2 == 0b001#3) && (CRm == 0b1100#4)) : Bool)
          then (do (pure ((← (PMCNTENSET_read ())) ||| (temprt &&& mask))))
          else (pure temprt) ) : SailM (BitVec 32) )
        let temprt ← (( do
          if (((opc2 == 0b010#3) && (CRm == 0b1110#4)) : Bool)
          then (do (pure ((← (PMINTENSET_read ())) &&& (Complement.complement (temprt &&& mask)))))
          else (pure temprt) ) : SailM (BitVec 32) )
        if (((opc2 == 0b001#3) && (CRm == 0b1110#4)) : Bool)
        then (do (pure ((← (PMINTENSET_read ())) ||| (temprt &&& mask))))
        else (pure temprt))
    else (pure temprt) ) : SailM (BitVec 32) )
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (opc2 == 0b000#3)) && (CRn == 0b1001#4)) && (CRm == 0b1100#4)) : Bool)
  then
    (do
      if ((←((pure ((BitVec.join1 [(BitVec.access temprt 3)]) == 1#1)) <&&> (do
           (pure ((_get_PMCR_Type_D (← (PMCR_read ()))) == 0#1))))) : Bool)
      then writeReg __clock_divider 63
      else (pure ()))
  else (pure ())
  if (((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1110#4)) && (((Sail.BitVec.extractLsb CRm 3 2) == 0b10#2) || (((Sail.BitVec.extractLsb CRm 3 2) == 0b11#2) && (((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0)) != 0b11111#5)))) : Bool)
  then
    (do
      if ((←((pure (((BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (GetNumEventCounters ())) -i 1)) && (((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0)) != 0b11111#5))) <||> (do
           (EL2Enabled ()) <&&> (do
             (pure ((← readReg PSTATE).EL == EL0)) <||> (do
               (pure ((← readReg PSTATE).EL == EL1)))) <&&> (do
             (pure ((_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)) == 1#1))) <&&> (do
             (pure ((BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (AArch32_GetNumEventCountersAccessible ())) -i 1))))))) : Bool)
      then
        (do
          if (((BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b ((← (GetNumEventCounters ())) -i 1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((← (ELUsingAArch32 EL2)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
      else (pure ()))
  else (pure ())
  if ((←((pure ((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1001#4)) && (CRm == 0b1101#4))) <&&> (do
       (pure ((←((pure (opc2 == 0b001#3)) <&&> (do (pure ((_get_PMSELR_Type_SEL (← (PMSELR_read ()))) != 0b11111#5))))) || (opc2 == 0b010#3)))))) : Bool)
  then
    (do
      if ((←((pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (GetNumEventCounters ())) -i 1))) <&&> (do
           (pure ((_get_PMSELR_Type_SEL (← (PMSELR_read ()))) != 0b11111#5))) <||> (do
           (EL2Enabled ()) <&&> (do
             (pure ((← readReg PSTATE).EL == EL0)) <||> (do
               (pure ((← readReg PSTATE).EL == EL1)))) <&&> (do
             (pure ((_get_PMUSERENR_EL0_Type_EN (← readReg PMUSERENR_EL0)) == 1#1))) <&&> (do
             (pure ((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (AArch32_GetNumEventCountersAccessible ())) -i 1))))))) : Bool)
      then
        (do
          if (((BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))) >b ((← (GetNumEventCounters ())) -i 1)) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else
            (do
              if ((← (ELUsingAArch32 EL2)) : Bool)
              then (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8))
              else (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8))))
      else (pure ()))
  else (pure ())
  let temprt ← (( do
    if (((((cp_num == 14) && (opc1 == 0b000#3)) && (opc2 == 0b110#3)) && (CRn == 0b0111#4)) : Bool)
    then
      (do
        let temprt ← (( do
          if ((CRm == 0b1000#4) : Bool)
          then (do (pure (Sail.BitVec.updateSubrange temprt 7 0 ((Sail.BitVec.extractLsb (← (DBGCLAIMCLR_read ())) 7 0) ||| (Sail.BitVec.extractLsb temprt 7 0)))))
          else (pure temprt) ) : SailM (BitVec 32) )
        if ((CRm == 0b1001#4) : Bool)
        then (do (pure (Sail.BitVec.updateSubrange temprt 7 0 ((Sail.BitVec.extractLsb (← (DBGCLAIMCLR_read ())) 7 0) &&& (Complement.complement (Sail.BitVec.extractLsb temprt 7 0))))))
        else (pure temprt))
    else (pure temprt) ) : SailM (BitVec 32) )
  let temprt2 ← (( do (R_read t) ) : SailM (BitVec 32) )
  (R_set t temprt)
  (AArch32_AutoGen_SysRegWrite32 el (integer_subrange cp_num 3 0) opc1 CRn opc2 CRm t)
  (R_set t temprt2)
  if ((((((cp_num == 14) && (opc1 == 0b000#3)) && (opc2 == 0b110#3)) && (CRn == 0b0111#4)) && (CRm == 0b1000#4)) : Bool)
  then (DBGCLAIMCLR_write (Mk_DBGCLAIMCLR_Type (Sail.BitVec.updateSubrange (← (DBGCLAIMCLR_read ())) 7 0 (Sail.BitVec.extractLsb temprt 7 0))))
  else (pure ())
  if ((((((cp_num == 14) && (opc1 == 0b000#3)) && (opc2 == 0b100#3)) && (CRn == 0b0001#4)) && (CRm == 0b0000#4)) : Bool)
  then
    (do
      if (((BitVec.toNat temprt) == (BitVec.toNat 0xC5ACCE55#32)) : Bool)
      then
        (do
          (DBGOSLSR_write (_update_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ())) 1#1))
          writeReg EDPRSR (Sail.BitVec.updateSubrange (← readReg EDPRSR) 5 5 1#1)
          writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange (← readReg OSLSR_EL1) 1 1 1#1))
      else
        (do
          if (((_get_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ()))) == 1#1) : Bool)
          then
            (do
              (DBGOSLSR_write (_update_DBGOSLSR_Type_OSLK (← (DBGOSLSR_read ())) 0#1))
              writeReg EDPRSR (Sail.BitVec.updateSubrange (← readReg EDPRSR) 5 5 0#1)
              writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange (← readReg OSLSR_EL1) 1 1 0#1)
              (CheckOSUnlockCatch ()))
          else (pure ())))
  else (pure ())
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1001#4)) && ((CRm == 0b1100#4) || (CRm == 0b1110#4))) && ((opc2 == 0b001#3) || ((opc2 == 0b010#3) || (opc2 == 0b011#3)))) : Bool)
  then
    (do
      if (((opc2 == 0b011#3) && (CRm == 0b1100#4)) : Bool)
      then (PMOVSSET_write (Mk_PMOVSSET_Type temprt))
      else (pure ())
      if (((opc2 == 0b011#3) && (CRm == 0b1110#4)) : Bool)
      then (PMOVSR_write (Mk_PMOVSR_Type temprt))
      else (pure ())
      if (((opc2 == 0b010#3) && (CRm == 0b1100#4)) : Bool)
      then (PMCNTENSET_write (Mk_PMCNTENSET_Type temprt))
      else (pure ())
      if (((opc2 == 0b001#3) && (CRm == 0b1100#4)) : Bool)
      then (PMCNTENCLR_write (Mk_PMCNTENCLR_Type temprt))
      else (pure ())
      if (((opc2 == 0b010#3) && (CRm == 0b1110#4)) : Bool)
      then (PMINTENSET_write (Mk_PMINTENSET_Type temprt))
      else (pure ())
      if (((opc2 == 0b001#3) && (CRm == 0b1110#4)) : Bool)
      then (PMINTENCLR_write (Mk_PMINTENCLR_Type temprt))
      else (pure ()))
  else (pure ())
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (opc2 == 0b000#3)) && (CRn == 0b1001#4)) && (CRm == 0b1100#4)) : Bool)
  then
    (do
      if (((BitVec.join1 [(BitVec.access temprt 2)]) == 1#1) : Bool)
      then (PMCCNTR_write (Mk_PMCCNTR_Type (Zeros (n := 64))))
      else (pure ())
      if (((BitVec.join1 [(BitVec.access temprt 1)]) == 1#1) : Bool)
      then (AArch32_ClearEventCounters ())
      else (pure ()))
  else (pure ())
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1001#4)) && (CRm == 0b1101#4)) && ((opc2 == 0b001#3) || (opc2 == 0b010#3))) : Bool)
  then
    (do
      let pmselr ← do (pure (BitVec.toNat (_get_PMSELR_Type_SEL (← (PMSELR_read ())))))
      if ((opc2 == 0b001#3) : Bool)
      then
        (do
          if ((pmselr == 31) : Bool)
          then (PMCCFILTR_write (__get_PMCCFILTR (Mk_PMCCFILTR_Type temprt)))
          else (PMEVTYPER_set pmselr (__get_PMEVTYPER (Mk_PMEVTYPER_Type temprt))))
      else (pure ())
      if ((opc2 == 0b010#3) : Bool)
      then
        (do
          sail_assert (pmselr <b 31) "src/sysregs.sail:1330.30-1330.31"
          (PMEVCNTR_set pmselr temprt))
      else (pure ()))
  else (pure ())
  if (((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1110#4)) && ((Sail.BitVec.extractLsb CRm 3 2) == 0b11#2)) : Bool)
  then
    (do
      let index := (BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0)))
      if ((index == 31) : Bool)
      then (PMCCFILTR_write (__get_PMCCFILTR (Mk_PMCCFILTR_Type temprt)))
      else (PMEVTYPER_set index (__get_PMEVTYPER (Mk_PMEVTYPER_Type temprt))))
  else (pure ())
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (opc2 == 0b100#3)) && (CRn == 0b1001#4)) && (CRm == 0b1100#4)) : Bool)
  then (AArch32_PMUSwIncrement temprt)
  else (pure ())
  if (((((((cp_num == 15) && ((opc1 == 0b000#3) || (opc1 == 0b100#3))) && (CRn == 0b1100#4)) && (opc2 == 0b010#3)) && (CRm == 0b0000#4)) && ((BitVec.join1 [(BitVec.access temprt 1)]) == 1#1)) : Bool)
  then (TakeReset false)
  else
    (do
      if ((((((cp_num == 15) && (opc1 == 0b000#3)) && ((opc2 == 0b100#3) || (opc2 == 0b111#3))) && (CRn == 0b0000#4)) && (CRm == 0b0000#4)) : Bool)
      then (MIDR_write (Mk_MIDR_Type temprt))
      else (pure ()))
  if ((((((cp_num == 14) && (opc1 == 0b000#3)) && (CRn == 0b0000#4)) && (opc2 == 0b000#3)) && (CRm == 0b0101#4)) : Bool)
  then
    (do
      (DBGDSCRint_write (_update_DBGDSCRint_Type_TXfull (← (DBGDSCRint_read ())) 1#1))
      writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange (← readReg MDCCSR_EL0) 29 29 1#1)
      (DBGDSCRext_write (_update_DBGDSCRext_Type_TXfull (← (DBGDSCRext_read ())) 1#1))
      (EDSCR_write (_update_EDSCR_Type_TXfull (← (EDSCR_read ())) 1#1)))
  else (pure ())

/-- Type quantifiers: cp_num : Int, t : Int, t2 : Int -/
def AArch32_SysRegWrite64 (cp_num : Int) (instr : (BitVec 32)) (t : Int) (t2 : Int) : SailM Unit := do
  let el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let n ← (( do (undefined_int ()) ) : SailM Int )
  let el ← (( do
    let (_, __tup_1) ← do (ELFromM32 (← readReg PSTATE).M)
    (pure __tup_1) ) : SailM (BitVec 2) )
  let opc1 : (BitVec 4) := (BitVec.slice instr 4 4)
  let CRm : (BitVec 4) := (BitVec.slice instr 0 4)
  if ((((cp_num == 15) && (let b__0 := (Sail.BitVec.extractLsb CRm 3 1)
         if ((((Sail.BitVec.extractLsb b__0 2 2) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 0 0) == (0#1 : (BitVec 1)))) : Bool)
         then true
         else false : Bool)) && ((BitVec.join1 [(BitVec.access opc1 3)]) == 0#1)) : Bool)
  then
    (do
      let n := (BitVec.toNat ((BitVec.join1 [(BitVec.access CRm 0)]) +++ (Sail.BitVec.extractLsb opc1 2 0)))
      if (((Sail.BitVec.extractLsb CRm 3 1) == 0b000#3) : Bool)
      then
        (do
          if ((n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG0NC (← (AMCGCR_read ()))))) : Bool)
          then (sailThrow ((Error_Undefined ())) : SailM Unit)
          else (pure ()))
      else
        (do
          if (((Sail.BitVec.extractLsb CRm 3 1) == 0b010#3) : Bool)
          then
            (do
              if ((n ≥b (BitVec.toNat (_get_AMCGCR_Type_CG1NC (← (AMCGCR_read ()))))) : Bool)
              then (sailThrow ((Error_Undefined ())) : SailM Unit)
              else (pure ()))
          else (pure ())))
  else (pure ())
  (AArch32_AutoGen_SysRegWrite64 el (integer_subrange cp_num 3 0) opc1 CRm t t2)

