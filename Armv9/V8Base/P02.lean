import Armv9.Armv9
import Armv9.Flow
import Armv9.Arith
import Armv9.Vector
import Armv9.ReverseEndianness
import Armv9.Option
import Armv9.MonoRewrites
import Armv9.Common
import Armv9.Prelude
import Armv9.Builtins
import Armv9Core.V8Base

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

def undefined_CLIDR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CLIDR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_CLIDR_EL1_Type_Ctype1 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _update_CLIDR_EL1_Type_Ctype1 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_CLIDR_Type_Ctype1 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _get_CLIDR_Type_Ctype1 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)

def _get_CLIDR_EL1_Type_Ctype2 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 5 3)

def _update_CLIDR_EL1_Type_Ctype2 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 3 x)

def _update_CLIDR_Type_Ctype2 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 3 x)

def _get_CLIDR_Type_Ctype2 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 5 3)

def _get_CLIDR_EL1_Type_Ctype3 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 8 6)

def _update_CLIDR_EL1_Type_Ctype3 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 6 x)

def _update_CLIDR_Type_Ctype3 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 6 x)

def _get_CLIDR_Type_Ctype3 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 8 6)

def _get_CLIDR_EL1_Type_Ctype4 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 11 9)

def _update_CLIDR_EL1_Type_Ctype4 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 9 x)

def _update_CLIDR_Type_Ctype4 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 9 x)

def _get_CLIDR_Type_Ctype4 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 11 9)

def _get_CLIDR_EL1_Type_Ctype5 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 14 12)

def _update_CLIDR_EL1_Type_Ctype5 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 12 x)

def _update_CLIDR_Type_Ctype5 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 12 x)

def _get_CLIDR_Type_Ctype5 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 14 12)

def _get_CLIDR_EL1_Type_Ctype6 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 17 15)

def _update_CLIDR_EL1_Type_Ctype6 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 15 x)

def _update_CLIDR_Type_Ctype6 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 15 x)

def _get_CLIDR_Type_Ctype6 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 17 15)

def _get_CLIDR_EL1_Type_Ctype7 (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 20 18)

def _update_CLIDR_EL1_Type_Ctype7 (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 18 x)

def _update_CLIDR_Type_Ctype7 (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 18 x)

def _get_CLIDR_Type_Ctype7 (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 20 18)

def _get_CLIDR_EL1_Type_ICB (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 32 30)

def _update_CLIDR_EL1_Type_ICB (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 30 x)

def _update_CLIDR_Type_ICB (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 30 x)

def _get_CLIDR_Type_ICB (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)

def _get_CLIDR_EL1_Type_LoC (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 26 24)

def _update_CLIDR_EL1_Type_LoC (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 24 x)

def _update_CLIDR_Type_LoC (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 24 x)

def _get_CLIDR_Type_LoC (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 26 24)

def _get_CLIDR_EL1_Type_LoUIS (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 23 21)

def _update_CLIDR_EL1_Type_LoUIS (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 21 x)

def _update_CLIDR_Type_LoUIS (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 21 x)

def _get_CLIDR_Type_LoUIS (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 23 21)

def _get_CLIDR_EL1_Type_LoUU (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 29 27)

def _update_CLIDR_EL1_Type_LoUU (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 27 x)

def _update_CLIDR_Type_LoUU (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 27 x)

def _get_CLIDR_Type_LoUU (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 29 27)

def _get_CLIDR_EL1_Type_Ttype1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 34 33)

def _update_CLIDR_EL1_Type_Ttype1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 33 x)

def _get_CLIDR_EL1_Type_Ttype2 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 36 35)

def _update_CLIDR_EL1_Type_Ttype2 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 35 x)

def _get_CLIDR_EL1_Type_Ttype3 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 38 37)

def _update_CLIDR_EL1_Type_Ttype3 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 37 x)

def _get_CLIDR_EL1_Type_Ttype4 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 40 39)

def _update_CLIDR_EL1_Type_Ttype4 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 39 x)

def _get_CLIDR_EL1_Type_Ttype5 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 42 41)

def _update_CLIDR_EL1_Type_Ttype5 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 41 x)

def _get_CLIDR_EL1_Type_Ttype6 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 44 43)

def _update_CLIDR_EL1_Type_Ttype6 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 43 x)

def _get_CLIDR_EL1_Type_Ttype7 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 46 45)

def _update_CLIDR_EL1_Type_Ttype7 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 45 x)

/-- Type quantifiers: level : Int -/
def GetCacheInfo (level : Int) (cachetype : CacheType) : SailM (Int × Int × Int) := do
  (pure ((← (undefined_int ())), (← (undefined_int ())), (← (undefined_int ()))))

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def BitReverse (data : (BitVec k_N)) : SailM (BitVec k_N) := do
  let result ← (( do (undefined_bitvector (Sail.BitVec.length data)) ) : SailM (BitVec k_N) )
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length result) -i 1)
  let mut loop_vars := result
  for i in [loop_i_lower:loop_i_upper:1]i do
    let result := loop_vars
    loop_vars := (BitVec.update result (((Sail.BitVec.length result) -i i) -i 1) (Bit (BitVec.join1 [(BitVec.access data i)])))
  (pure loop_vars)

/-- Type quantifiers: k_N : Nat, k_N > 32 -/
def Poly32Mod2 (data_in : (BitVec k_N)) (poly : (BitVec 32)) : SailM (BitVec 32) := do
  sail_assert ((Sail.BitVec.length data_in) >b 32) "src/v8_base.sail:12544.18-12544.19"
  let data : (BitVec k_N) := data_in
  let data ← (( do
    let loop_i_lower := 32
    let loop_i_upper := ((Sail.BitVec.length data_in) -i 1)
    let mut loop_vars := data
    for i in [loop_i_upper:loop_i_lower:-1]i do
      let data := loop_vars
      loop_vars :=
        if (((BitVec.join1 [(BitVec.access data i)]) == 1#1) : Bool)
        then (Sail.BitVec.updateSubrange data (i -i 1) 0 ((Sail.BitVec.extractLsb data (i -i 1) 0) ^^^ (poly +++ (Zeros (n := (i -i 32))))))
        else data
    (pure loop_vars) ) : SailM (BitVec k_N) )
  (pure (Sail.BitVec.extractLsb data 31 0))

/-- Type quantifiers: k_N : Nat, shift : Int, k_N ≥ 0 -/
def ROL (x : (BitVec k_N)) (shift : Int) : SailM (BitVec k_N) := do
  sail_assert ((shift ≥b 0) && (shift ≤b (Sail.BitVec.length x))) "src/v8_base.sail:12606.35-12606.36"
  if ((shift == 0) : Bool)
  then (pure x)
  else (pure (ROR x ((Sail.BitVec.length x) -i shift)))

def AESShiftRows (op : (BitVec 128)) : (BitVec 128) :=
  ((((((((((((((((Sail.BitVec.extractLsb op 95 88) +++ (Sail.BitVec.extractLsb op 55 48)) +++ (Sail.BitVec.extractLsb op 15 8)) +++ (Sail.BitVec.extractLsb op 103 96)) +++ (Sail.BitVec.extractLsb op 63 56)) +++ (Sail.BitVec.extractLsb op 23 16)) +++ (Sail.BitVec.extractLsb op 111 104)) +++ (Sail.BitVec.extractLsb op 71 64)) +++ (Sail.BitVec.extractLsb op 31 24)) +++ (Sail.BitVec.extractLsb op 119 112)) +++ (Sail.BitVec.extractLsb op 79 72)) +++ (Sail.BitVec.extractLsb op 39 32)) +++ (Sail.BitVec.extractLsb op 127 120)) +++ (Sail.BitVec.extractLsb op 87 80)) +++ (Sail.BitVec.extractLsb op 47 40)) +++ (Sail.BitVec.extractLsb op 7 0))

def AESInvShiftRows (op : (BitVec 128)) : (BitVec 128) :=
  ((((((((((((((((Sail.BitVec.extractLsb op 31 24) +++ (Sail.BitVec.extractLsb op 55 48)) +++ (Sail.BitVec.extractLsb op 79 72)) +++ (Sail.BitVec.extractLsb op 103 96)) +++ (Sail.BitVec.extractLsb op 127 120)) +++ (Sail.BitVec.extractLsb op 23 16)) +++ (Sail.BitVec.extractLsb op 47 40)) +++ (Sail.BitVec.extractLsb op 71 64)) +++ (Sail.BitVec.extractLsb op 95 88)) +++ (Sail.BitVec.extractLsb op 119 112)) +++ (Sail.BitVec.extractLsb op 15 8)) +++ (Sail.BitVec.extractLsb op 39 32)) +++ (Sail.BitVec.extractLsb op 63 56)) +++ (Sail.BitVec.extractLsb op 87 80)) +++ (Sail.BitVec.extractLsb op 111 104)) +++ (Sail.BitVec.extractLsb op 7 0))

def AESSubBytes (op : (BitVec 128)) : SailM (BitVec 128) := do
  let GF2 : (BitVec 2048) := (((((((((((((((0x16BB54B00F2D99416842E6BF0D89A18C#128 +++ 0xDF2855CEE9871E9B948ED9691198F8E1#128) +++ 0x9E1DC186B95735610EF6034866B53E70#128) +++ 0x8A8BBD4B1F74DDE8C6B4A61C2E2578BA#128) +++ 0x08AE7A65EAF4566CA94ED58D6D37C8E7#128) +++ 0x79E4959162ACD3C25C2406490A3A32E0#128) +++ 0xDB0B5EDE14B8EE4688902A22DC4F8160#128) +++ 0x73195D643D7EA7C41744975FEC130CCD#128) +++ 0xD2F3FF1021DAB6BCF5389D928F40A351#128) +++ 0xA89F3C507F02F94585334D43FBAAEFD0#128) +++ 0xCF584C4A39BECB6A5BB1FC20ED00D153#128) +++ 0x842FE329B3D63B52A05A6E1B1A2C8309#128) +++ 0x75B227EBE28012079A059618C323C704#128) +++ 0x1531D871F1E5A534CCF73F362693FDB7#128) +++ 0xC072A49CAFA2D4ADF04759FA7DC982CA#128) +++ 0x76ABD7FE2B670130C56F6BF27B777C63#128)
  let out ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let loop_i_lower := 0
  let loop_i_upper := 15
  let mut loop_vars := out
  for i in [loop_i_lower:loop_i_upper:1]i do
    let out := loop_vars
    loop_vars := (set_slice 8 out (i *i 8) (BitVec.slice GF2 ((BitVec.toNat (BitVec.slice op (i *i 8) 8)) *i 8) 8))
  (pure loop_vars)

def AESInvSubBytes (op : (BitVec 128)) : SailM (BitVec 128) := do
  let GF2_inv : (BitVec 2048) := (((((((((((((((0x7D0C2155631469E126D677BA7E042B17#128 +++ 0x619953833CBBEBC8B0F52AAE4D3BE0A0#128) +++ 0xEF9CC9939F7AE52D0D4AB519A97F5160#128) +++ 0x5FEC8027591012B131C7078833A8DD1F#128) +++ 0xF45ACD78FEC0DB9A2079D2C64B3E56FC#128) +++ 0x1BBE18AA0E62B76F89C5291D711AF147#128) +++ 0x6EDF751CE837F9E28535ADE72274AC96#128) +++ 0x73E6B4F0CECFF297EADC674F4111913A#128) +++ 0x6B8A130103BDAFC1020F3FCA8F1E2CD0#128) +++ 0x0645B3B80558E4F70AD3BC8C00ABD890#128) +++ 0x849D8DA75746155EDAB9EDFD5048706C#128) +++ 0x92B6655DCC5CA4D41698688664F6F872#128) +++ 0x25D18B6D49A25B76B224D92866A12E08#128) +++ 0x4EC3FA420B954CEE3D23C2A632947B54#128) +++ 0xCBE9DEC444438E3487FF2F9B8239E37C#128) +++ 0xFBD7F3819EA340BF38A53630D56A0952#128)
  let out ← (( do (undefined_bitvector 128) ) : SailM (BitVec 128) )
  let loop_i_lower := 0
  let loop_i_upper := 15
  let mut loop_vars := out
  for i in [loop_i_lower:loop_i_upper:1]i do
    let out := loop_vars
    loop_vars := (set_slice 8 out (i *i 8) (BitVec.slice GF2_inv ((BitVec.toNat (BitVec.slice op (i *i 8) 8)) *i 8) 8))
  (pure loop_vars)

def FFmul02 (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_02 : (BitVec 2048) := (((((((((((((((0xE5E7E1E3EDEFE9EBF5F7F1F3FDFFF9FB#128 +++ 0xC5C7C1C3CDCFC9CBD5D7D1D3DDDFD9DB#128) +++ 0xA5A7A1A3ADAFA9ABB5B7B1B3BDBFB9BB#128) +++ 0x858781838D8F898B959791939D9F999B#128) +++ 0x656761636D6F696B757771737D7F797B#128) +++ 0x454741434D4F494B555751535D5F595B#128) +++ 0x252721232D2F292B353731333D3F393B#128) +++ 0x050701030D0F090B151711131D1F191B#128) +++ 0xFEFCFAF8F6F4F2F0EEECEAE8E6E4E2E0#128) +++ 0xDEDCDAD8D6D4D2D0CECCCAC8C6C4C2C0#128) +++ 0xBEBCBAB8B6B4B2B0AEACAAA8A6A4A2A0#128) +++ 0x9E9C9A98969492908E8C8A8886848280#128) +++ 0x7E7C7A78767472706E6C6A6866646260#128) +++ 0x5E5C5A58565452504E4C4A4846444240#128) +++ 0x3E3C3A38363432302E2C2A2826242220#128) +++ 0x1E1C1A18161412100E0C0A0806040200#128)
  (BitVec.slice FFmul_02 ((BitVec.toNat b) *i 8) 8)

def FFmul03 (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_03 : (BitVec 2048) := (((((((((((((((0x1A191C1F16151013020104070E0D080B#128 +++ 0x2A292C2F26252023323134373E3D383B#128) +++ 0x7A797C7F76757073626164676E6D686B#128) +++ 0x4A494C4F46454043525154575E5D585B#128) +++ 0xDAD9DCDFD6D5D0D3C2C1C4C7CECDC8CB#128) +++ 0xEAE9ECEFE6E5E0E3F2F1F4F7FEFDF8FB#128) +++ 0xBAB9BCBFB6B5B0B3A2A1A4A7AEADA8AB#128) +++ 0x8A898C8F86858083929194979E9D989B#128) +++ 0x818287848D8E8B88999A9F9C95969390#128) +++ 0xB1B2B7B4BDBEBBB8A9AAAFACA5A6A3A0#128) +++ 0xE1E2E7E4EDEEEBE8F9FAFFFCF5F6F3F0#128) +++ 0xD1D2D7D4DDDEDBD8C9CACFCCC5C6C3C0#128) +++ 0x414247444D4E4B48595A5F5C55565350#128) +++ 0x717277747D7E7B78696A6F6C65666360#128) +++ 0x212227242D2E2B28393A3F3C35363330#128) +++ 0x111217141D1E1B18090A0F0C05060300#128)
  (BitVec.slice FFmul_03 ((BitVec.toNat b) *i 8) 8)

def FFmul09 (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_09 : (BitVec 2048) := (((((((((((((((0x464F545D626B70790E071C152A233831#128 +++ 0xD6DFC4CDF2FBE0E99E978C85BAB3A8A1#128) +++ 0x7D746F6659504B42353C272E1118030A#128) +++ 0xEDE4FFF6C9C0DBD2A5ACB7BE8188939A#128) +++ 0x3039222B141D060F78716A635C554E47#128) +++ 0xA0A9B2BB848D969FE8E1FAF3CCC5DED7#128) +++ 0x0B0219102F263D34434A5158676E757C#128) +++ 0x9B928980BFB6ADA4D3DAC1C8F7FEE5EC#128) +++ 0xAAA3B8B18E879C95E2EBF0F9C6CFD4DD#128) +++ 0x3A3328211E170C05727B6069565F444D#128) +++ 0x9198838AB5BCA7AED9D0CBC2FDF4EFE6#128) +++ 0x0108131A252C373E49405B526D647F76#128) +++ 0xDCD5CEC7F8F1EAE3949D868FB0B9A2AB#128) +++ 0x4C455E5768617A73040D161F2029323B#128) +++ 0xE7EEF5FCC3CAD1D8AFA6BDB48B829990#128) +++ 0x777E656C535A41483F362D241B120900#128)
  (BitVec.slice FFmul_09 ((BitVec.toNat b) *i 8) 8)

def FFmul0B (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_0B : (BitVec 2048) := (((((((((((((((0xA3A8B5BE8F849992FBF0EDE6D7DCC1CA#128 +++ 0x1318050E3F3429224B405D56676C717A#128) +++ 0xD8D3CEC5F4FFE2E9808B969DACA7BAB1#128) +++ 0x68637E75444F5259303B262D1C170A01#128) +++ 0x555E434879726F640D061B10212A373C#128) +++ 0xE5EEF3F8C9C2DFD4BDB6ABA0919A878C#128) +++ 0x2E2538330209141F767D606B5A514C47#128) +++ 0x9E958883B2B9A4AFC6CDD0DBEAE1FCF7#128) +++ 0x545F424978736E650C071A11202B363D#128) +++ 0xE4EFF2F9C8C3DED5BCB7AAA1909B868D#128) +++ 0x2F2439320308151E777C616A5B504D46#128) +++ 0x9F948982B3B8A5AEC7CCD1DAEBE0FDF6#128) +++ 0xA2A9B4BF8E859893FAF1ECE7D6DDC0CB#128) +++ 0x1219040F3E3528234A415C57666D707B#128) +++ 0xD9D2CFC4F5FEE3E8818A979CADA6BBB0#128) +++ 0x69627F74454E5358313A272C1D160B00#128)
  (BitVec.slice FFmul_0B ((BitVec.toNat b) *i 8) 8)

def FFmul0D (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_0D : (BitVec 2048) := (((((((((((((((0x979A8D80A3AEB9B4FFF2E5E8CBC6D1DC#128 +++ 0x474A5D50737E69642F2235381B16010C#128) +++ 0x2C21363B1815020F44495E53707D6A67#128) +++ 0xFCF1E6EBC8C5D2DF94998E83A0ADBAB7#128) +++ 0xFAF7E0EDCEC3D4D9929F8885A6ABBCB1#128) +++ 0x2A27303D1E130409424F5855767B6C61#128) +++ 0x414C5B5675786F622924333E1D10070A#128) +++ 0x919C8B86A5A8BFB2F9F4E3EECDC0D7DA#128) +++ 0x4D40575A7974636E25283F32111C0B06#128) +++ 0x9D90878AA9A4B3BEF5F8EFE2C1CCDBD6#128) +++ 0xF6FBECE1C2CFD8D59E938489AAA7B0BD#128) +++ 0x262B3C31121F08054E4354597A77606D#128) +++ 0x202D3A3714190E034845525F7C71666B#128) +++ 0xF0FDEAE7C4C9DED39895828FACA1B6BB#128) +++ 0x9B96818CAFA2B5B8F3FEE9E4C7CADDD0#128) +++ 0x4B46515C7F726568232E3934171A0D00#128)
  (BitVec.slice FFmul_0D ((BitVec.toNat b) *i 8) 8)

def FFmul0E (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_0E : (BitVec 2048) := (((((((((((((((0x8D83919FB5BBA9A7FDF3E1EFC5CBD9D7#128 +++ 0x6D63717F555B49471D13010F252B3937#128) +++ 0x56584A446E60727C26283A341E10020C#128) +++ 0xB6B8AAA48E80929CC6C8DAD4FEF0E2EC#128) +++ 0x202E3C321816040A505E4C426866747A#128) +++ 0xC0CEDCD2F8F6E4EAB0BEACA28886949A#128) +++ 0xFBF5E7E9C3CDDFD18B859799B3BDAFA1#128) +++ 0x1B150709232D3F316B657779535D4F41#128) +++ 0xCCC2D0DEF4FAE8E6BCB2A0AE848A9896#128) +++ 0x2C22303E141A08065C52404E646A7876#128) +++ 0x17190B052F21333D67697B755F51434D#128) +++ 0xF7F9EBE5CFC1D3DD87899B95BFB1A3AD#128) +++ 0x616F7D735957454B111F0D032927353B#128) +++ 0x818F9D93B9B7A5ABF1FFEDE3C9C7D5DB#128) +++ 0xBAB4A6A8828C9E90CAC4D6D8F2FCEEE0#128) +++ 0x5A544648626C7E702A243638121C0E00#128)
  (BitVec.slice FFmul_0E ((BitVec.toNat b) *i 8) 8)

def SHAchoose (x : (BitVec 32)) (y : (BitVec 32)) (z : (BitVec 32)) : (BitVec 32) :=
  (((y ^^^ z) &&& x) ^^^ z)

def SHAparity (x : (BitVec 32)) (y : (BitVec 32)) (z : (BitVec 32)) : (BitVec 32) :=
  ((x ^^^ y) ^^^ z)

def SHAmajority (x : (BitVec 32)) (y : (BitVec 32)) (z : (BitVec 32)) : (BitVec 32) :=
  ((x &&& y) ||| ((x ||| y) &&& z))

def SHAhashSIGMA0 (x : (BitVec 32)) : (BitVec 32) :=
  (((ROR x 2) ^^^ (ROR x 13)) ^^^ (ROR x 22))

def SHAhashSIGMA1 (x : (BitVec 32)) : (BitVec 32) :=
  (((ROR x 6) ^^^ (ROR x 11)) ^^^ (ROR x 25))

def Sbox (sboxin : (BitVec 8)) : (BitVec 8) :=
  let sboxstring : (BitVec 2048) := 0xD690E9FECCE13DB716B614C228FB2C052B679A762ABE04C3AA441326498606999C4250F491EF987A33540B43EDCFAC62E4B31CA9C908E89580DF94FA758F3FA64707A7FCF37317BA83593C19E6854FA8686B81B27164DA8BF8EB0F4B70569D351E240E5E6358D1A225227C3B01217887D40046579FD327524C3602E7A0C4C89EEABF8AD240C738B5A3F7F2CEF96115A1E0AE5DA49B341A55AD933230F58CB1E31DF6E22E8266CA60C02923AB0D534E6FD5DB3745DEFD8E2F03FF6A726D6C5B518D1BAF92BBDDBC7F11D95C411F105AD80AC13188A5CD7BBD2D74D012B8E5B4B08969974A0C96777E65B9F109C56EC68418F07DEC3ADC4D2079EE5F3ED7CB3948#2048
  let sboxin := (BitVec.toNat sboxin)
  (Sail.BitVec.extractLsb sboxstring (((255 -i sboxin) *i 8) +i 7) ((255 -i sboxin) *i 8))

def TargetSecurityState (NS : (BitVec 1)) (NSE : (BitVec 1)) : SailM SecurityState := do
  let curr_ss ← (( do (SecurityStateAtEL (← readReg PSTATE).EL) ) : SailM SecurityState )
  if ((BEq.beq curr_ss SS_NonSecure) : Bool)
  then (pure SS_NonSecure)
  else
    (do
      if ((BEq.beq curr_ss SS_Secure) : Bool)
      then
        (do
          match (NS : BitVec 1) with
          | 0 => (pure SS_Secure)
          | 1 => (pure SS_NonSecure)
          | _ => (do (undefined_SecurityState ())))
      else
        (do
          if ((← (HaveRME ())) : Bool)
          then
            (do
              if ((BEq.beq curr_ss SS_Root) : Bool)
              then
                (do
                  match ((NSE +++ NS) : BitVec 2) with
                  | 0b00 => (pure SS_Secure)
                  | 0b01 => (pure SS_NonSecure)
                  | 0b11 => (pure SS_Realm)
                  | 0b10 => (pure SS_Root)
                  | _ => (do (undefined_SecurityState ())))
              else
                (do
                  if ((BEq.beq curr_ss SS_Realm) : Bool)
                  then (pure SS_Realm)
                  else (do (undefined_SecurityState ()))))
          else (do (undefined_SecurityState ()))))

def RESTRICT_PREDICTIONS (c : ExecutionCntxt) : Unit :=
  ()

def undefined_CONTEXTIDR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CONTEXTIDR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_CONTEXTIDR_EL1_Type_PROCID (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_CONTEXTIDR_EL1_Type_PROCID (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_CONTEXTIDR_EL2_Type_PROCID (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _get_CONTEXTIDR_EL2_Type_PROCID (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def Mk_TTBCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _update_TTBCR_Type_EAE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_TTBCR_Type_PD0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_TTBCR_Type_PD1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_TTBCR_Type_T2E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def EAEisOne (_ : Unit) : SailM Bool := do
  (pure ((_get_TTBCR_Type_EAE (← (TTBCR_read ()))) == 1#1))

def Mk_CONTEXTIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _update_CONTEXTIDR_Type_ASID (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_TTBR0_EL1_Type_ASID (v : (BitVec 128)) (x : (BitVec 16)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 63 48 x)

def _update_TTBR0_EL2_Type_ASID (v : (BitVec 128)) (x : (BitVec 16)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 63 48 x)

def _update_TTBR0_Type_ASID (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _update_TTBR1_EL1_Type_ASID (v : (BitVec 128)) (x : (BitVec 16)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 63 48 x)

def _update_TTBR1_EL2_Type_ASID (v : (BitVec 128)) (x : (BitVec 16)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 63 48 x)

def _update_TTBR1_Type_ASID (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def Mk_TTBR0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_TTBR0_Type_BADDR (v : (BitVec 64)) : (BitVec 47) :=
  (Sail.BitVec.extractLsb v 47 1)

def _update_TTBR0_Type_BADDR (v : (BitVec 64)) (x : (BitVec 47)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 1 x)

def _update_GPTBR_EL3_Type_BADDR (v : (BitVec 64)) (x : (BitVec 40)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 0 x)

def _update_HTTBR_Type_BADDR (v : (BitVec 64)) (x : (BitVec 47)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 1 x)

def _update_TTBR1_Type_BADDR (v : (BitVec 64)) (x : (BitVec 47)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 1 x)

def _update_VNCR_EL2_Type_BADDR (v : (BitVec 64)) (x : (BitVec 45)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 12 x)

def _update_VTTBR_Type_BADDR (v : (BitVec 64)) (x : (BitVec 47)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 1 x)

def _get_HTTBR_Type_BADDR (v : (BitVec 64)) : (BitVec 47) :=
  (Sail.BitVec.extractLsb v 47 1)

def _get_TTBR1_Type_BADDR (v : (BitVec 64)) : (BitVec 47) :=
  (Sail.BitVec.extractLsb v 47 1)

def _get_VNCR_EL2_Type_BADDR (v : (BitVec 64)) : (BitVec 45) :=
  (Sail.BitVec.extractLsb v 56 12)

def _get_VTTBR_Type_BADDR (v : (BitVec 64)) : (BitVec 47) :=
  (Sail.BitVec.extractLsb v 47 1)

def _update_TTBR0_Type_CnP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_HTTBR_Type_CnP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ID_AA64MMFR2_EL1_Type_CnP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_MMFR4_EL1_Type_CnP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_MMFR4_Type_CnP (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_TTBR0_EL1_Type_CnP (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_TTBR0_EL2_Type_CnP (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_TTBR0_EL3_Type_CnP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_TTBR1_EL1_Type_CnP (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_TTBR1_EL2_Type_CnP (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_TTBR1_Type_CnP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_VSTTBR_EL2_Type_CnP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_VTTBR_EL2_Type_CnP (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_VTTBR_Type_CnP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_ID_AA64MMFR2_EL1_Type_CnP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_MMFR4_EL1_Type_CnP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_MMFR4_Type_CnP (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_TTBR0_Type_IRGN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 0 0 (Sail.BitVec.extractLsb x (2 -i 1) (((2 -i 1) -i ((0 -i 0) +i 1)) +i 1))) 6 6 (Sail.BitVec.extractLsb x ((2 -i 1) -i ((0 -i 0) +i 1)) ((((2 -i 1) -i ((0 -i 0) +i 1)) -i ((6 -i 6) +i 1)) +i 1)))

def _update_GPCCR_EL3_Type_IRGN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def _update_TTBR1_Type_IRGN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 6 6 (Sail.BitVec.extractLsb x (2 -i 1) (((2 -i 1) -i ((6 -i 6) +i 1)) +i 1))) 0 0 (Sail.BitVec.extractLsb x ((2 -i 1) -i ((6 -i 6) +i 1)) ((((2 -i 1) -i ((6 -i 6) +i 1)) -i ((0 -i 0) +i 1)) +i 1)))

def _update_TTBR0_Type_NOS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PAR_Type_NOS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_TTBR1_Type_NOS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_PAR_Type_NOS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_TTBR0_Type_RGN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 3 x)

def _update_TTBR1_Type_RGN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 3 x)

def _update_TTBR0_Type_TTB0 (v : (BitVec 64)) (x : (BitVec 25)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 7 x)

def undefined_TTBR0_EL1_Type (_ : Unit) : SailM (BitVec 128) := do
  (undefined_bitvector 128)

def Mk_TTBR0_EL1_Type (v : (BitVec 128)) : (BitVec 128) :=
  v

def _update_TTBR0_EL1_Type_SKL (v : (BitVec 128)) (x : (BitVec 2)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 2 1 x)

def _update_TTBR0_EL2_Type_SKL (v : (BitVec 128)) (x : (BitVec 2)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 2 1 x)

def _update_TTBR0_EL3_Type_SKL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 1 x)

def _update_TTBR1_EL1_Type_SKL (v : (BitVec 128)) (x : (BitVec 2)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 2 1 x)

def _update_TTBR1_EL2_Type_SKL (v : (BitVec 128)) (x : (BitVec 2)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 2 1 x)

def _update_VSTTBR_EL2_Type_SKL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 1 x)

def _update_VTTBR_EL2_Type_SKL (v : (BitVec 128)) (x : (BitVec 2)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 2 1 x)

def undefined_HTTBR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_HTTBR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_TTBR0_EL2_Type (_ : Unit) : SailM (BitVec 128) := do
  (undefined_bitvector 128)

def Mk_TTBR0_EL2_Type (v : (BitVec 128)) : (BitVec 128) :=
  v

def Mk_TTBR1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_TTBR1_Type_TTB1 (v : (BitVec 64)) (x : (BitVec 25)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 7 x)

def undefined_TTBR1_EL1_Type (_ : Unit) : SailM (BitVec 128) := do
  (undefined_bitvector 128)

def Mk_TTBR1_EL1_Type (v : (BitVec 128)) : (BitVec 128) :=
  v

def undefined_TTBR1_EL2_Type (_ : Unit) : SailM (BitVec 128) := do
  (undefined_bitvector 128)

def Mk_TTBR1_EL2_Type (v : (BitVec 128)) : (BitVec 128) :=
  v

def ASID_read (_ : Unit) : SailM (BitVec 16) := do
  if ((←((EL2Enabled ()) <&&> (do
       (pure (! (← (ELUsingAArch32 EL2))))) <&&> (do
       (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))) : Bool)
  then
    (do
      if (((_get_TCR_EL2_Type_A1 (← readReg TCR_EL2)) == 1#1) : Bool)
      then (pure (_get_TTBR1_EL2_Type_ASID (← readReg TTBR1_EL2)))
      else (pure (_get_TTBR0_EL2_Type_ASID (← (TTBR0_EL2_read ())))))
  else
    (do
      if ((! (← (ELUsingAArch32 EL1))) : Bool)
      then
        (do
          if (((_get_TCR_EL1_Type_A1 (← readReg TCR_EL1)) == 1#1) : Bool)
          then (pure (_get_TTBR1_EL1_Type_ASID (← (TTBR1_EL1_read ()))))
          else (pure (_get_TTBR0_EL1_Type_ASID (← (TTBR0_EL1_read ())))))
      else
        (do
          if (((_get_TTBCR_Type_EAE (← (TTBCR_read ()))) == 0#1) : Bool)
          then (pure (Sail.BitVec.zeroExtend (_get_CONTEXTIDR_Type_ASID (← (CONTEXTIDR_read ()))) 16))
          else
            (do
              if (((_get_TTBCR_Type_A1 (← (TTBCR_read ()))) == 1#1) : Bool)
              then (pure (Sail.BitVec.zeroExtend (_get_TTBR1_Type_ASID (← (TTBR1_read ()))) 16))
              else (pure (Sail.BitVec.zeroExtend (_get_TTBR0_Type_ASID (← (TTBR0_read ()))) 16)))))

/-- Type quantifiers: a_in : Int, k_increasedprecision_name : Bool -/
def RecipEstimate (a_in : Int) (increasedprecision_name : Bool) : SailM Int := do
  let a : Int := a_in
  let r ← (( do (undefined_int ()) ) : SailM Int )
  let r ← (( do
    if ((! increasedprecision_name) : Bool)
    then
      (do
        sail_assert ((256 ≤b a) && (a <b 512)) "src/v8_base.sail:13058.33-13058.34"
        let a := ((a *i 2) +i 1)
        let b := (fdiv_int (2 ^i 19) a)
        let r : Int := (fdiv_int (b +i 1) 2)
        sail_assert ((256 ≤b r) && (r <b 512)) "src/v8_base.sail:13062.33-13062.34"
        (pure r))
    else
      (do
        sail_assert ((2048 ≤b a) && (a <b 4096)) "src/v8_base.sail:13064.35-13064.36"
        let a := ((a *i 2) +i 1)
        let real_val : real := (div_real (to_real (2 ^i 25)) (to_real a))
        let r : Int := (round_down real_val)
        let error : real := (sub_real real_val (to_real r))
        let round_up : Bool := (gt_real error (1/2))
        let r : Int :=
          if (round_up : Bool)
          then (r +i 1)
          else r
        sail_assert ((4096 ≤b r) && (r <b 8192)) "src/v8_base.sail:13073.35-13073.36"
        (pure r)) ) : SailM Int )
  let r := r
  (pure r)

/-- Type quantifiers: a_in : Int, k_increasedprecision_name : Bool -/
def RecipSqrtEstimate (a_in : Int) (increasedprecision_name : Bool) : SailM Int := do
  let round_up ← (( do (undefined_bool ()) ) : SailM Bool )
  let a : Int := a_in
  let r ← (( do (undefined_int ()) ) : SailM Int )
  let r ← (( do
    if ((! increasedprecision_name) : Bool)
    then
      (do
        sail_assert ((128 ≤b a) && (a <b 512)) "src/v8_base.sail:13104.33-13104.34"
        let a : Int :=
          if ((a <b 256) : Bool)
          then ((a *i 2) +i 1)
          else
            (let a : Int := (Int.shiftl (Int.shiftr a 1) 1)
            ((a +i 1) *i 2))
        let a := a
        let b : Int := 512
        let b ← (( do
          let mut loop_vars := b
          while (λ b => (((a *i (b +i 1)) *i (b +i 1)) <b (2 ^i 28))) loop_vars do
            let b := loop_vars
            loop_vars := ((b +i 1) : Int)
          (pure loop_vars) ) : SailM Int )
        let b := b
        let r : Int := (fdiv_int (b +i 1) 2)
        sail_assert ((256 ≤b r) && (r <b 512)) "src/v8_base.sail:13118.33-13118.34"
        (pure r))
    else
      (do
        sail_assert ((1024 ≤b a) && (a <b 4096)) "src/v8_base.sail:13120.35-13120.36"
        let real_val ← (( do (undefined_real ()) ) : SailM real )
        let real_val : real :=
          if ((a <b 2048) : Bool)
          then
            (let a := ((a *i 2) +i 1)
            (div_real (to_real a) (2)))
          else
            (let a : Int := (Int.shiftl (Int.shiftr a 1) 1)
            let a := (a +i 1)
            (to_real a))
        let real_val : real := (sqrt_real real_val)
        let real_val : real := (mult_real real_val (to_real (2 ^i 47)))
        let int_val : Int := (round_down real_val)
        let error : real := (sub_real real_val (to_real int_val))
        let round_up : Bool := (gt_real error (1/2))
        let int_val : Int :=
          if (round_up : Bool)
          then (int_val +i 1)
          else int_val
        let real_val : real := (div_real (to_real (2 ^i 65)) (to_real int_val))
        let int_val : Int := (round_down real_val)
        let error : real := (sub_real real_val (to_real int_val))
        let round_up : Bool := ((gt_real error (1/2)) || ((eq_real error (1/2)) && ((BitVec.join1 [(integer_access int_val 0)]) == 1#1)))
        let int_val : Int :=
          if (round_up : Bool)
          then (int_val +i 1)
          else int_val
        let int_val := int_val
        let r : Int := int_val
        sail_assert ((4096 ≤b r) && (r <b 8192)) "src/v8_base.sail:13147.35-13147.36"
        (pure r)) ) : SailM Int )
  let r := r
  (pure r)

/-- Type quantifiers: N : Nat, i : Int, 0 ≤ (N - 1) -/
def SignedSatQ (i : Int) (N : Nat) : SailM ((BitVec N) × Bool) := do
  let result ← (( do (undefined_int ()) ) : SailM Int )
  let saturated ← (( do (undefined_bool ()) ) : SailM Bool )
  let (result, saturated) : (Int × Bool) :=
    if ((i >b ((2 ^i (N -i 1)) -i 1)) : Bool)
    then
      (let result : Int := ((2 ^i (N -i 1)) -i 1)
      let saturated : Bool := true
      (result, saturated))
    else
      (let (result, saturated) : (Int × Bool) :=
        if ((i <b (Neg.neg (2 ^i (N -i 1)))) : Bool)
        then
          (let result : Int := (Neg.neg (2 ^i (N -i 1)))
          let saturated : Bool := true
          (result, saturated))
        else
          (let result : Int := i
          let saturated : Bool := false
          (result, saturated))
      (result, saturated))
  let result := result
  (pure ((integer_subrange result (N -i 1) 0), saturated))

/-- Type quantifiers: N : Nat, i : Int, 0 ≤ (N - 1) -/
def UnsignedSatQ (i : Int) (N : Nat) : SailM ((BitVec N) × Bool) := do
  let result ← (( do (undefined_int ()) ) : SailM Int )
  let saturated ← (( do (undefined_bool ()) ) : SailM Bool )
  let (result, saturated) : (Int × Bool) :=
    if ((i >b ((2 ^i N) -i 1)) : Bool)
    then
      (let result : Int := ((2 ^i N) -i 1)
      let saturated : Bool := true
      (result, saturated))
    else
      (let (result, saturated) : (Int × Bool) :=
        if ((i <b 0) : Bool)
        then
          (let result : Int := 0
          let saturated : Bool := true
          (result, saturated))
        else
          (let result : Int := i
          let saturated : Bool := false
          (result, saturated))
      (result, saturated))
  let result := result
  (pure ((integer_subrange result (N -i 1) 0), saturated))

def AdvSIMDExpandImm (op : (BitVec 1)) (cmode : (BitVec 4)) (imm8 : (BitVec 8)) : SailM (BitVec 64) := do
  let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let imm8a ← (( do (undefined_bitvector 8) ) : SailM (BitVec 8) )
  let imm8b ← (( do (undefined_bitvector 8) ) : SailM (BitVec 8) )
  let imm8c ← (( do (undefined_bitvector 8) ) : SailM (BitVec 8) )
  let imm8d ← (( do (undefined_bitvector 8) ) : SailM (BitVec 8) )
  let imm8e ← (( do (undefined_bitvector 8) ) : SailM (BitVec 8) )
  let imm8f ← (( do (undefined_bitvector 8) ) : SailM (BitVec 8) )
  let imm8g ← (( do (undefined_bitvector 8) ) : SailM (BitVec 8) )
  let imm8h ← (( do (undefined_bitvector 8) ) : SailM (BitVec 8) )
  let imm64 ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  match ((Sail.BitVec.extractLsb cmode 3 1) : BitVec 3) with
  | 0b000 => (pure (BitVec.replicateBits ((Zeros (n := 24)) +++ imm8) 2))
  | 0b001 => (pure (BitVec.replicateBits (((Zeros (n := 16)) +++ imm8) +++ (Zeros (n := 8))) 2))
  | 0b010 => (pure (BitVec.replicateBits (((Zeros (n := 8)) +++ imm8) +++ (Zeros (n := 16))) 2))
  | 0b011 => (pure (BitVec.replicateBits (imm8 +++ (Zeros (n := 24))) 2))
  | 0b100 => (pure (BitVec.replicateBits ((Zeros (n := 8)) +++ imm8) 4))
  | 0b101 => (pure (BitVec.replicateBits (imm8 +++ (Zeros (n := 8))) 4))
  | 0b110 =>
    (if (((BitVec.join1 [(BitVec.access cmode 0)]) == 0#1) : Bool)
    then (pure (BitVec.replicateBits (((Zeros (n := 16)) +++ imm8) +++ (Ones (n := 8))) 2))
    else (pure (BitVec.replicateBits (((Zeros (n := 8)) +++ imm8) +++ (Ones (n := 16))) 2)))
  | _ =>
    (do
      let imm64 : (BitVec 64) :=
        if ((((BitVec.join1 [(BitVec.access cmode 0)]) == 0#1) && (op == 0#1)) : Bool)
        then (BitVec.replicateBits imm8 8)
        else imm64
      let imm64 : (BitVec 64) :=
        if ((((BitVec.join1 [(BitVec.access cmode 0)]) == 0#1) && (op == 1#1)) : Bool)
        then
          (let imm8a : (BitVec 8) := (BitVec.replicateBits (BitVec.join1 [(BitVec.access imm8 7)]) 8)
          let imm8b : (BitVec 8) := (BitVec.replicateBits (BitVec.join1 [(BitVec.access imm8 6)]) 8)
          let imm8c : (BitVec 8) := (BitVec.replicateBits (BitVec.join1 [(BitVec.access imm8 5)]) 8)
          let imm8d : (BitVec 8) := (BitVec.replicateBits (BitVec.join1 [(BitVec.access imm8 4)]) 8)
          let imm8e : (BitVec 8) := (BitVec.replicateBits (BitVec.join1 [(BitVec.access imm8 3)]) 8)
          let imm8f : (BitVec 8) := (BitVec.replicateBits (BitVec.join1 [(BitVec.access imm8 2)]) 8)
          let imm8g : (BitVec 8) := (BitVec.replicateBits (BitVec.join1 [(BitVec.access imm8 1)]) 8)
          let imm8h : (BitVec 8) := (BitVec.replicateBits (BitVec.join1 [(BitVec.access imm8 0)]) 8)
          (((((((imm8a +++ imm8b) +++ imm8c) +++ imm8d) +++ imm8e) +++ imm8f) +++ imm8g) +++ imm8h))
        else imm64
      let imm64 : (BitVec 64) :=
        if ((((BitVec.join1 [(BitVec.access cmode 0)]) == 1#1) && (op == 0#1)) : Bool)
        then
          (let imm32 : (BitVec 32) := (((((BitVec.join1 [(BitVec.access imm8 7)]) +++ (Complement.complement (BitVec.join1 [(BitVec.access imm8 6)]))) +++ (BitVec.replicateBits (BitVec.join1 [(BitVec.access imm8 6)]) 5)) +++ (Sail.BitVec.extractLsb imm8 5 0)) +++ (Zeros (n := 19)))
          (BitVec.replicateBits imm32 2))
        else imm64
      if ((((BitVec.join1 [(BitVec.access cmode 0)]) == 1#1) && (op == 1#1)) : Bool)
      then
        (do
          if ((← (UsingAArch32 ())) : Bool)
          then (ReservedEncoding ())
          else (pure ())
          (pure (((((BitVec.join1 [(BitVec.access imm8 7)]) +++ (Complement.complement (BitVec.join1 [(BitVec.access imm8 6)]))) +++ (BitVec.replicateBits (BitVec.join1 [(BitVec.access imm8 6)]) 8)) +++ (Sail.BitVec.extractLsb imm8 5 0)) +++ (Zeros (n := 48)))))
      else (pure imm64))

/-- Type quantifiers: k_M : Nat, k_N : Nat, k_M ≥ 0 ∧ k_N ≥ 0 -/
def PolynomialMult (op1 : (BitVec k_M)) (op2 : (BitVec k_N)) : (BitVec (k_M + k_N)) := Id.run do
  let result : (BitVec (k_M + k_N)) := (Zeros (n := ((Sail.BitVec.length op1) +i (Sail.BitVec.length op2))))
  let extended_op2 : (BitVec (k_M + k_N)) := (Sail.BitVec.zeroExtend op2 ((Sail.BitVec.length op1) +i (Sail.BitVec.length op2)))
  let loop_i_lower := 0
  let loop_i_upper := ((Sail.BitVec.length op1) -i 1)
  let mut loop_vars := result
  for i in [loop_i_lower:loop_i_upper:1]i do
    let result := loop_vars
    loop_vars :=
      if (((BitVec.join1 [(BitVec.access op1 i)]) == 1#1) : Bool)
      then (result ^^^ (extended_op2 <<< i))
      else result
  (pure loop_vars)

/-- Type quantifiers: k_N : Nat, k_op1_unsigned : Bool, k_op2_unsigned : Bool, k_N = 128 -/
def MatMulAdd (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (op1_unsigned : Bool) (op2_unsigned : Bool) : SailM (BitVec k_N) := do
  sail_assert ((Sail.BitVec.length op2) == 128) "src/v8_base.sail:13317.20-13317.21"
  let result ← (( do (undefined_bitvector (Sail.BitVec.length op2)) ) : SailM (BitVec k_N) )
  let sum ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let prod ← (( do (undefined_int ()) ) : SailM Int )
  let (prod, result, sum) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := 1
    let mut loop_vars := (prod, result, sum)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (prod, result, sum) := loop_vars
      loop_vars ← do
        let (prod, result, sum) ← (( do
          let loop_j_lower := 0
          let loop_j_upper := 1
          let mut loop_vars_1 := (prod, result, sum)
          for j in [loop_j_lower:loop_j_upper:1]i do
            let (prod, result, sum) := loop_vars_1
            loop_vars_1 ← do
              let sum ← (Elem_read addend ((2 *i i) +i j) 32)
              let (prod, sum) ← (( do
                let loop_k_lower := 0
                let loop_k_upper := 7
                let mut loop_vars_2 := (prod, sum)
                for k in [loop_k_lower:loop_k_upper:1]i do
                  let (prod, sum) := loop_vars_2
                  loop_vars_2 ← do
                    let prod ← (pure ((← (asl_Int (← (Elem_read op1 ((8 *i i) +i k) 8)) op1_unsigned)) *i (← (asl_Int (← (Elem_read op2 ((8 *i j) +i k) 8)) op2_unsigned))))
                    let sum : (BitVec 32) := (BitVec.addInt sum prod)
                    (pure (prod, sum))
                (pure loop_vars_2) ) : SailM (Int × (BitVec 32)) )
              let result ← (Elem_set result ((2 *i i) +i j) 32 sum)
              (pure (prod, result, sum))
          (pure loop_vars_1) ) : SailM (Int × (BitVec k_N) × (BitVec 32)) )
        (pure (prod, result, sum))
    (pure loop_vars) ) : SailM (Int × (BitVec k_N) × (BitVec 32)) )
  (pure result)

def undefined_HPFAR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_HSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_MVBAR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_MVBAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_MVBAR_Type_Reserved (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)

def _update_MVBAR_Type_Reserved (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)

def undefined_DFSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def _get_DFSR_Type_AET (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)

def _update_DFSR_Type_AET (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_DISR_EL1_Type_AET (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 10 x)

def _update_VDFSR_Type_AET (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_VDISR_EL2_Type_AET (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_VDISR_Type_AET (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_VSESR_EL2_Type_AET (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _get_DISR_EL1_Type_AET (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 12 10)

def _get_VDISR_EL2_Type_AET (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)

def _get_VDISR_Type_AET (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)

def _get_DFSR_Type_CM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_DFSR_Type_CM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_EDHSR_Type_CM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_EDHSR_Type_CM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_DFSR_Type_Domain (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_DFSR_Type_Domain (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_DFSR_Type_ExT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_DFSR_Type_ExT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_DISR_Type_ExT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_IFSR32_EL2_Type_ExT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_IFSR_Type_ExT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_VDFSR_Type_ExT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_VDISR_EL2_Type_ExT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_VDISR_Type_ExT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_VSESR_EL2_Type_ExT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_DISR_Type_ExT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_IFSR32_EL2_Type_ExT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_IFSR_Type_ExT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_VDISR_EL2_Type_ExT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_VDISR_Type_ExT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_DFSR_Type_FS (v : (BitVec 32)) : (BitVec 5) :=
  ((Sail.BitVec.extractLsb v 10 10) +++ (Sail.BitVec.extractLsb v 3 0))

def _update_DFSR_Type_FS (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 10 10 (Sail.BitVec.extractLsb x (5 -i 1) (((5 -i 1) -i ((10 -i 10) +i 1)) +i 1))) 3 0 (Sail.BitVec.extractLsb x ((5 -i 1) -i ((10 -i 10) +i 1)) ((((5 -i 1) -i ((10 -i 10) +i 1)) -i ((3 -i 0) +i 1)) +i 1)))

def _update_DISR_Type_FS (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 10 10 (Sail.BitVec.extractLsb x (5 -i 1) (((5 -i 1) -i ((10 -i 10) +i 1)) +i 1))) 3 0 (Sail.BitVec.extractLsb x ((5 -i 1) -i ((10 -i 10) +i 1)) ((((5 -i 1) -i ((10 -i 10) +i 1)) -i ((3 -i 0) +i 1)) +i 1)))

def _update_IFSR32_EL2_Type_FS (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 10 10 (Sail.BitVec.extractLsb x (5 -i 1) (((5 -i 1) -i ((10 -i 10) +i 1)) +i 1))) 3 0 (Sail.BitVec.extractLsb x ((5 -i 1) -i ((10 -i 10) +i 1)) ((((5 -i 1) -i ((10 -i 10) +i 1)) -i ((3 -i 0) +i 1)) +i 1)))

def _update_IFSR_Type_FS (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 10 10 (Sail.BitVec.extractLsb x (5 -i 1) (((5 -i 1) -i ((10 -i 10) +i 1)) +i 1))) 3 0 (Sail.BitVec.extractLsb x ((5 -i 1) -i ((10 -i 10) +i 1)) ((((5 -i 1) -i ((10 -i 10) +i 1)) -i ((3 -i 0) +i 1)) +i 1)))

def _update_ISR_EL1_Type_FS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PAR_Type_FS (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 6 6 (Sail.BitVec.extractLsb x (6 -i 1) (((6 -i 1) -i ((6 -i 6) +i 1)) +i 1))) 5 1 (Sail.BitVec.extractLsb x ((6 -i 1) -i ((6 -i 6) +i 1)) ((((6 -i 1) -i ((6 -i 6) +i 1)) -i ((5 -i 1) +i 1)) +i 1)))

def _update_VDISR_EL2_Type_FS (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 10 10 (Sail.BitVec.extractLsb x (5 -i 1) (((5 -i 1) -i ((10 -i 10) +i 1)) +i 1))) 3 0 (Sail.BitVec.extractLsb x ((5 -i 1) -i ((10 -i 10) +i 1)) ((((5 -i 1) -i ((10 -i 10) +i 1)) -i ((3 -i 0) +i 1)) +i 1)))

def _update_VDISR_Type_FS (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 10 10 (Sail.BitVec.extractLsb x (5 -i 1) (((5 -i 1) -i ((10 -i 10) +i 1)) +i 1))) 3 0 (Sail.BitVec.extractLsb x ((5 -i 1) -i ((10 -i 10) +i 1)) ((((5 -i 1) -i ((10 -i 10) +i 1)) -i ((3 -i 0) +i 1)) +i 1)))

def _get_DISR_Type_FS (v : (BitVec 32)) : (BitVec 5) :=
  ((Sail.BitVec.extractLsb v 10 10) +++ (Sail.BitVec.extractLsb v 3 0))

def _get_IFSR32_EL2_Type_FS (v : (BitVec 64)) : (BitVec 5) :=
  ((Sail.BitVec.extractLsb v 10 10) +++ (Sail.BitVec.extractLsb v 3 0))

def _get_IFSR_Type_FS (v : (BitVec 32)) : (BitVec 5) :=
  ((Sail.BitVec.extractLsb v 10 10) +++ (Sail.BitVec.extractLsb v 3 0))

def _get_ISR_EL1_Type_FS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PAR_Type_FS (v : (BitVec 64)) : (BitVec 6) :=
  ((Sail.BitVec.extractLsb v 6 6) +++ (Sail.BitVec.extractLsb v 5 1))

def _get_VDISR_EL2_Type_FS (v : (BitVec 64)) : (BitVec 5) :=
  ((Sail.BitVec.extractLsb v 10 10) +++ (Sail.BitVec.extractLsb v 3 0))

def _get_VDISR_Type_FS (v : (BitVec 32)) : (BitVec 5) :=
  ((Sail.BitVec.extractLsb v 10 10) +++ (Sail.BitVec.extractLsb v 3 0))

def _get_DFSR_Type_FnV (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_DFSR_Type_FnV (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_EDHSR_Type_FnV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_IFSR32_EL2_Type_FnV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_IFSR_Type_FnV (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_EDHSR_Type_FnV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_IFSR32_EL2_Type_FnV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_IFSR_Type_FnV (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_DFSR_Type_LPAE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_DFSR_Type_LPAE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_DISR_Type_LPAE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_IFSR32_EL2_Type_LPAE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_IFSR_Type_LPAE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PAR_Type_LPAE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_VDISR_EL2_Type_LPAE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_VDISR_Type_LPAE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_DISR_Type_LPAE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_IFSR32_EL2_Type_LPAE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_IFSR_Type_LPAE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_PAR_Type_LPAE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_VDISR_EL2_Type_LPAE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_VDISR_Type_LPAE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _get_DFSR_Type_WnR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_DFSR_Type_WnR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_EDHSR_Type_WnR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_EDHSR_Type_WnR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def undefined_IFSR32_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_IFSR32_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_IFSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_DBGDSCRext_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGDSCRext_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _update_DBGDSCRext_Type_MDBGen (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_DBGDSCRint_Type_MDBGen (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_DBGDSCRint_Type_MDBGen (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_DBGDSCRext_Type_MOE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 5 2)

def _update_DBGDSCRint_Type_MOE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 2 x)

def _set_DBGDSCRext_Type_MOE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_DBGDSCRext_Type_MOE r v)

def _get_DBGDSCRint_Type_MOE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 5 2)

def _get_DBGDSCRext_Type_SPIDdis (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_DBGDSCRext_Type_SPIDdis (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_DBGDSCRint_Type_SPIDdis (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_DBGDSCRint_Type_SPIDdis (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_DBGDSCRext_Type_SPNIDdis (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_DBGDSCRext_Type_SPNIDdis (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_DBGDSCRint_Type_SPNIDdis (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_DBGDSCRint_Type_SPNIDdis (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_DBGDSCRext_Type_UDCCdis (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_DBGDSCRext_Type_UDCCdis (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_DBGDSCRint_Type_UDCCdis (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_DBGDSCRint_Type_UDCCdis (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def undefined_DBGDSCRint_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_HCR2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_HCR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_SCTLR2_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SCTLR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_SCTLR2_EL1_Type_EnADERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_SCTLR2_EL1_Type_EnADERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_SCTLR2_EL2_Type_EnADERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_SCTLR2_EL3_Type_EnADERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_SCTLR2_EL2_Type_EnADERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_SCTLR2_EL3_Type_EnADERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_SCTLR2_EL1_Type_EnANERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_SCTLR2_EL1_Type_EnANERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_SCTLR2_EL2_Type_EnANERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_SCTLR2_EL3_Type_EnANERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_SCTLR2_EL2_Type_EnANERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_SCTLR2_EL3_Type_EnANERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def undefined_SCTLR2_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SCTLR2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_SCTLR2_EL2_Type_EMEC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_SCTLR2_EL3_Type_EMEC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPInfinity (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  sail_assert ((N == 16) || ((N == 32) || (N == 64))) "src/v8_base.sail:15378.38-15378.39"
  let E :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F := (N -i (E +i 1))
  let exp : (BitVec E) := (Ones (n := E))
  let frac : (BitVec F) := (Zeros (n := F))
  (pure ((sign +++ exp) +++ frac))

/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPMaxNormal (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  sail_assert ((N == 16) || ((N == 32) || (N == 64))) "src/v8_base.sail:15389.38-15389.39"
  let E :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F := (N -i (E +i 1))
  let exp : (BitVec E) := ((Ones (n := (E -i 1))) +++ 0#1)
  let frac : (BitVec F) := (Ones (n := F))
  (pure ((sign +++ exp) +++ frac))

/-- Type quantifiers: k_is_ase : Bool -/
def AArch64_FPTrappedException (is_ase : Bool) (accumulated_exceptions : (BitVec 8)) : SailM Unit := do
  let except ← (( do (ExceptionSyndrome Exception_FPTrappedException) ) : SailM ExceptionRecord )
  let except ← (( do
    if (is_ase : Bool)
    then
      (do
        if ((← (__IMPDEF_boolean "vector instructions set TFV to 1")) : Bool)
        then (pure { except with syndrome := (BitVec.update except.syndrome 23 (Bit 1#1)) })
        else (pure { except with syndrome := (BitVec.update except.syndrome 23 (Bit 0#1)) }))
    else (pure { except with syndrome := (BitVec.update except.syndrome 23 (Bit 1#1)) }) ) : SailM ExceptionRecord )
  let except ← (pure { except with syndrome := ← (do (pure (Sail.BitVec.updateSubrange except.syndrome 10 8 (← (__UNKNOWN_bits 3))))) })
  let except ← (( do
    if (((BitVec.join1 [(BitVec.access except.syndrome 23)]) == 1#1) : Bool)
    then
      (let split_vec := ((BitVec.join1 [(BitVec.access accumulated_exceptions 7)]) +++ (Sail.BitVec.extractLsb accumulated_exceptions 4 0))
      let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 7 7 (Sail.BitVec.extractLsb split_vec 5 5)) }
      (pure { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0 (Sail.BitVec.extractLsb split_vec 4 0)) }))
    else
      (do
        let split_vec ← do (__UNKNOWN_bits 6)
        let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 7 7 (Sail.BitVec.extractLsb split_vec 5 5)) }
        (pure { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0 (Sail.BitVec.extractLsb split_vec 4 0)) })) ) : SailM ExceptionRecord )
  let route_to_el2 ← (( do (EL2Enabled ()) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  if (((BitVec.toNat (← readReg PSTATE).EL) >b (BitVec.toNat EL1)) : Bool)
  then (AArch64_TakeException (← readReg PSTATE).EL except preferred_exception_return vect_offset)
  else
    (do
      if (route_to_el2 : Bool)
      then (AArch64_TakeException EL2 except preferred_exception_return vect_offset)
      else (AArch64_TakeException EL1 except preferred_exception_return vect_offset))

def undefined_FPEXC32_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_FPEXC32_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_FPEXC32_EL2_Type_DEX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_FPEXC32_EL2_Type_DEX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_FPEXC_Type_DEX (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_FPEXC_Type_DEX (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_FPEXC32_EL2_Type_DZF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_FPEXC32_EL2_Type_DZF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_FPEXC_Type_DZF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_FPEXC_Type_DZF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_FPEXC32_EL2_Type_EN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_FPEXC32_EL2_Type_EN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_AMUSERENR_EL0_Type_EN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_AMUSERENR_Type_EN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CNTCR_Type_EN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_FPEXC_Type_EN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_LORC_EL1_Type_EN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMPCSCTL_Type_EN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMUSERENR_EL0_Type_EN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMUSERENR_Type_EN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_AMUSERENR_EL0_Type_EN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_AMUSERENR_Type_EN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_FPEXC_Type_EN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_LORC_EL1_Type_EN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMPCSCTL_Type_EN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMUSERENR_EL0_Type_EN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMUSERENR_Type_EN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_FPEXC32_EL2_Type_EX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_FPEXC32_EL2_Type_EX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_FPEXC_Type_EX (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMCFGR_Type_EX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_FPEXC_Type_EX (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMCFGR_Type_EX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_FPEXC32_EL2_Type_FP2V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_FPEXC32_EL2_Type_FP2V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_FPEXC_Type_FP2V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_FPEXC_Type_FP2V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_FPEXC32_EL2_Type_IDF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_FPEXC32_EL2_Type_IDF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_FPEXC_Type_IDF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_FPEXC_Type_IDF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_FPEXC32_EL2_Type_IOF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_FPEXC32_EL2_Type_IOF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_FPEXC_Type_IOF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_FPEXC_Type_IOF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_FPEXC32_EL2_Type_IXF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_FPEXC32_EL2_Type_IXF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_FPEXC_Type_IXF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_FPEXC_Type_IXF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_FPEXC32_EL2_Type_OFF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_FPEXC32_EL2_Type_OFF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_FPEXC_Type_OFF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_FPEXC_Type_OFF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_FPEXC32_EL2_Type_TFV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_FPEXC32_EL2_Type_TFV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_FPEXC_Type_TFV (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_FPEXC_Type_TFV (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_FPEXC32_EL2_Type_UFF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_FPEXC32_EL2_Type_UFF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_FPEXC_Type_UFF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_FPEXC_Type_UFF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_FPEXC32_EL2_Type_VECITR (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 10 8)

def _update_FPEXC32_EL2_Type_VECITR (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 8 x)

def _update_FPEXC_Type_VECITR (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 8 x)

def _get_FPEXC_Type_VECITR (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 10 8)

def _get_FPEXC32_EL2_Type_VV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_FPEXC32_EL2_Type_VV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_FPEXC_Type_VV (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_FPEXC_Type_VV (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def undefined_FPEXC_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_FPEXC_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def FPEXC_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _FPEXC ) : SailM FPEXC_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg FPEXC32_EL2) 0 32)))

def FPEXC_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : FPEXC_Type := value_name
  writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange (← readReg FPEXC32_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _FPEXC r

def FPSCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : FPSCR_Type := value_name
  writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 31 27 (BitVec.slice r 27 5))
  writeReg FPSR (BitVec.update (← readReg FPSR) 7 (Bit (BitVec.slice r 7 1)))
  writeReg FPSR (Sail.BitVec.updateSubrange (← readReg FPSR) 4 0 (BitVec.slice r 0 5))
  writeReg FPCR (Sail.BitVec.updateSubrange (← readReg FPCR) 26 15 (BitVec.slice r 15 12))
  writeReg FPCR (Sail.BitVec.updateSubrange (← readReg FPCR) 12 8 (BitVec.slice r 8 5))

def GetAccumulatedFPExceptions (_ : Unit) : SailM (BitVec 8) := do
  (__UNKNOWN_bits 8)

def IsASEInstruction (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())

def SetAccumulatedFPExceptions (accumulated_exceptions : (BitVec 8)) : Unit :=
  ()

/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPZero (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  sail_assert ((N == 16) || ((N == 32) || (N == 64))) "src/v8_base.sail:15627.38-15627.39"
  let E :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F := (N -i (E +i 1))
  let exp : (BitVec E) := (Zeros (n := E))
  let frac : (BitVec F) := (Zeros (n := F))
  (pure ((sign +++ exp) +++ frac))

/-- Type quantifiers: M : Nat, k_N : Nat, List.elem k_N [16, 32, 64] ∧ List.elem M [16, 32, 64] -/
def FPConvertNaN (op : (BitVec k_N)) (M : Nat) : SailM (BitVec M) := do
  sail_assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length op) == 64))) "src/v8_base.sail:16429.41-16429.42"
  sail_assert ((M == 16) || ((M == 32) || (M == 64))) "src/v8_base.sail:16430.38-16430.39"
  let result ← (( do (undefined_bitvector M) ) : SailM (BitVec M) )
  let frac ← (( do (undefined_bitvector 51) ) : SailM (BitVec 51) )
  let sign : (BitVec 1) := (BitVec.join1 [(BitVec.access op ((Sail.BitVec.length op) -i 1))])
  let frac : (BitVec 51) :=
    match (Sail.BitVec.length op) with
    | 64 => (Sail.BitVec.extractLsb op 50 0)
    | 32 => ((Sail.BitVec.extractLsb op 21 0) +++ (Zeros (n := 29)))
    | 16 => ((Sail.BitVec.extractLsb op 8 0) +++ (Zeros (n := 42)))
    | _ => frac
  match M with
  | 64 => (pure ((sign +++ (Ones (n := (M -i 52)))) +++ frac))
  | 32 => (pure ((sign +++ (Ones (n := (M -i 23)))) +++ (Sail.BitVec.extractLsb frac 50 29)))
  | 16 => (pure ((sign +++ (Ones (n := (M -i 10)))) +++ (Sail.BitVec.extractLsb frac 50 42)))
  | _ => (pure result)

/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPTwo (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  sail_assert ((N == 16) || ((N == 32) || (N == 64))) "src/v8_base.sail:17017.38-17017.39"
  let E :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F := (N -i (E +i 1))
  let exp : (BitVec (1 + (E - 1))) := (1#1 +++ (Zeros (n := (E -i 1))))
  let frac : (BitVec F) := (Zeros (n := F))
  (pure ((sign +++ exp) +++ frac))

/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPOnePointFive (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  sail_assert ((N == 16) || ((N == 32) || (N == 64))) "src/v8_base.sail:17244.38-17244.39"
  let E :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F := (N -i (E +i 1))
  let exp : (BitVec (1 + (E - 1))) := (0#1 +++ (Ones (n := (E -i 1))))
  let frac : (BitVec (1 + (F - 1))) := (1#1 +++ (Zeros (n := (F -i 1))))
  (pure ((sign +++ exp) +++ frac))

/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPThree (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  sail_assert ((N == 16) || ((N == 32) || (N == 64))) "src/v8_base.sail:17825.38-17825.39"
  let E :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F := (N -i (E +i 1))
  let exp : (BitVec (1 + (E - 1))) := (1#1 +++ (Zeros (n := (E -i 1))))
  let frac : (BitVec (1 + (F - 1))) := (1#1 +++ (Zeros (n := (F -i 1))))
  (pure ((sign +++ exp) +++ frac))

/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def VFPExpandImm (imm8 : (BitVec 8)) (N : Nat) : SailM (BitVec N) := do
  sail_assert ((N == 16) || ((N == 32) || (N == 64))) "src/v8_base.sail:17939.38-17939.39"
  let E :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F := ((N -i E) -i 1)
  let sign : (BitVec 1) := (BitVec.join1 [(BitVec.access imm8 7)])
  let exp : (BitVec (1 + (E - 3) + 2)) := (((Complement.complement (BitVec.join1 [(BitVec.access imm8 6)])) +++ (BitVec.replicateBits (BitVec.join1 [(BitVec.access imm8 6)]) (E -i 3))) +++ (Sail.BitVec.extractLsb imm8 5 4))
  let frac : (BitVec (4 + (F - 4))) := ((Sail.BitVec.extractLsb imm8 3 0) +++ (Zeros (n := (F -i 4))))
  (pure ((sign +++ exp) +++ frac))

/-- Type quantifiers: N : Nat, N ≥ 0 -/
def SPSR_read {N : _} : SailM (BitVec N) := do
  let result ← (( do (undefined_bitvector N) ) : SailM (BitVec N) )
  if ((← (UsingAArch32 ())) : Bool)
  then
    (do
      sail_assert (N == 32) "src/v8_base.sail:17954.22-17954.23"
      let questionMark ← do (pure (← readReg PSTATE).M)
      if ((questionMark == M32_FIQ) : Bool)
      then (do (pure (Sail.BitVec.extractLsb (← readReg SPSR_fiq) (N -i 1) 0)))
      else
        (do
          if ((questionMark == M32_IRQ) : Bool)
          then (do (pure (Sail.BitVec.extractLsb (← readReg SPSR_irq) (N -i 1) 0)))
          else
            (do
              if ((questionMark == M32_Svc) : Bool)
              then (do (pure (Sail.BitVec.extractLsb (← (SPSR_svc_read ())) (N -i 1) 0)))
              else
                (do
                  if ((questionMark == M32_Monitor) : Bool)
                  then (do (pure (Sail.BitVec.extractLsb (← readReg SPSR_mon) (N -i 1) 0)))
                  else
                    (do
                      if ((questionMark == M32_Abort) : Bool)
                      then (do (pure (Sail.BitVec.extractLsb (← readReg SPSR_abt) (N -i 1) 0)))
                      else
                        (do
                          if ((questionMark == M32_Hyp) : Bool)
                          then (do (pure (Sail.BitVec.extractLsb (← (SPSR_hyp_read ())) (N -i 1) 0)))
                          else
                            (do
                              if ((questionMark == M32_Undef) : Bool)
                              then (do (pure (Sail.BitVec.extractLsb (← readReg SPSR_und) (N -i 1) 0)))
                              else
                                (do
                                  (Unreachable ())
                                  (pure result)))))))))
  else
    (do
      sail_assert (N == 64) "src/v8_base.sail:17982.22-17982.23"
      let questionMark ← do (pure (← readReg PSTATE).EL)
      if ((questionMark == EL1) : Bool)
      then (do (pure (Sail.BitVec.extractLsb (← readReg SPSR_EL1) (N -i 1) 0)))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then (do (pure (Sail.BitVec.extractLsb (← readReg SPSR_EL2) (N -i 1) 0)))
          else
            (do
              if ((questionMark == EL3) : Bool)
              then (do (pure (Sail.BitVec.extractLsb (← readReg SPSR_EL3) (N -i 1) 0)))
              else
                (do
                  (Unreachable ())
                  (pure result)))))

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def BranchToAddr (target : (BitVec k_N)) (branch_type : BranchType) : SailM Unit := do
  (Hint_Branch branch_type)
  if (((Sail.BitVec.length target) == 32) : Bool)
  then
    (do
      sail_assert (← (UsingAArch32 ())) "src/v8_base.sail:18006.29-18006.30"
      let _ : Unit := (sail_branch_announce 64 (ZeroExtend1 (m := 64) target))
      writeReg _PC (Sail.BitVec.zeroExtend target 64))
  else
    (do
      sail_assert (←((pure ((Sail.BitVec.length target) == 64)) <&&> (do
        (pure (! (← (UsingAArch32 ()))))))) "src/v8_base.sail:18010.50-18010.51"
      let _ : Unit := (sail_branch_announce 64 (Sail.BitVec.extractLsb target 63 0))
      writeReg _PC (Sail.BitVec.extractLsb target 63 0))
  writeReg __BranchTaken true

def undefined_CNTHP_CTL_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTHP_CTL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_CNTHP_CTL_EL2_Type_ENABLE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CNTHPS_CTL_EL2_Type_ENABLE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CNTHPS_CTL_Type_ENABLE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CNTHP_CTL_Type_ENABLE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CNTHVS_CTL_EL2_Type_ENABLE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CNTHVS_CTL_Type_ENABLE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CNTHV_CTL_EL2_Type_ENABLE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CNTHV_CTL_Type_ENABLE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CNTPS_CTL_EL1_Type_ENABLE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CNTP_CTL_EL0_Type_ENABLE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CNTP_CTL_Type_ENABLE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CNTV_CTL_EL0_Type_ENABLE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_CNTV_CTL_Type_ENABLE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_CNTHPS_CTL_Type_ENABLE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_CNTHVS_CTL_Type_ENABLE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_CNTHV_CTL_Type_ENABLE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_CNTV_CTL_Type_ENABLE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_CNTHP_CTL_EL2_Type_IMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_CNTHPS_CTL_EL2_Type_IMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_CNTHPS_CTL_Type_IMASK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_CNTHP_CTL_Type_IMASK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_CNTHVS_CTL_EL2_Type_IMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_CNTHVS_CTL_Type_IMASK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_CNTHV_CTL_EL2_Type_IMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_CNTHV_CTL_Type_IMASK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_CNTPS_CTL_EL1_Type_IMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_CNTP_CTL_EL0_Type_IMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_CNTP_CTL_Type_IMASK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_CNTV_CTL_EL0_Type_IMASK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_CNTV_CTL_Type_IMASK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_CNTHPS_CTL_Type_IMASK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_CNTHVS_CTL_Type_IMASK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_CNTHV_CTL_Type_IMASK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_CNTV_CTL_Type_IMASK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_CNTHP_CTL_EL2_Type_ISTATUS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_CNTHPS_CTL_EL2_Type_ISTATUS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_CNTHPS_CTL_Type_ISTATUS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_CNTHVS_CTL_EL2_Type_ISTATUS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_CNTHVS_CTL_Type_ISTATUS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_CNTHV_CTL_EL2_Type_ISTATUS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_CNTHV_CTL_Type_ISTATUS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_CNTPS_CTL_EL1_Type_ISTATUS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_CNTP_CTL_EL0_Type_ISTATUS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_CNTV_CTL_EL0_Type_ISTATUS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_CNTV_CTL_Type_ISTATUS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_CNTHPS_CTL_EL2_Type_ISTATUS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_CNTHPS_CTL_Type_ISTATUS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_CNTHP_CTL_Type_ISTATUS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_CNTHVS_CTL_EL2_Type_ISTATUS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_CNTHVS_CTL_Type_ISTATUS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_CNTHV_CTL_EL2_Type_ISTATUS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_CNTHV_CTL_Type_ISTATUS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_CNTP_CTL_Type_ISTATUS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_CNTV_CTL_Type_ISTATUS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _set_CNTHP_CTL_Type_ISTATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTHP_CTL_Type_ISTATUS r v)

def _set_CNTP_CTL_Type_ISTATUS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_CNTP_CTL_Type_ISTATUS r v)

def undefined_CNTHP_CTL_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CNTHP_CTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_CNTHP_CVAL_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTHP_CVAL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_CNTHP_CVAL_EL2_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _update_CNTHP_CVAL_EL2_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_CNTHPS_CVAL_EL2_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_CNTHP_CVAL_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_CNTHVS_CVAL_EL2_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_CNTHV_CVAL_EL2_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_CNTPS_CVAL_EL1_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_CNTP_CVAL_EL0_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_CNTP_CVAL_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_CNTV_CVAL_EL0_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_CNTV_CVAL_Type_CompareValue (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _get_CNTHPS_CVAL_EL2_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_CNTHP_CVAL_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_CNTHVS_CVAL_EL2_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_CNTHV_CVAL_EL2_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_CNTPS_CVAL_EL1_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_CNTP_CVAL_EL0_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_CNTP_CVAL_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_CNTV_CVAL_EL0_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_CNTV_CVAL_Type_CompareValue (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def undefined_CNTHP_CVAL_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTHP_CVAL_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CNTP_CTL_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTP_CTL_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_CNTP_CTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_CNTP_CVAL_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTP_CVAL_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_CNTP_CVAL_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CNTV_CTL_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTV_CTL_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CNTV_CVAL_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTV_CVAL_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CNTHPS_CTL_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTHPS_CTL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CNTHPS_CVAL_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTHPS_CVAL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CNTHVS_CTL_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTHVS_CTL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CNTHVS_CVAL_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTHVS_CVAL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CNTHV_CTL_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTHV_CTL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CNTHV_CVAL_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTHV_CVAL_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CNTPS_CTL_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTPS_CTL_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CNTPS_CVAL_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTPS_CVAL_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CNTCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CNTCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _update_CNTCR_Type_FCREQ (v : (BitVec 32)) (x : (BitVec 10)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 8 x)

def _update_CNTCR_Type_HDBG (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_AMCFGR_EL0_Type_HDBG (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_AMCFGR_Type_HDBG (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_AMCR_EL0_Type_HDBG (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_AMCR_Type_HDBG (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_AMCFGR_EL0_Type_HDBG (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_AMCFGR_Type_HDBG (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_AMCR_EL0_Type_HDBG (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_AMCR_Type_HDBG (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_CNTCR_Type_SCEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def undefined_CNTSCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CNTSCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CNTSCR_Type_ScaleVal (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_CNTSCR_Type_ScaleVal (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def undefined_CNTKCTL_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CNTKCTL_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def PAREncodeShareability (memattrs : MemoryAttributes) : (BitVec 2) :=
  if (((BEq.beq memattrs.memtype MemType_Device) || ((memattrs.inner.attrs == MemAttr_NC) && (memattrs.outer.attrs == MemAttr_NC))) : Bool)
  then 0b10#2
  else
    (match memattrs.shareability with
    | .Shareability_NSH => 0b00#2
    | .Shareability_ISH => 0b11#2
    | .Shareability_OSH => 0b10#2)

def EncodePARAttrs (memattrs : MemoryAttributes) : SailM (BitVec 8) := SailME.run do
  let result ← (( do (undefined_bitvector 8) ) : SailME (BitVec 8) (BitVec 8) )
  if (((← (HaveMTEExt ())) && (BEq.beq memattrs.tags MemTag_AllocationTagged)) : Bool)
  then
    (do
      if (((← (HaveMTEPermExt ())) && memattrs.notagaccess) : Bool)
      then (pure (Sail.BitVec.updateSubrange result 7 0 0b11100000#8))
      else (pure (Sail.BitVec.updateSubrange result 7 0 0b11110000#8)))
  else
    (do
      if ((BEq.beq memattrs.memtype MemType_Device) : Bool)
      then
        (let result : (BitVec 8) := (Sail.BitVec.updateSubrange result 7 4 0b0000#4)
        let result : (BitVec 8) :=
          match memattrs.device with
          | .DeviceType_nGnRnE => (Sail.BitVec.updateSubrange result 3 0 0b0000#4)
          | .DeviceType_nGnRE => (Sail.BitVec.updateSubrange result 3 0 0b0100#4)
          | .DeviceType_nGRE => (Sail.BitVec.updateSubrange result 3 0 0b1000#4)
          | .DeviceType_GRE => (Sail.BitVec.updateSubrange result 3 0 0b1100#4)
        (pure (BitVec.update result 0 (Bit (Complement.complement memattrs.xs)))))
      else
        (do
          if ((memattrs.xs == 0#1) : Bool)
          then
            (do
              if (((((memattrs.outer.attrs == MemAttr_WT) && (memattrs.inner.attrs == MemAttr_WT)) && (! memattrs.outer.transient)) && (memattrs.outer.hints == MemHint_RA)) : Bool)
              then SailME.throw (0b10100000#8 : (BitVec 8))
              else
                (do
                  if (((memattrs.outer.attrs == MemAttr_NC) && (memattrs.inner.attrs == MemAttr_NC)) : Bool)
                  then SailME.throw (0b01000000#8 : (BitVec 8))
                  else (pure ())))
          else (pure ())
          let result : (BitVec 8) :=
            if ((memattrs.outer.attrs == MemAttr_WT) : Bool)
            then
              (let result : (BitVec 8) :=
                (Sail.BitVec.updateSubrange result 7 6
                  (if (memattrs.outer.transient : Bool)
                  then 0b00#2
                  else 0b10#2))
              (Sail.BitVec.updateSubrange result 5 4 memattrs.outer.hints))
            else
              (if ((memattrs.outer.attrs == MemAttr_WB) : Bool)
              then
                (let result : (BitVec 8) :=
                  (Sail.BitVec.updateSubrange result 7 6
                    (if (memattrs.outer.transient : Bool)
                    then 0b01#2
                    else 0b11#2))
                (Sail.BitVec.updateSubrange result 5 4 memattrs.outer.hints))
              else (Sail.BitVec.updateSubrange result 7 4 0b0100#4))
          if ((memattrs.inner.attrs == MemAttr_WT) : Bool)
          then
            (let result : (BitVec 8) :=
              (Sail.BitVec.updateSubrange result 3 2
                (if (memattrs.inner.transient : Bool)
                then 0b00#2
                else 0b10#2))
            (pure (Sail.BitVec.updateSubrange result 1 0 memattrs.inner.hints)))
          else
            (if ((memattrs.inner.attrs == MemAttr_WB) : Bool)
            then
              (let result : (BitVec 8) :=
                (Sail.BitVec.updateSubrange result 3 2
                  (if (memattrs.inner.transient : Bool)
                  then 0b01#2
                  else 0b11#2))
              (pure (Sail.BitVec.updateSubrange result 1 0 memattrs.inner.hints)))
            else (pure (Sail.BitVec.updateSubrange result 3 0 0b0100#4)))))

def undefined_GPCCR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GPCCR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_GPCCR_EL3_Type_GPC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_GPCCR_EL3_Type_GPCP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_GPCCR_EL3_Type_GPCP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_GPCCR_EL3_Type_L0GPTSZ (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_GPCCR_EL3_Type_ORGN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_GPCCR_EL3_Type_PGS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_GPCCR_EL3_Type_PPS (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def undefined_GPTBR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GPTBR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def SecurityStateForRegime (regime : Regime) : SailM SecurityState := do
  match regime with
  | .Regime_EL3 => (SecurityStateAtEL EL3)
  | .Regime_EL30 => (pure SS_Secure)
  | .Regime_EL2 => (SecurityStateAtEL EL2)
  | .Regime_EL20 => (SecurityStateAtEL EL2)
  | .Regime_EL10 => (SecurityStateAtEL EL1)

def ExclusiveFault (accdesc : AccessDescriptor) : SailM FaultRecord := do
  let fault ← (( do (undefined_FaultRecord ()) ) : SailM FaultRecord )
  let fault : FaultRecord := { fault with statuscode := Fault_Exclusive }
  let fault : FaultRecord := { fault with access := accdesc }
  let fault : FaultRecord := { fault with secondstage := false }
  let fault : FaultRecord := { fault with s2fs1walk := false }
  let fault : FaultRecord := { fault with write := ((! accdesc.read) && accdesc.write) }
  let fault : FaultRecord := { fault with gpcfs2walk := false }
  (pure { fault with gpcf := ← (do (GPCNoFault ())) })

def undefined_MAIR2_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MAIR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_MAIR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MAIR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PIRE0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PIRE0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PIR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PIR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_TCR2_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_TCR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_TCR2_EL1_Type_DisCH1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_TCR2_EL2_Type_DisCH1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def undefined_MAIR2_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MAIR2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_MAIR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MAIR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PIR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PIR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_TCR2_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_TCR2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_TCR2_EL2_Type_AMEC0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_TCR2_EL2_Type_AMEC1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_TCR2_EL2_Type_SKL0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def _update_TCR2_EL2_Type_SKL0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _get_TCR2_EL2_Type_SKL1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)

def _update_TCR2_EL2_Type_SKL1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def undefined_PIRE0_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PIRE0_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_MAIR2_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MAIR2_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_MAIR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MAIR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PIR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PIR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_SCTLR2_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_SCTLR2_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_TTBR0_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_TTBR0_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def PtrHasUpperAndLowerAddRanges (_ : Unit) : SailM Bool := do
  let regime ← (( do (TranslationRegime (← readReg PSTATE).EL) ) : SailM Regime )
  (pure (HasUnprivileged regime))

/-- Type quantifiers: k_data : Bool -/
def Strip (A : (BitVec 64)) (data : Bool) : SailM (BitVec 64) := do
  let original_ptr ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let tbi ← (( do (pure ((← (EffectiveTBI A (! data) (← readReg PSTATE).EL)) == 1#1)) ) : SailM Bool )
  let mtx ← (( do (pure ((← (EffectiveMTX A (! data) (← readReg PSTATE).EL)) == 1#1)) ) : SailM Bool )
  let bottom_PAC_bit ← do (CalculateBottomPACBit (BitVec.join1 [(BitVec.access A 55)]))
  let extfield : (BitVec 64) := (BitVec.replicateBits (BitVec.join1 [(BitVec.access A 55)]) 64)
  if ((tbi && (bottom_PAC_bit ≥b 55)) : Bool)
  then (pure A)
  else
    (do
      if (tbi : Bool)
      then
        (do
          sail_assert ((0 ≤b ((56 -i bottom_PAC_bit) -i 1)) && (((56 -i bottom_PAC_bit) -i 1) <b 64)) "src/v8_base.sail:21567.90-21567.91"
          sail_assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "src/v8_base.sail:21568.80-21568.81"
          (pure (((Sail.BitVec.extractLsb A 63 56) +++ (Sail.BitVec.extractLsb extfield ((56 -i bottom_PAC_bit) -i 1) 0)) +++ (Sail.BitVec.extractLsb A (bottom_PAC_bit -i 1) 0))))
      else
        (do
          if (mtx : Bool)
          then
            (do
              sail_assert ((0 ≤b ((56 -i bottom_PAC_bit) -i 1)) && (((56 -i bottom_PAC_bit) -i 1) <b 64)) "src/v8_base.sail:21571.90-21571.91"
              sail_assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "src/v8_base.sail:21572.80-21572.81"
              (pure ((((Sail.BitVec.extractLsb extfield 63 60) +++ (Sail.BitVec.extractLsb A 59 56)) +++ (Sail.BitVec.extractLsb extfield ((56 -i bottom_PAC_bit) -i 1) 0)) +++ (Sail.BitVec.extractLsb A (bottom_PAC_bit -i 1) 0))))
          else
            (do
              sail_assert ((0 ≤b ((64 -i bottom_PAC_bit) -i 1)) && (((64 -i bottom_PAC_bit) -i 1) <b 64)) "src/v8_base.sail:21575.90-21575.91"
              sail_assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "src/v8_base.sail:21576.80-21576.81"
              (pure ((Sail.BitVec.extractLsb extfield ((64 -i bottom_PAC_bit) -i 1) 0) +++ (Sail.BitVec.extractLsb A (bottom_PAC_bit -i 1) 0))))))

def AddPACGA (x : (BitVec 64)) (y : (BitVec 64)) : SailM (BitVec 64) := do
  let TrapEL2 ← (( do (undefined_bool ()) ) : SailM Bool )
  let TrapEL3 ← (( do (undefined_bool ()) ) : SailM Bool )
  let isgeneric : Bool := true
  let APGAKey_EL1 ← (( do (pure ((Sail.BitVec.extractLsb (← readReg APGAKeyHi_EL1) 63 0) +++ (Sail.BitVec.extractLsb (← readReg APGAKeyLo_EL1) 63 0))) ) : SailM (BitVec 128) )
  let (TrapEL2, TrapEL3) ← (( do
    let questionMark ← do (pure (← readReg PSTATE).EL)
    let (TrapEL2, TrapEL3) ← (( do
      if ((questionMark == EL0) : Bool)
      then
        (do
          let TrapEL2 ← (EL2Enabled ()) <&&> (do (pure ((_get_HCR_EL2_Type_API (← readReg HCR_EL2)) == 0#1))) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 0#1)) <||> (do (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1))))
          let TrapEL3 ← (pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_API (← readReg SCR_EL3)) == 0#1)))
          (pure (TrapEL2, TrapEL3)))
      else
        (do
          let (TrapEL2, TrapEL3) ← (( do
            if ((questionMark == EL1) : Bool)
            then
              (do
                let TrapEL2 ← (EL2Enabled ()) <&&> (do (pure ((_get_HCR_EL2_Type_API (← readReg HCR_EL2)) == 0#1)))
                let TrapEL3 ← (pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_API (← readReg SCR_EL3)) == 0#1)))
                (pure (TrapEL2, TrapEL3)))
            else
              (do
                let (TrapEL2, TrapEL3) ← (( do
                  if ((questionMark == EL2) : Bool)
                  then
                    (do
                      let TrapEL2 : Bool := false
                      let TrapEL3 ← (pure (HaveEL EL3)) <&&> (do (pure ((_get_SCR_EL3_Type_API (← readReg SCR_EL3)) == 0#1)))
                      (pure (TrapEL2, TrapEL3)))
                  else
                    (let (TrapEL2, TrapEL3) : (Bool × Bool) :=
                      if ((questionMark == EL3) : Bool)
                      then
                        (let TrapEL2 : Bool := false
                        let TrapEL3 : Bool := false
                        (TrapEL2, TrapEL3))
                      else (TrapEL2, TrapEL3)
                    (pure (TrapEL2, TrapEL3))) ) : SailM (Bool × Bool) )
                (pure (TrapEL2, TrapEL3))) ) : SailM (Bool × Bool) )
          (pure (TrapEL2, TrapEL3))) ) : SailM (Bool × Bool) )
    (pure (TrapEL2, TrapEL3)) ) : SailM (Bool × Bool) )
  if ((←((pure TrapEL3) <&&> (do
       (EL3SDDUndefPriority ())))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if (TrapEL2 : Bool)
      then
        (do
          (TrapPACUse EL2)
          (undefined_bitvector 64))
      else
        (do
          if (TrapEL3 : Bool)
          then
            (do
              if ((← (EL3SDDUndef ())) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  (TrapPACUse EL3)
                  (undefined_bitvector 64)))
          else (pure ((Sail.BitVec.extractLsb (← (ComputePAC x y (Sail.BitVec.extractLsb APGAKey_EL1 127 64) (Sail.BitVec.extractLsb APGAKey_EL1 63 0) isgeneric)) 63 32) +++ (Zeros (n := 32))))))

/-- Type quantifiers: n : Int, width : Nat, List.elem width [8, 16, 32, 64, 128] -/
def V_read (n : Int) (width : Nat) : SailM (BitVec width) := do
  sail_assert ((n ≥b 0) && (n ≤b 31)) "src/v8_base.sail:22333.27-22333.28"
  sail_assert ((width == 8) || ((width == 16) || ((width == 32) || ((width == 64) || (width == 128))))) "src/v8_base.sail:22334.78-22334.79"
  (pure (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg _Z) n) (width -i 1) 0))

def AArch64_ResetGeneralRegisters (_ : Unit) : SailM Unit := do
  let loop_i_lower := 0
  let loop_i_upper := 30
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do (X_set i 64 (← (__UNKNOWN_bits 64)))
  (pure loop_vars)

def AArch64_ResetSIMDFPRegisters (_ : Unit) : SailM Unit := do
  let loop_i_lower := 0
  let loop_i_upper := 31
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do (V_set i 128 (← (__UNKNOWN_bits 128)))
  (pure loop_vars)

def ELR_read (el : (BitVec 2)) : SailM (BitVec 64) := do
  let r ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let questionMark := el
  if ((questionMark == EL1) : Bool)
  then (do readReg ELR_EL1)
  else
    (do
      if ((questionMark == EL2) : Bool)
      then (do readReg ELR_EL2)
      else
        (do
          if ((questionMark == EL3) : Bool)
          then (do readReg ELR_EL3)
          else
            (do
              (Unreachable ())
              (pure r))))

def undefined_CNTKCTL_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CNTKCTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CNTKCTL_Type_PL0PCTEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_CNTKCTL_Type_PL0PCTEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_CNTKCTL_Type_PL0PTEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_CNTKCTL_Type_PL0PTEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_CNTKCTL_Type_PL0VCTEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_CNTKCTL_Type_PL0VCTEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_CNTKCTL_Type_PL0VTEN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_CNTKCTL_Type_PL0VTEN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def CNTKCTL_read__1 (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CNTKCTL ) : SailM CNTKCTL_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg CNTKCTL_EL1) 0 32)))

def CheckTransactionalSystemAccess (op0 : (BitVec 2)) (op1 : (BitVec 3)) (crn : (BitVec 4)) (crm : (BitVec 4)) (op2 : (BitVec 3)) (read : (BitVec 1)) : SailM Bool := do
  let b__0 := (((((read +++ op0) +++ op1) +++ crn) +++ crm) +++ op2)
  if ((((Sail.BitVec.extractLsb b__0 16 7) == (0b0000110100#10 : (BitVec 10))) && ((Sail.BitVec.extractLsb b__0 2 1) == (0b11#2 : (BitVec 2)))) : Bool)
  then (pure true)
  else
    (do
      if ((b__0 == (0b00101101110100001#17 : (BitVec 17))) : Bool)
      then (pure true)
      else
        (do
          if (((Sail.BitVec.extractLsb b__0 16 1) == (0x6D08#16 : (BitVec 16))) : Bool)
          then (pure true)
          else
            (do
              if (((Sail.BitVec.extractLsb b__0 16 1) == (0x6D10#16 : (BitVec 16))) : Bool)
              then (pure true)
              else
                (do
                  if ((b__0 == (0b01100001000110000#17 : (BitVec 17))) : Bool)
                  then (pure true)
                  else
                    (do
                      if ((b__0 == (0b01101110011100100#17 : (BitVec 17))) : Bool)
                      then (pure true)
                      else
                        (do
                          if ((b__0 == (0b11101100100101001#17 : (BitVec 17))) : Bool)
                          then (pure ((← readReg PSTATE).EL == EL0))
                          else
                            (do
                              if ((b__0 == (0b11100000100101001#17 : (BitVec 17))) : Bool)
                              then (pure ((← readReg PSTATE).EL == EL1)) <||> (do (pure ((← readReg PSTATE).EL == EL2)) <&&> (do (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1))))
                              else
                                (do
                                  if ((b__0 == (0b11110000100101001#17 : (BitVec 17))) : Bool)
                                  then (pure ((← readReg PSTATE).EL == EL2)) <&&> (do (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 0#1)))
                                  else
                                    (do
                                      if ((b__0 == (0b11111000100101001#17 : (BitVec 17))) : Bool)
                                      then (pure ((← readReg PSTATE).EL == EL3))
                                      else
                                        (do
                                          if ((b__0 == (0b00101101110111000#17 : (BitVec 17))) : Bool)
                                          then (pure true)
                                          else
                                            (do
                                              if ((b__0 == (0b10101101110111001#17 : (BitVec 17))) : Bool)
                                              then (pure true)
                                              else
                                                (do
                                                  if ((b__0 == (0b00101101110111010#17 : (BitVec 17))) : Bool)
                                                  then (pure true)
                                                  else
                                                    (do
                                                      if ((b__0 == (0b10101101110111011#17 : (BitVec 17))) : Bool)
                                                      then (pure true)
                                                      else
                                                        (do
                                                          if ((b__0 == (0b00100001110111110#17 : (BitVec 17))) : Bool)
                                                          then (pure true)
                                                          else
                                                            (do
                                                              if ((b__0 == (0b11110100100101001#17 : (BitVec 17))) : Bool)
                                                              then (pure false)
                                                              else
                                                                (do
                                                                  if ((b__0 == (0b11100000100101010#17 : (BitVec 17))) : Bool)
                                                                  then (pure false)
                                                                  else
                                                                    (do
                                                                      if ((b__0 == (0b11100000100101000#17 : (BitVec 17))) : Bool)
                                                                      then (pure false)
                                                                      else
                                                                        (do
                                                                          if ((b__0 == (0b11110100100101000#17 : (BitVec 17))) : Bool)
                                                                          then (pure false)
                                                                          else
                                                                            (do
                                                                              if ((b__0 == (0b11110000100101000#17 : (BitVec 17))) : Bool)
                                                                              then (pure false)
                                                                              else
                                                                                (do
                                                                                  if ((b__0 == (0b11111000100101000#17 : (BitVec 17))) : Bool)
                                                                                  then (pure false)
                                                                                  else
                                                                                    (do
                                                                                      if ((((Sail.BitVec.extractLsb b__0 16 14) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb b__0 10 10) == (0#1 : (BitVec 1)))) : Bool)
                                                                                      then (pure true)
                                                                                      else
                                                                                        (do
                                                                                          if ((((Sail.BitVec.extractLsb b__0 16 14) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb b__0 10 8) == (0b100#3 : (BitVec 3)))) : Bool)
                                                                                          then (pure true)
                                                                                          else
                                                                                            (do
                                                                                              if ((((Sail.BitVec.extractLsb b__0 16 14) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb b__0 10 7) == (0xA#4 : (BitVec 4)))) : Bool)
                                                                                              then (pure true)
                                                                                              else
                                                                                                (do
                                                                                                  if ((((Sail.BitVec.extractLsb b__0 16 6) == (0b11100011001#11 : (BitVec 11))) && ((Sail.BitVec.extractLsb b__0 4 0) == (0b00010#5 : (BitVec 5)))) : Bool)
                                                                                                  then (pure true)
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((b__0 == (0b11100011001011011#17 : (BitVec 17))) : Bool)
                                                                                                      then (pure true)
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((((Sail.BitVec.extractLsb b__0 16 14) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb b__0 10 7) == (0xD#4 : (BitVec 4)))) : Bool)
                                                                                                          then (pure true)
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((((Sail.BitVec.extractLsb b__0 16 14) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb b__0 10 7) == (0xE#4 : (BitVec 4)))) : Bool)
                                                                                                              then (pure true)
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((b__0 == (0b00101101110011111#17 : (BitVec 17))) : Bool)
                                                                                                                  then (pure true)
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      if (((Sail.BitVec.extractLsb b__0 16 1) == (0x2DCE#16 : (BitVec 16))) : Bool)
                                                                                                                      then (pure true)
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          if ((((Sail.BitVec.extractLsb b__0 15 14) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.extractLsb b__0 10 10) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb b__0 8 7) == (0b11#2 : (BitVec 2))))) : Bool)
                                                                                                                          then (__IMPDEF_boolean "")
                                                                                                                          else (pure false)))))))))))))))))))))))))))))))

def BTypeCompatible_BTI (hintcode : (BitVec 2)) : SailM Bool := do
  match (hintcode : BitVec 2) with
  | 0b00 => (pure false)
  | 0b01 => (pure ((← readReg PSTATE).BTYPE != 0b11#2))
  | 0b10 => (pure ((← readReg PSTATE).BTYPE != 0b10#2))
  | 0b11 => (pure true)
  | _ => (do (undefined_bool ()))

def BTypeCompatible_PACIXSP (_ : Unit) : SailM Bool := do
  let index ← (( do (undefined_int ()) ) : SailM Int )
  if ((←((pure ((← readReg PSTATE).BTYPE == 0b01#2)) <||> (do
       (pure ((← readReg PSTATE).BTYPE == 0b10#2))))) : Bool)
  then (pure true)
  else
    (do
      if (((← readReg PSTATE).BTYPE == 0b11#2) : Bool)
      then
        (do
          let index ← do
            if (((← readReg PSTATE).EL == EL0) : Bool)
            then (pure 35)
            else (pure 36)
          (pure ((BitVec.join1 [(BitVec.access (← (SCTLR_read__1 ())) index)]) == 0#1)))
      else (pure false))

def AArch64_ExecutingERETInstr (_ : Unit) : SailM Bool := do
  let instr ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
  (pure ((Sail.BitVec.extractLsb instr 31 12) == 0b11010110100111110000#20))

def SetBTypeNext (x : (BitVec 2)) : SailM Unit := do
  writeReg BTypeNext x

def undefined_GCR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_GCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_GCR_EL1_Type_Exclude (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _update_GCR_EL1_Type_Exclude (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _get_GCR_EL1_Type_RRND (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_GCR_EL1_Type_RRND (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def undefined_RGSR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_RGSR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_RGSR_EL1_Type_SEED (v : (BitVec 64)) : (BitVec 48) :=
  (Sail.BitVec.extractLsb v 55 8)

def _update_RGSR_EL1_Type_SEED (v : (BitVec 64)) (x : (BitVec 48)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 8 x)

def _get_RGSR_EL1_Type_TAG (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_RGSR_EL1_Type_TAG (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def AArch64_ChooseNonExcludedTag (tag_in : (BitVec 4)) (offset_in : (BitVec 4)) (exclude : (BitVec 16)) : (BitVec 4) := Id.run do
  let tag : (BitVec 4) := tag_in
  let offset : (BitVec 4) := offset_in
  if ((IsOnes exclude) : Bool)
  then (pure 0b0000#4)
  else
    (do
      let tag ← (( do
        if ((offset == 0b0000#4) : Bool)
        then
          (do
            let mut loop_vars := tag
            while (λ tag => ((BitVec.join1 [(BitVec.access exclude (BitVec.toNat tag))]) == 1#1)) loop_vars do
              let tag := loop_vars
              loop_vars := ((tag + 0b0001#4) : (BitVec 4))
            (pure loop_vars))
        else (pure tag) ) : Id (BitVec 4) )
      let (offset, tag) ← (( do
        let mut loop_vars_1 := (offset, tag)
        while (λ (offset, tag) => (offset != 0b0000#4)) loop_vars_1 do
          let (offset, tag) := loop_vars_1
          loop_vars_1 ← do
            let offset : (BitVec 4) := (offset - 0b0001#4)
            let tag : (BitVec 4) := (tag + 0b0001#4)
            let tag ← (( do
              let mut loop_vars_2 := tag
              while (λ tag => ((BitVec.join1 [(BitVec.access exclude (BitVec.toNat tag))]) == 1#1)) loop_vars_2 do
                let tag := loop_vars_2
                loop_vars_2 := ((tag + 0b0001#4) : (BitVec 4))
              (pure loop_vars_2) ) : Id (BitVec 4) )
            (pure (offset, tag))
        (pure loop_vars_1) ) : Id ((BitVec 4) × (BitVec 4)) )
      (pure tag))

def undefined_TFSRE0_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_TFSRE0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_TFSRE0_EL1_Type_TF0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_TFSRE0_EL1_Type_TF0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_TFSR_EL1_Type_TF0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_TFSR_EL2_Type_TF0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_TFSR_EL3_Type_TF0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_TFSR_EL1_Type_TF0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_TFSR_EL2_Type_TF0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_TFSR_EL3_Type_TF0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_TFSRE0_EL1_Type_TF1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_TFSRE0_EL1_Type_TF1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_TFSR_EL1_Type_TF1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_TFSR_EL2_Type_TF1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_TFSR_EL1_Type_TF1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_TFSR_EL2_Type_TF1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def undefined_TFSR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_TFSR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_TFSR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_TFSR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_TFSR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_TFSR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_CONTEXTIDR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_CONTEXTIDR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_DBGBCR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_DBGBCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_DBGBCR_EL1_Type_BAS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 5 x)

def _update_DBGBCR_Type_BAS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 5 x)

def _update_DBGWCR_EL1_Type_BAS (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 5 x)

def _update_DBGWCR_Type_BAS (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 5 x)

def _update_DBGBCR_EL1_Type_BT2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_DBGBCR_EL1_Type_HMC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_DBGBCR_Type_HMC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_DBGWCR_EL1_Type_HMC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_DBGWCR_Type_HMC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_DBGBCR_EL1_Type_LBN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_DBGBCR_Type_LBN (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_DBGWCR_EL1_Type_LBN (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_DBGWCR_Type_LBN (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_DBGWCR_Type_LBN (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_DBGBCR_EL1_Type_LBNX (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 30 x)

def _update_DBGWCR_EL1_Type_LBNX (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 30 x)

def _update_DBGBCR_EL1_Type_MASK (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 24 x)

def _update_DBGWCR_EL1_Type_MASK (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 24 x)

def _update_DBGWCR_Type_MASK (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 24 x)

def _update_DBGBCR_EL1_Type_PMC (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 1 x)

def _update_DBGBCR_Type_PMC (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 1 x)

def _update_DBGBCR_EL1_Type_SSC (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_DBGBCR_Type_SSC (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_DBGWCR_EL1_Type_SSC (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_DBGWCR_Type_SSC (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_DBGBCR_EL1_Type_SSCE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_DBGWCR_EL1_Type_SSCE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def undefined_DBGBVR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_DBGBVR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_DBGBVR_EL1_Type_ContextID (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_DBGBVR_EL1_Type_ContextID (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_DBGBVR_Type_ContextID (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _get_DBGBVR_Type_ContextID (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _get_DBGBVR_EL1_Type_ContextID2 (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 63 32)

def _update_DBGBVR_EL1_Type_ContextID2 (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 32 x)

def _update_DBGBXVR_Type_ContextID2 (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _get_DBGBXVR_Type_ContextID2 (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _get_DBGBVR_EL1_Type_RESS (v : (BitVec 64)) : (BitVec 15) :=
  ((Sail.BitVec.extractLsb v 63 57) +++ ((Sail.BitVec.extractLsb v 56 53) +++ (Sail.BitVec.extractLsb v 52 49)))

def _update_DBGBVR_EL1_Type_RESS (v : (BitVec 64)) (x : (BitVec 15)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 63 57 (Sail.BitVec.extractLsb x (15 -i 1) (((15 -i 1) -i ((63 -i 57) +i 1)) +i 1))) 56 53 (Sail.BitVec.extractLsb x ((15 -i 1) -i ((63 -i 57) +i 1)) ((((15 -i 1) -i ((63 -i 57) +i 1)) -i ((56 -i 53) +i 1)) +i 1))) 52 49 (Sail.BitVec.extractLsb x (((15 -i 1) -i ((63 -i 57) +i 1)) -i ((56 -i 53) +i 1)) (((((15 -i 1) -i ((63 -i 57) +i 1)) -i ((56 -i 53) +i 1)) -i ((52 -i 49) +i 1)) +i 1)))

def _update_DBGWVR_EL1_Type_RESS (v : (BitVec 64)) (x : (BitVec 15)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 63 57 (Sail.BitVec.extractLsb x (15 -i 1) (((15 -i 1) -i ((63 -i 57) +i 1)) +i 1))) 56 53 (Sail.BitVec.extractLsb x ((15 -i 1) -i ((63 -i 57) +i 1)) ((((15 -i 1) -i ((63 -i 57) +i 1)) -i ((56 -i 53) +i 1)) +i 1))) 52 49 (Sail.BitVec.extractLsb x (((15 -i 1) -i ((63 -i 57) +i 1)) -i ((56 -i 53) +i 1)) (((((15 -i 1) -i ((63 -i 57) +i 1)) -i ((56 -i 53) +i 1)) -i ((52 -i 49) +i 1)) +i 1)))

def _update_VNCR_EL2_Type_RESS (v : (BitVec 64)) (x : (BitVec 7)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 57 x)

def _get_DBGWVR_EL1_Type_RESS (v : (BitVec 64)) : (BitVec 15) :=
  ((Sail.BitVec.extractLsb v 63 57) +++ ((Sail.BitVec.extractLsb v 56 53) +++ (Sail.BitVec.extractLsb v 52 49)))

def _get_VNCR_EL2_Type_RESS (v : (BitVec 64)) : (BitVec 7) :=
  (Sail.BitVec.extractLsb v 63 57)

def _get_DBGBVR_EL1_Type_VMID (v : (BitVec 64)) : (BitVec 16) :=
  ((Sail.BitVec.extractLsb v 47 40) +++ (Sail.BitVec.extractLsb v 39 32))

def _update_DBGBVR_EL1_Type_VMID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 47 40 (Sail.BitVec.extractLsb x (16 -i 1) (((16 -i 1) -i ((47 -i 40) +i 1)) +i 1))) 39 32 (Sail.BitVec.extractLsb x ((16 -i 1) -i ((47 -i 40) +i 1)) ((((16 -i 1) -i ((47 -i 40) +i 1)) -i ((39 -i 32) +i 1)) +i 1)))

def _update_DBGBXVR_Type_VMID (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 8 (Sail.BitVec.extractLsb x (16 -i 1) (((16 -i 1) -i ((15 -i 8) +i 1)) +i 1))) 7 0 (Sail.BitVec.extractLsb x ((16 -i 1) -i ((15 -i 8) +i 1)) ((((16 -i 1) -i ((15 -i 8) +i 1)) -i ((7 -i 0) +i 1)) +i 1)))

def _update_EDVIDSR_Type_VMID (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 8 (Sail.BitVec.extractLsb x (16 -i 1) (((16 -i 1) -i ((15 -i 8) +i 1)) +i 1))) 7 0 (Sail.BitVec.extractLsb x ((16 -i 1) -i ((15 -i 8) +i 1)) ((((16 -i 1) -i ((15 -i 8) +i 1)) -i ((7 -i 0) +i 1)) +i 1)))

def _update_PMVCIDSR_Type_VMID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 47 40 (Sail.BitVec.extractLsb x (16 -i 1) (((16 -i 1) -i ((47 -i 40) +i 1)) +i 1))) 39 32 (Sail.BitVec.extractLsb x ((16 -i 1) -i ((47 -i 40) +i 1)) ((((16 -i 1) -i ((47 -i 40) +i 1)) -i ((39 -i 32) +i 1)) +i 1)))

def _update_PMVIDSR_Type_VMID (v : (BitVec 32)) (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 15 8 (Sail.BitVec.extractLsb x (16 -i 1) (((16 -i 1) -i ((15 -i 8) +i 1)) +i 1))) 7 0 (Sail.BitVec.extractLsb x ((16 -i 1) -i ((15 -i 8) +i 1)) ((((16 -i 1) -i ((15 -i 8) +i 1)) -i ((7 -i 0) +i 1)) +i 1)))

def _update_VTTBR_EL2_Type_VMID (v : (BitVec 128)) (x : (BitVec 16)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 63 48 x)

def _update_VTTBR_Type_VMID (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)

def _get_DBGBXVR_Type_VMID (v : (BitVec 32)) : (BitVec 16) :=
  ((Sail.BitVec.extractLsb v 15 8) +++ (Sail.BitVec.extractLsb v 7 0))

def _get_EDVIDSR_Type_VMID (v : (BitVec 32)) : (BitVec 16) :=
  ((Sail.BitVec.extractLsb v 15 8) +++ (Sail.BitVec.extractLsb v 7 0))

def _get_PMVCIDSR_Type_VMID (v : (BitVec 64)) : (BitVec 16) :=
  ((Sail.BitVec.extractLsb v 47 40) +++ (Sail.BitVec.extractLsb v 39 32))

def _get_PMVIDSR_Type_VMID (v : (BitVec 32)) : (BitVec 16) :=
  ((Sail.BitVec.extractLsb v 15 8) +++ (Sail.BitVec.extractLsb v 7 0))

def undefined_EDSCR2_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDSCR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_VTCR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_VTCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_VTCR_EL2_Type_GCSH (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _update_VTCR_EL2_Type_NSA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_VTCR_EL2_Type_NSW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_VTCR_EL2_Type_S2PIE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _update_ID_AA64MMFR3_EL1_Type_S2PIE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_AA64MMFR3_EL1_Type_S2PIE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_VTCR_EL2_Type_S2POE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _update_ID_AA64MMFR3_EL1_Type_S2POE (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_AA64MMFR3_EL1_Type_S2POE (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_VTCR_EL2_Type_SL0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _update_VSTCR_EL2_Type_SL0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _update_VTCR_Type_SL0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _update_VTCR_EL2_Type_SL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _update_VSTCR_EL2_Type_SL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _update_VTCR_EL2_Type_TL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _update_VTCR_EL2_Type_TL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _update_VTCR_EL2_Type_VS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def undefined_VTTBR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_VTTBR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_VTTBR_EL2_Type (_ : Unit) : SailM (BitVec 128) := do
  (undefined_bitvector 128)

def Mk_VTTBR_EL2_Type (v : (BitVec 128)) : (BitVec 128) :=
  v

def undefined_DBGWCR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_DBGWCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_DBGWCR_EL1_Type_LSC (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 3 x)

def _update_DBGWCR_Type_LSC (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 3 x)

def _update_DBGWCR_EL1_Type_PAC (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 1 x)

def _update_DBGWCR_Type_PAC (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 1 x)

def _update_DBGWCR_EL1_Type_WT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_DBGWCR_Type_WT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMCFGR_Type_WT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_PMCFGR_Type_WT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def undefined_DBGWVR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_DBGWVR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_POR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_POR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_POR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_POR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_POR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_POR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_POR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_POR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_MECID_P0_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MECID_P0_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_MECID_P0_EL2_Type_MECID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_MECID_A0_EL2_Type_MECID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_MECID_A1_EL2_Type_MECID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_MECID_P1_EL2_Type_MECID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_MECID_RL_A_EL3_Type_MECID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_VMECID_A_EL2_Type_MECID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def _update_VMECID_P_EL2_Type_MECID (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def undefined_VMECID_P_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_VMECID_P_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_MECID_A0_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MECID_A0_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_MECID_A1_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MECID_A1_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_MECID_P1_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MECID_P1_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_MECID_RL_A_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MECID_RL_A_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_S2PIR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_S2PIR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_VSTCR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_VSTCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _update_VSTCR_EL2_Type_SW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_FPSID_Type_SW (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMUSERENR_EL0_Type_SW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMUSERENR_Type_SW (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_FPSID_Type_SW (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMUSERENR_EL0_Type_SW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMUSERENR_Type_SW (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def undefined_VSTTBR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_VSTTBR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_S2POR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_S2POR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_VMECID_A_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_VMECID_A_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

/-- Type quantifiers: k_ispair : Bool, size : Nat, (size * 8) ≥ 0 -/
def Mem_read__1 (address : (BitVec 64)) (size : Nat) (accdesc : AccessDescriptor) (ispair : Bool) : SailM (BitVec (size * 8)) := do
  let highestAddressfirst : Bool := false
  sail_assert (((((size == 1) || (size == 2)) || (size == 4)) || (size == 8)) || (size == 16)) "src/v8_base.sail:28174.48-28174.49"
  (Mem_read__2 address size accdesc ispair highestAddressfirst)

/-- Type quantifiers: k_ispair : Bool, size : Nat, (size * 8) ≥ 0 -/
def Mem_set__1 (address : (BitVec 64)) (size : Nat) (accdesc : AccessDescriptor) (ispair : Bool) (value_in_name : (BitVec (size * 8))) : SailM Unit := do
  let highestAddressfirst : Bool := false
  (Mem_set__2 address size accdesc ispair highestAddressfirst value_in_name)

/-- Type quantifiers: k_size : Nat, k_size ≥ 0 -/
def MemAtomic (address : (BitVec 64)) (cmpoperand : (BitVec k_size)) (operand : (BitVec k_size)) (accdesc_in : AccessDescriptor) : SailM (BitVec k_size) := do
  sail_assert accdesc_in.atomicop "src/v8_base.sail:28335.30-28335.31"
  let bytes := (Int.ediv (Sail.BitVec.length operand) 8)
  sail_assert ((bytes == 1) || ((bytes == 2) || ((bytes == 4) || ((bytes == 8) || (bytes == 16))))) "src/v8_base.sail:28337.74-28337.75"
  let newvalue ← (( do (undefined_bitvector (Sail.BitVec.length operand)) ) : SailM (BitVec k_size) )
  let oldvalue ← (( do (undefined_bitvector (Sail.BitVec.length operand)) ) : SailM (BitVec k_size) )
  let accdesc : AccessDescriptor := accdesc_in
  let aligned : Bool := (IsAligned__1 address bytes)
  let accdesc ← (( do
    if (((← (HaveMTE2Ext ())) && accdesc.tagchecked) : Bool)
    then (do (pure { accdesc with tagchecked := ← (do (AArch64_AccessIsTagChecked address accdesc)) }))
    else (pure accdesc) ) : SailM AccessDescriptor )
  if ((←((pure (! aligned)) <&&> (do
       (AArch64_UnalignedAccessFaults accdesc address bytes)))) : Bool)
  then (AArch64_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned (Sail.BitVec.length operand)) ) : SailM AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then (AArch64_Abort address memaddrdesc.fault)
  else (pure ())
  let _ : Unit :=
    if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
    then (ClearExclusiveByAddress memaddrdesc.paddress (ProcessorID ()) (Sail.BitVec.length operand))
    else ()
  if ((←((pure ((← (HaveMTE2Ext ())) && accdesc.tagchecked)) <&&> (do
       (pure (! (← (HaveMTEStoreOnlyExt ())))) <||> (do
         (pure (! (← (StoreOnlyTagCheckingEnabled accdesc.el)))))))) : Bool)
  then
    (do
      let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
      if ((! (← (AArch64_CheckTag memaddrdesc accdesc ptag))) : Bool)
      then (AArch64_TagCheckFault address accdesc)
      else (pure ()))
  else (pure ())
  let memstatus ← (( do (undefined_PhysMemRetStatus ()) ) : SailM PhysMemRetStatus )
  sail_assert ((8 *i bytes) == (Sail.BitVec.length operand)) "src/v8_base.sail:28363.42-28363.43"
  let (memstatus, oldvalue) ← (( do
    let (tup__0, tup__1) ← do (PhysMemRead memaddrdesc bytes accdesc none)
    let memstatus : PhysMemRetStatus := tup__0
    let oldvalue : (BitVec k_size) := tup__1
    (pure (memstatus, oldvalue)) ) : SailM (PhysMemRetStatus × (BitVec k_size)) )
  if ((IsFault__2 memstatus) : Bool)
  then (HandleExternalReadAbort memstatus memaddrdesc bytes accdesc)
  else (pure ())
  let oldvalue ← (( do
    if ((← (BigEndian accdesc.acctype)) : Bool)
    then (pure (reverse_endianness oldvalue))
    else (pure oldvalue) ) : SailM (BitVec k_size) )
  let oldvalue := oldvalue
  let cmpfail : Bool := false
  let (cmpfail, newvalue) : (Bool × (BitVec k_size)) :=
    match accdesc.modop with
    | .MemAtomicOp_ADD =>
      (let newvalue : (BitVec k_size) := (oldvalue + operand)
      (cmpfail, newvalue))
    | .MemAtomicOp_BIC =>
      (let newvalue : (BitVec k_size) := (oldvalue &&& (Complement.complement operand))
      (cmpfail, newvalue))
    | .MemAtomicOp_EOR =>
      (let newvalue : (BitVec k_size) := (oldvalue ^^^ operand)
      (cmpfail, newvalue))
    | .MemAtomicOp_ORR =>
      (let newvalue : (BitVec k_size) := (oldvalue ||| operand)
      (cmpfail, newvalue))
    | .MemAtomicOp_SMAX =>
      (let newvalue : (BitVec k_size) := (integer_subrange (Max.max (BitVec.toInt oldvalue) (BitVec.toInt operand)) ((Sail.BitVec.length operand) -i 1) 0)
      (cmpfail, newvalue))
    | .MemAtomicOp_SMIN =>
      (let newvalue : (BitVec k_size) := (integer_subrange (Min.min (BitVec.toInt oldvalue) (BitVec.toInt operand)) ((Sail.BitVec.length operand) -i 1) 0)
      (cmpfail, newvalue))
    | .MemAtomicOp_UMAX =>
      (let newvalue : (BitVec k_size) := (integer_subrange (Max.max (BitVec.toNat oldvalue) (BitVec.toNat operand)) ((Sail.BitVec.length operand) -i 1) 0)
      (cmpfail, newvalue))
    | .MemAtomicOp_UMIN =>
      (let newvalue : (BitVec k_size) := (integer_subrange (Min.min (BitVec.toNat oldvalue) (BitVec.toNat operand)) ((Sail.BitVec.length operand) -i 1) 0)
      (cmpfail, newvalue))
    | .MemAtomicOp_SWP =>
      (let newvalue : (BitVec k_size) := operand
      (cmpfail, newvalue))
    | .MemAtomicOp_CAS =>
      (let newvalue : (BitVec k_size) := operand
      let cmpfail : Bool := (cmpoperand != oldvalue)
      (cmpfail, newvalue))
    | .MemAtomicOp_GCSSS1 =>
      (let newvalue : (BitVec k_size) := operand
      let cmpfail : Bool := (cmpoperand != oldvalue)
      (cmpfail, newvalue))
  let accdesc ← (( do
    if ((←((HaveMTEStoreOnlyExt ()) <&&> (do
         (StoreOnlyTagCheckingEnabled accdesc.el)))) : Bool)
    then
      (do
        let accdesc ← (( do
          if ((accdesc.tagchecked && cmpfail) : Bool)
          then (do (pure { accdesc with tagchecked := ← (do (ConstrainUnpredictableBool Unpredictable_STOREONLYTAGCHECKEDCAS)) }))
          else (pure accdesc) ) : SailM AccessDescriptor )
        if (((← (HaveMTE2Ext ())) && accdesc.tagchecked) : Bool)
        then
          (do
            let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
            if ((! (← (AArch64_CheckTag memaddrdesc accdesc ptag))) : Bool)
            then
              (do
                let accdesc : AccessDescriptor := { accdesc with read := false }
                (AArch64_TagCheckFault address accdesc)
                (pure accdesc))
            else (pure accdesc))
        else (pure accdesc))
    else (pure accdesc) ) : SailM AccessDescriptor )
  if ((! cmpfail) : Bool)
  then
    (do
      let newvalue ← (( do
        if ((← (BigEndian accdesc.acctype)) : Bool)
        then (pure (reverse_endianness newvalue))
        else (pure newvalue) ) : SailM (BitVec k_size) )
      let memstatus ← (( do (PhysMemWrite memaddrdesc bytes accdesc none newvalue) ) : SailM PhysMemRetStatus )
      if ((IsFault__2 memstatus) : Bool)
      then (HandleExternalWriteAbort memstatus memaddrdesc bytes accdesc)
      else (pure ()))
  else (pure ())
  if ((← readReg SPESampleInFlight) : Bool)
  then
    (do
      let is_load : Bool := false
      (SPESampleLoadStore is_load accdesc memaddrdesc))
  else (pure ())
  (pure oldvalue)

def IsD128Enabled (el : (BitVec 2)) : SailM Bool := do
  let d128enabled ← (( do (undefined_bool ()) ) : SailM Bool )
  if ((← (Have128BitDescriptorExt ())) : Bool)
  then
    (do
      let questionMark := el
      if ((questionMark == EL0) : Bool)
      then
        (do
          if ((! (← (ELIsInHost EL0))) : Bool)
          then (do (IsTCR2EL1Enabled ()) <&&> (do (pure ((_get_TCR2_EL1_Type_D128 (← readReg TCR2_EL1)) == 1#1))))
          else (do (IsTCR2EL2Enabled ()) <&&> (do (pure ((_get_TCR2_EL2_Type_D128 (← readReg TCR2_EL2)) == 1#1)))))
      else
        (do
          if ((questionMark == EL1) : Bool)
          then (do (IsTCR2EL1Enabled ()) <&&> (do (pure ((_get_TCR2_EL1_Type_D128 (← readReg TCR2_EL1)) == 1#1))))
          else
            (do
              if ((questionMark == EL2) : Bool)
              then (do (IsTCR2EL2Enabled ()) <&&> (do (pure ((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) == 1#1))) <&&> (do (pure ((_get_TCR2_EL2_Type_D128 (← readReg TCR2_EL2)) == 1#1))))
              else
                (do
                  if ((questionMark == EL3) : Bool)
                  then (do (pure ((_get_TCR_EL3_Type_D128 (← readReg TCR_EL3)) == 1#1)))
                  else (pure d128enabled)))))
  else (pure false)

def undefined_RCWMASK_EL1_Type (_ : Unit) : SailM (BitVec 128) := do
  (undefined_bitvector 128)

def Mk_RCWMASK_EL1_Type (v : (BitVec 128)) : (BitVec 128) :=
  v

def _get_RCWMASK_EL1_Type_Mask (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v 127 0)

def _update_RCWMASK_EL1_Type_Mask (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 127 0 x)

def undefined_RCWSMASK_EL1_Type (_ : Unit) : SailM (BitVec 128) := do
  (undefined_bitvector 128)

def Mk_RCWSMASK_EL1_Type (v : (BitVec 128)) : (BitVec 128) :=
  v

def _get_RCWSMASK_EL1_Type_Software_Mask (v : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.extractLsb v 127 0)

def _update_RCWSMASK_EL1_Type_Software_Mask (v : (BitVec 128)) (x : (BitVec 128)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 127 0 x)

def AArch64_AddressWithAllocationTag (address : (BitVec 64)) (allocation_tag : (BitVec 4)) : SailM (BitVec 64) := do
  let result : (BitVec 64) := address
  let tag ← (( do (undefined_bitvector 4) ) : SailM (BitVec 4) )
  let tag ← (( do
    if ((← (AArch64_AllocationTagAccessIsEnabled (← readReg PSTATE).EL)) : Bool)
    then (pure allocation_tag)
    else (pure 0b0000#4) ) : SailM (BitVec 4) )
  (pure (Sail.BitVec.updateSubrange result 59 56 tag))

def AArch64_AllocationTagFromAddress (tagged_address : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb tagged_address 59 56)

def PhysMemTagWrite (desc : AddressDescriptor) (accdesc : AccessDescriptor) (data : (BitVec 4)) : SailM PhysMemRetStatus := do
  (undefined_PhysMemRetStatus ())

def undefined_VNCR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_VNCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def AddressSupportsLS64 (paddress : (BitVec 56)) : SailM Bool := do
  (__UNKNOWN_boolean ())

def MemStore64BWithRet (address : (BitVec 64)) (value_name : (BitVec 512)) (accdesc_in : AccessDescriptor) : SailM (BitVec 64) := SailME.run do
  let size := 64
  let accdesc : AccessDescriptor := accdesc_in
  let aligned : Bool := (IsAligned__1 address size)
  if ((←((pure (! aligned)) <&&> (do
       (AArch64_UnalignedAccessFaults accdesc address size)))) : Bool)
  then (AArch64_Abort address (← (AlignmentFault accdesc)))
  else (pure ())
  let accdesc ← (( do
    if (((← (HaveMTE2Ext ())) && accdesc.tagchecked) : Bool)
    then (do (pure { accdesc with tagchecked := ← (do (AArch64_AccessIsTagChecked address accdesc)) }))
    else (pure accdesc) ) : SailME (BitVec 64) AccessDescriptor )
  let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned size) ) : SailME (BitVec 64) AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then
    (do
      (AArch64_Abort address memaddrdesc.fault)
      (pure (Sail.BitVec.zeroExtend 1#1 64)))
  else
    (do
      let _ : Unit :=
        if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
        then (ClearExclusiveByAddress memaddrdesc.paddress (ProcessorID ()) 64)
        else ()
      if (((← (HaveMTE2Ext ())) && accdesc.tagchecked) : Bool)
      then
        (do
          let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
          if ((! (← (AArch64_CheckTag memaddrdesc accdesc ptag))) : Bool)
          then
            SailME.throw (← (do
                (AArch64_TagCheckFault address accdesc)
                (pure (Sail.BitVec.zeroExtend 1#1 64))))
          else (pure ()))
      else (pure ())
      let memstatus ← (( do (PhysMemWrite memaddrdesc size accdesc none value_name) ) : SailME (BitVec 64) PhysMemRetStatus )
      if ((IsFault__2 memstatus) : Bool)
      then (HandleExternalWriteAbort memstatus memaddrdesc size accdesc)
      else (pure ())
      (pure memstatus.store64bstatus))

def AArch64_IsUnprivAccessPriv (_ : Unit) : SailM Bool := do
  let privileged ← (( do (undefined_bool ()) ) : SailM Bool )
  let privileged ← (( do
    let questionMark ← do (pure (← readReg PSTATE).EL)
    if ((questionMark == EL0) : Bool)
    then (pure false)
    else
      (do
        if ((questionMark == EL1) : Bool)
        then (do (EL2Enabled ()) <&&> (do (HaveNVExt ())) <&&> (do (pure (((_get_HCR_EL2_Type_NV (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_NV1 (← readReg HCR_EL2))) == 0b11#2))))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then (do (pure (! (←((HaveVirtHostExt ()) <&&> (do (pure (((_get_HCR_EL2_Type_E2H (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_TGE (← readReg HCR_EL2))) == 0b11#2))))))))
            else
              (if ((questionMark == EL3) : Bool)
              then (pure true)
              else (pure privileged)))) ) : SailM Bool )
  if ((←((HaveUAOExt ()) <&&> (do
       (pure ((← readReg PSTATE).UAO == 1#1))))) : Bool)
  then (do (pure ((← readReg PSTATE).EL != EL0)))
  else (pure privileged)

/-- Type quantifiers: size : Int -/
def AArch64_DataMemZero (regval : (BitVec 64)) (vaddress : (BitVec 64)) (accdesc_in : AccessDescriptor) (size : Int) : SailM Unit := do
  let memstatus ← (( do (undefined_PhysMemRetStatus ()) ) : SailM PhysMemRetStatus )
  let accdesc : AccessDescriptor := accdesc_in
  let accdesc ← (( do
    if (((← (HaveMTE2Ext ())) && accdesc.tagaccess) : Bool)
    then (do (pure { accdesc with tagaccess := ← (do (AArch64_AllocationTagAccessIsEnabled accdesc.el)) }))
    else (pure accdesc) ) : SailM AccessDescriptor )
  let accdesc ← (( do
    if (((← (HaveMTE2Ext ())) && accdesc.tagchecked) : Bool)
    then (do (pure { accdesc with tagchecked := ← (do (AArch64_AccessIsTagChecked vaddress accdesc)) }))
    else (pure accdesc) ) : SailM AccessDescriptor )
  let aligned : Bool := true
  let memaddrdesc ← (( do (AArch64_TranslateAddress vaddress accdesc aligned size) ) : SailM AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then
    (do
      if ((← (IsDebugException memaddrdesc.fault)) : Bool)
      then (AArch64_Abort vaddress memaddrdesc.fault)
      else (AArch64_Abort regval memaddrdesc.fault))
  else (pure ())
  if ((← (HaveTME ())) : Bool)
  then
    (do
      if ((←((pure accdesc.transactional) <&&> (do
           (pure (! (← (MemHasTransactionalAccess memaddrdesc.memattrs))))))) : Bool)
      then (FailTransaction TMFailure_IMP false)
      else (pure ()))
  else (pure ())
  let (memaddrdesc, memstatus) ← (( do
    let loop_i_lower := 0
    let loop_i_upper := (size -i 1)
    let mut loop_vars := (memaddrdesc, memstatus)
    for i in [loop_i_lower:loop_i_upper:1]i do
      let (memaddrdesc, memstatus) := loop_vars
      loop_vars ← do
        if (((← (HaveMTE2Ext ())) && accdesc.tagchecked) : Bool)
        then
          (do
            let ptag : (BitVec 4) := (AArch64_PhysicalTag vaddress)
            if ((! (← (AArch64_CheckTag memaddrdesc accdesc ptag))) : Bool)
            then
              (do
                if ((← (__IMPDEF_boolean "DC_ZVA tag fault reported with lowest faulting address")) : Bool)
                then (AArch64_TagCheckFault vaddress accdesc)
                else (AArch64_TagCheckFault regval accdesc))
            else (pure ()))
        else (pure ())
        let memstatus ← (PhysMemWrite memaddrdesc 1 accdesc none (Zeros (n := 8)))
        if ((IsFault__2 memstatus) : Bool)
        then (HandleExternalWriteAbort memstatus memaddrdesc 1 accdesc)
        else (pure ())
        let memaddrdesc : AddressDescriptor := { memaddrdesc with paddress := { memaddrdesc.paddress with address := (BitVec.addInt memaddrdesc.paddress.address 1) } }
        (pure (memaddrdesc, memstatus))
    (pure loop_vars) ) : SailM (AddressDescriptor × PhysMemRetStatus) )
  (pure ())

/-- Type quantifiers: processorid : Int, size : Int -/
def AArch64_MarkExclusiveVA (address : (BitVec 64)) (processorid : Int) (size : Int) : Unit :=
  ()

/-- Type quantifiers: processorid : Int, size : Int -/
def MarkExclusiveGlobal (paddress : FullAddress) (processorid : Int) (size : Int) : Unit :=
  ()

/-- Type quantifiers: processorid : Int, size : Int -/
def MarkExclusiveLocal (paddress : FullAddress) (processorid : Int) (size : Int) : Unit :=
  ()

/-- Type quantifiers: processorid : Int, size : Int -/
def AArch64_IsExclusiveVA (address : (BitVec 64)) (processorid : Int) (size : Int) : Bool :=
  true

/-- Type quantifiers: processorid : Int, size : Int -/
def IsExclusiveGlobal (paddress : FullAddress) (processorid : Int) (size : Int) : Bool :=
  true

/-- Type quantifiers: processorid : Int, size : Int -/
def IsExclusiveLocal (paddress : FullAddress) (processorid : Int) (size : Int) : Bool :=
  true

def SVEAccessTrap (target_el : (BitVec 2)) : SailM Unit := do
  sail_assert ((((BitVec.toNat target_el) ≥b (BitVec.toNat (← readReg PSTATE).EL)) && (target_el != EL0)) && (HaveEL target_el)) "src/v8_base.sail:29235.86-29235.87"
  let route_to_el2 ← (( do (pure (target_el == EL1)) <&&> (do (EL2Enabled ())) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))) ) : SailM Bool )
  let except ← (( do (ExceptionSyndrome Exception_SVEAccessTrap) ) : SailM ExceptionRecord )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  if (route_to_el2 : Bool)
  then (AArch64_TakeException EL2 except preferred_exception_return vect_offset)
  else (AArch64_TakeException target_el except preferred_exception_return vect_offset)

def SMEAccessTrap (etype : SMEExceptionType) (target_el_in : (BitVec 2)) : SailM Unit := do
  let target_el : (BitVec 2) := target_el_in
  sail_assert ((BitVec.toNat target_el) ≥b (BitVec.toNat (← readReg PSTATE).EL)) "src/v8_base.sail:29351.45-29351.46"
  let target_el : (BitVec 2) :=
    if ((target_el == EL0) : Bool)
    then EL1
    else target_el
  let route_to_el2 ← (( do (pure (((← readReg PSTATE).EL == EL0) && (target_el == EL1))) <&&> (do (EL2Enabled ())) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))) ) : SailM Bool )
  let except ← (( do (ExceptionSyndrome Exception_SMEAccessTrap) ) : SailM ExceptionRecord )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let except : ExceptionRecord :=
    match etype with
    | .SMEExceptionType_AccessTrap => { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 2 0 0b000#3) }
    | .SMEExceptionType_Streaming => { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 2 0 0b001#3) }
    | .SMEExceptionType_NotStreaming => { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 2 0 0b010#3) }
    | .SMEExceptionType_InactiveZA => { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 2 0 0b011#3) }
    | .SMEExceptionType_InaccessibleZT0 => { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 2 0 0b100#3) }
  if (route_to_el2 : Bool)
  then (AArch64_TakeException EL2 except preferred_exception_return vect_offset)
  else (AArch64_TakeException target_el except preferred_exception_return vect_offset)

def SetPSTATE_SM (value_name : (BitVec 1)) : SailM Unit := do
  if (((← readReg PSTATE).SM != value_name) : Bool)
  then
    (do
      (ResetSVEState ())
      writeReg PSTATE { (← readReg PSTATE) with SM := value_name })
  else (pure ())

/-- Type quantifiers: n : Int, width : Nat, width ≥ 0 -/
def Z_read (n : Int) (width : Nat) : SailM (BitVec width) := do
  let VL ← do (CurrentVL_read ())
  sail_assert ((n ≥b 0) && (n ≤b 31)) "src/v8_base.sail:29646.27-29646.28"
  sail_assert (width == VL) "src/v8_base.sail:29647.22-29647.23"
  (pure (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg _Z) n) (width -i 1) 0))

/-- Type quantifiers: n : Int, width : Nat, width ≥ 0 ∧ n < 16 ∨ (not (n ≥ 0 ∧ n ≤ 31)) -/
def P_read (n : Int) (width : Nat) : SailM (BitVec width) := do
  let VL ← do (CurrentVL_read ())
  sail_assert ((n ≥b 0) && (n ≤b 31)) "src/v8_base.sail:29657.27-29657.28"
  sail_assert (width == (Int.ediv VL 8)) "src/v8_base.sail:29658.30-29658.31"
  (pure (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg _P) n) (width -i 1) 0))

/-- Type quantifiers: width : Nat, width ≥ 0 -/
def FFR_read (width : Nat) : SailM (BitVec width) := do
  let VL ← do (CurrentVL_read ())
  sail_assert (width == (Int.ediv VL 8)) "src/v8_base.sail:29666.30-29666.31"
  (pure (Sail.BitVec.extractLsb (← readReg _FFR) (width -i 1) 0))

/-- Type quantifiers: k_aligned : Bool, size : Nat, size > 0 -/
def MemSingleNF_read (address : (BitVec 64)) (size : Nat) (accdesc_in : AccessDescriptor) (aligned : Bool) : SailM ((BitVec (8 * size)) × Bool) := SailME.run do
  sail_assert (BEq.beq accdesc_in.acctype AccessType_SVE) "src/v8_base.sail:29674.47-29674.48"
  sail_assert (accdesc_in.nonfault || (accdesc_in.firstfault && (! accdesc_in.first))) "src/v8_base.sail:29675.83-29675.84"
  let value_name ← (( do (undefined_bitvector (8 *i size)) ) : SailME ((BitVec (8 * size)) × Bool) (BitVec (8 * size)) )
  let memstatus ← (( do (undefined_PhysMemRetStatus ()) ) : SailME ((BitVec (8 * size)) × Bool) PhysMemRetStatus )
  let accdesc : AccessDescriptor := accdesc_in
  let fault ← (( do (NoFault__1 accdesc) ) : SailME ((BitVec (8 * size)) × Bool) FaultRecord )
  if ((← (ConstrainUnpredictableBool Unpredictable_NONFAULT)) : Bool)
  then (pure ((← (__UNKNOWN_bits (8 *i size))), true))
  else
    (do
      let accdesc ← (( do
        if (((← (HaveMTE2Ext ())) && accdesc.tagchecked) : Bool)
        then (do (pure { accdesc with tagchecked := ← (do (AArch64_AccessIsTagChecked address accdesc)) }))
        else (pure accdesc) ) : SailME ((BitVec (8 * size)) × Bool) AccessDescriptor )
      let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned size) ) : SailME ((BitVec (8 * size)) × Bool) AddressDescriptor )
      if ((BEq.beq memaddrdesc.memattrs.memtype MemType_Device) : Bool)
      then (pure ((← (__UNKNOWN_bits (8 *i size))), true))
      else
        (do
          if ((IsFault memaddrdesc) : Bool)
          then (pure ((← (__UNKNOWN_bits (8 *i size))), true))
          else
            (do
              if (((← (HaveMTE2Ext ())) && accdesc.tagchecked) : Bool)
              then
                (do
                  let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
                  if ((! (← (AArch64_CheckTag memaddrdesc accdesc ptag))) : Bool)
                  then SailME.throw (← (do (pure ((← (__UNKNOWN_bits (8 *i size))), true))))
                  else (pure ()))
              else (pure ())
              let (memstatus, value_name) ← (( do
                let (tup__0, tup__1) ← do (PhysMemRead memaddrdesc size accdesc none)
                let memstatus : PhysMemRetStatus := tup__0
                let value_name : (BitVec (8 * size)) := tup__1
                (pure (memstatus, value_name)) ) : SailME ((BitVec (8 * size)) × Bool) (PhysMemRetStatus × (BitVec (8 * size))) )
              if ((IsFault__2 memstatus) : Bool)
              then
                (do
                  let iswrite : Bool := false
                  if ((← (IsExternalAbortTakenSynchronously memstatus iswrite memaddrdesc size accdesc)) : Bool)
                  then SailME.throw (← (do (pure ((← (__UNKNOWN_bits (8 *i size))), true))))
                  else
                    (let fault : FaultRecord := { fault with merrorstate := memstatus.merrorstate }
                    let fault : FaultRecord := { fault with extflag := memstatus.extflag }
                    let fault : FaultRecord := { fault with statuscode := memstatus.statuscode }
                    (pure (PendSErrorInterrupt fault))))
              else (pure ())
              (pure (value_name, false)))))

/-- Type quantifiers: k_N : Nat, e : Int, esize : Int, k_N ≥ 0 -/
def ActivePredicateElement (pred : (BitVec k_N)) (e : Int) (esize : Int) : SailM Bool := do
  sail_assert ((esize == 8) || ((esize == 16) || ((esize == 32) || ((esize == 64) || (esize == 128))))) "src/v8_base.sail:29766.78-29766.79"
  let n := (e *i (Int.ediv esize 8))
  sail_assert ((n ≥b 0) && (n <b (Sail.BitVec.length pred))) "src/v8_base.sail:29768.26-29768.27"
  (pure ((BitVec.join1 [(BitVec.access pred n)]) == 1#1))

/-- Type quantifiers: k_N : Nat, e : Int, esize : Int, k_N ≥ 0 -/
def PredicateElement (pred : (BitVec k_N)) (e : Int) (esize : Int) : SailM (BitVec 1) := do
  sail_assert ((esize == 8) || ((esize == 16) || ((esize == 32) || ((esize == 64) || (esize == 128))))) "src/v8_base.sail:29776.78-29776.79"
  let n := (e *i (Int.ediv esize 8))
  sail_assert ((n ≥b 0) && (n <b (Sail.BitVec.length pred))) "src/v8_base.sail:29778.26-29778.27"
  (pure (BitVec.join1 [(BitVec.access pred n)]))

/-- Type quantifiers: e : Int, esize : Int -/
def ElemFFR_set (e : Int) (esize : Int) (value_name : (BitVec 1)) : SailM Unit := do
  let VL ← do (CurrentVL_read ())
  let psize := (fdiv_int esize 8)
  let n := (e *i psize)
  sail_assert ((n ≥b 0) && ((n +i psize) ≤b (Int.ediv VL 8))) "src/v8_base.sail:29836.43-29836.44"
  sail_assert (n ≤b ((n +i psize) -i 1)) "src/v8_base.sail:29837.44-29837.45"
  writeReg _FFR (Sail.BitVec.updateSubrange (← readReg _FFR) ((n +i psize) -i 1) n (Sail.BitVec.zeroExtend value_name psize))

/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPOne (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  sail_assert ((N == 16) || ((N == 32) || (N == 64))) "src/v8_base.sail:29918.38-29918.39"
  let E :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F := (N -i (E +i 1))
  let exp : (BitVec (1 + (E - 1))) := (0#1 +++ (Ones (n := (E -i 1))))
  let frac : (BitVec F) := (Zeros (n := F))
  (pure ((sign +++ exp) +++ frac))

/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPPointFive (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  sail_assert ((N == 16) || ((N == 32) || (N == 64))) "src/v8_base.sail:29929.38-29929.39"
  let E :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F := (N -i (E +i 1))
  let exp : (BitVec (1 + (E - 2) + 1)) := ((0#1 +++ (Ones (n := (E -i 2)))) +++ 0#1)
  let frac : (BitVec F) := (Zeros (n := F))
  (pure ((sign +++ exp) +++ frac))

/-- Type quantifiers: N : Nat, scale_in : Int, N ≥ 0 -/
def GetOptimizedScale (op : (BitVec k_N)) (scale_in : Int) (N : Nat) : Int :=
  let scale : Int := scale_in
  let scale : Int :=
    if ((N == 16) : Bool)
    then
      (let exp16 := (BitVec.toNat (Sail.BitVec.extractLsb op 14 10))
      let scale : Int :=
        if (((scale +i exp16) <b (Neg.neg 11)) : Bool)
        then ((Neg.neg 11) -i exp16)
        else scale
      if (((scale +i exp16) >b 43) : Bool)
      then (43 -i exp16)
      else scale)
    else
      (if ((N == 32) : Bool)
      then
        (let exp32 := (BitVec.toNat (Sail.BitVec.extractLsb op 30 23))
        let scale : Int :=
          if (((scale +i exp32) <b (Neg.neg 24)) : Bool)
          then ((Neg.neg 24) -i exp32)
          else scale
        if (((scale +i exp32) >b 280) : Bool)
        then (280 -i exp32)
        else scale)
      else
        (if ((N == 64) : Bool)
        then
          (let exp64 := (BitVec.toNat (Sail.BitVec.extractLsb op 62 52))
          let scale : Int :=
            if (((scale +i exp64) <b (Neg.neg 53)) : Bool)
            then ((Neg.neg 53) -i exp64)
            else scale
          if (((scale +i exp64) >b 2101) : Bool)
          then (2101 -i exp64)
          else scale)
        else scale))
  let scale := scale
  scale

/-- Type quantifiers: M : Int, k_N : Nat, k_N ≥ 0 -/
def Reverse (word : (BitVec k_N)) (M : Int) : SailM (BitVec k_N) := do
  let result ← (( do (undefined_bitvector (Sail.BitVec.length word)) ) : SailM (BitVec k_N) )
  let sw := (fdiv_int (Sail.BitVec.length word) M)
  sail_assert ((Sail.BitVec.length word) == (sw *i M)) "src/v8_base.sail:29989.23-29989.24"
  let loop_s_lower := 0
  let loop_s_upper := (sw -i 1)
  let mut loop_vars := result
  for s in [loop_s_lower:loop_s_upper:1]i do
    let result := loop_vars
    loop_vars ← do
      sail_assert (((s *i M) ≤b (((s *i M) +i M) -i 1)) || (! ((s ≥b 0) && (((s +i 1) *i M) ≤b (Sail.BitVec.length word))))) "src/v8_base.sail:29991.115-29991.116"
      (Elem_set result ((sw -i 1) -i s) M (← (Elem_read word s M)))
  (pure loop_vars)

/-- Type quantifiers: N : Nat, index : Int, List.elem N [16, 32, 64] -/
def FPTrigMAddCoefficient_read (index : Int) (N : Nat) : SailM (BitVec N) := do
  sail_assert ((N == 16) || ((N == 32) || (N == 64))) "src/v8_base.sail:30034.38-30034.39"
  let result ← (( do (undefined_int ()) ) : SailM Int )
  let result : Int :=
    if ((N == 16) : Bool)
    then
      (match index with
      | 0 => (BitVec.toNat 0x3C00#16)
      | 1 => (BitVec.toNat 0xB155#16)
      | 2 => (BitVec.toNat 0x2030#16)
      | 3 => (BitVec.toNat 0x0000#16)
      | 4 => (BitVec.toNat 0x0000#16)
      | 5 => (BitVec.toNat 0x0000#16)
      | 6 => (BitVec.toNat 0x0000#16)
      | 7 => (BitVec.toNat 0x0000#16)
      | 8 => (BitVec.toNat 0x3C00#16)
      | 9 => (BitVec.toNat 0xB800#16)
      | 10 => (BitVec.toNat 0x293A#16)
      | 11 => (BitVec.toNat 0x0000#16)
      | 12 => (BitVec.toNat 0x0000#16)
      | 13 => (BitVec.toNat 0x0000#16)
      | 14 => (BitVec.toNat 0x0000#16)
      | 15 => (BitVec.toNat 0x0000#16)
      | _ => result)
    else
      (if ((N == 32) : Bool)
      then
        (match index with
        | 0 => (BitVec.toNat 0x3F800000#32)
        | 1 => (BitVec.toNat 0xBE2AAAAB#32)
        | 2 => (BitVec.toNat 0x3C088886#32)
        | 3 => (BitVec.toNat 0xB95008B9#32)
        | 4 => (BitVec.toNat 0x36369D6D#32)
        | 5 => (BitVec.toNat 0x00000000#32)
        | 6 => (BitVec.toNat 0x00000000#32)
        | 7 => (BitVec.toNat 0x00000000#32)
        | 8 => (BitVec.toNat 0x3F800000#32)
        | 9 => (BitVec.toNat 0xBF000000#32)
        | 10 => (BitVec.toNat 0x3D2AAAA6#32)
        | 11 => (BitVec.toNat 0xBAB60705#32)
        | 12 => (BitVec.toNat 0x37CD37CC#32)
        | 13 => (BitVec.toNat 0x00000000#32)
        | 14 => (BitVec.toNat 0x00000000#32)
        | 15 => (BitVec.toNat 0x00000000#32)
        | _ => result)
      else
        (match index with
        | 0 => (BitVec.toNat 0x3FF0000000000000#64)
        | 1 => (BitVec.toNat 0xBFC5555555555543#64)
        | 2 => (BitVec.toNat 0x3F8111111110F30C#64)
        | 3 => (BitVec.toNat 0xBF2A01A019B92FC6#64)
        | 4 => (BitVec.toNat 0x3EC71DE351F3D22B#64)
        | 5 => (BitVec.toNat 0xBE5AE5E2B60F7B91#64)
        | 6 => (BitVec.toNat 0x3DE5D8408868552F#64)
        | 7 => (BitVec.toNat 0x0000000000000000#64)
        | 8 => (BitVec.toNat 0x3FF0000000000000#64)
        | 9 => (BitVec.toNat 0xBFE0000000000000#64)
        | 10 => (BitVec.toNat 0x3FA5555555555536#64)
        | 11 => (BitVec.toNat 0xBF56C16C16C13A0B#64)
        | 12 => (BitVec.toNat 0x3EFA01A019B1E8D8#64)
        | 13 => (BitVec.toNat 0xBE927E4F7282F468#64)
        | 14 => (BitVec.toNat 0x3E21EE96D2641B13#64)
        | 15 => (BitVec.toNat 0xBDA8F76380FBB401#64)
        | _ => result))
  let result := result
  (pure (integer_subrange result (N -i 1) 0))

/-- Type quantifiers: N : Nat, index : Int, List.elem N [16, 32, 64] -/
def FPExpCoefficient_read (index : Int) (N : Nat) : SailM (BitVec N) := do
  sail_assert ((N == 16) || ((N == 32) || (N == 64))) "src/v8_base.sail:30222.38-30222.39"
  let result ← (( do (undefined_int ()) ) : SailM Int )
  let result : Int :=
    if ((N == 16) : Bool)
    then
      (match index with
      | 0 => (BitVec.toNat 0x0000#16)
      | 1 => (BitVec.toNat 0x0016#16)
      | 2 => (BitVec.toNat 0x002D#16)
      | 3 => (BitVec.toNat 0x0045#16)
      | 4 => (BitVec.toNat 0x005D#16)
      | 5 => (BitVec.toNat 0x0075#16)
      | 6 => (BitVec.toNat 0x008E#16)
      | 7 => (BitVec.toNat 0x00A8#16)
      | 8 => (BitVec.toNat 0x00C2#16)
      | 9 => (BitVec.toNat 0x00DC#16)
      | 10 => (BitVec.toNat 0x00F8#16)
      | 11 => (BitVec.toNat 0x0114#16)
      | 12 => (BitVec.toNat 0x0130#16)
      | 13 => (BitVec.toNat 0x014D#16)
      | 14 => (BitVec.toNat 0x016B#16)
      | 15 => (BitVec.toNat 0x0189#16)
      | 16 => (BitVec.toNat 0x01A8#16)
      | 17 => (BitVec.toNat 0x01C8#16)
      | 18 => (BitVec.toNat 0x01E8#16)
      | 19 => (BitVec.toNat 0x0209#16)
      | 20 => (BitVec.toNat 0x022B#16)
      | 21 => (BitVec.toNat 0x024E#16)
      | 22 => (BitVec.toNat 0x0271#16)
      | 23 => (BitVec.toNat 0x0295#16)
      | 24 => (BitVec.toNat 0x02BA#16)
      | 25 => (BitVec.toNat 0x02E0#16)
      | 26 => (BitVec.toNat 0x0306#16)
      | 27 => (BitVec.toNat 0x032E#16)
      | 28 => (BitVec.toNat 0x0356#16)
      | 29 => (BitVec.toNat 0x037F#16)
      | 30 => (BitVec.toNat 0x03A9#16)
      | 31 => (BitVec.toNat 0x03D4#16)
      | _ => result)
    else
      (if ((N == 32) : Bool)
      then
        (match index with
        | 0 => (BitVec.toNat 0x000000#24)
        | 1 => (BitVec.toNat 0x0164D2#24)
        | 2 => (BitVec.toNat 0x02CD87#24)
        | 3 => (BitVec.toNat 0x043A29#24)
        | 4 => (BitVec.toNat 0x05AAC3#24)
        | 5 => (BitVec.toNat 0x071F62#24)
        | 6 => (BitVec.toNat 0x08980F#24)
        | 7 => (BitVec.toNat 0x0A14D5#24)
        | 8 => (BitVec.toNat 0x0B95C2#24)
        | 9 => (BitVec.toNat 0x0D1ADF#24)
        | 10 => (BitVec.toNat 0x0EA43A#24)
        | 11 => (BitVec.toNat 0x1031DC#24)
        | 12 => (BitVec.toNat 0x11C3D3#24)
        | 13 => (BitVec.toNat 0x135A2B#24)
        | 14 => (BitVec.toNat 0x14F4F0#24)
        | 15 => (BitVec.toNat 0x16942D#24)
        | 16 => (BitVec.toNat 0x1837F0#24)
        | 17 => (BitVec.toNat 0x19E046#24)
        | 18 => (BitVec.toNat 0x1B8D3A#24)
        | 19 => (BitVec.toNat 0x1D3EDA#24)
        | 20 => (BitVec.toNat 0x1EF532#24)
        | 21 => (BitVec.toNat 0x20B051#24)
        | 22 => (BitVec.toNat 0x227043#24)
        | 23 => (BitVec.toNat 0x243516#24)
        | 24 => (BitVec.toNat 0x25FED7#24)
        | 25 => (BitVec.toNat 0x27CD94#24)
        | 26 => (BitVec.toNat 0x29A15B#24)
        | 27 => (BitVec.toNat 0x2B7A3A#24)
        | 28 => (BitVec.toNat 0x2D583F#24)
        | 29 => (BitVec.toNat 0x2F3B79#24)
        | 30 => (BitVec.toNat 0x3123F6#24)
        | 31 => (BitVec.toNat 0x3311C4#24)
        | 32 => (BitVec.toNat 0x3504F3#24)
        | 33 => (BitVec.toNat 0x36FD92#24)
        | 34 => (BitVec.toNat 0x38FBAF#24)
        | 35 => (BitVec.toNat 0x3AFF5B#24)
        | 36 => (BitVec.toNat 0x3D08A4#24)
        | 37 => (BitVec.toNat 0x3F179A#24)
        | 38 => (BitVec.toNat 0x412C4D#24)
        | 39 => (BitVec.toNat 0x4346CD#24)
        | 40 => (BitVec.toNat 0x45672A#24)
        | 41 => (BitVec.toNat 0x478D75#24)
        | 42 => (BitVec.toNat 0x49B9BE#24)
        | 43 => (BitVec.toNat 0x4BEC15#24)
        | 44 => (BitVec.toNat 0x4E248C#24)
        | 45 => (BitVec.toNat 0x506334#24)
        | 46 => (BitVec.toNat 0x52A81E#24)
        | 47 => (BitVec.toNat 0x54F35B#24)
        | 48 => (BitVec.toNat 0x5744FD#24)
        | 49 => (BitVec.toNat 0x599D16#24)
        | 50 => (BitVec.toNat 0x5BFBB8#24)
        | 51 => (BitVec.toNat 0x5E60F5#24)
        | 52 => (BitVec.toNat 0x60CCDF#24)
        | 53 => (BitVec.toNat 0x633F89#24)
        | 54 => (BitVec.toNat 0x65B907#24)
        | 55 => (BitVec.toNat 0x68396A#24)
        | 56 => (BitVec.toNat 0x6AC0C7#24)
        | 57 => (BitVec.toNat 0x6D4F30#24)
        | 58 => (BitVec.toNat 0x6FE4BA#24)
        | 59 => (BitVec.toNat 0x728177#24)
        | 60 => (BitVec.toNat 0x75257D#24)
        | 61 => (BitVec.toNat 0x77D0DF#24)
        | 62 => (BitVec.toNat 0x7A83B3#24)
        | 63 => (BitVec.toNat 0x7D3E0C#24)
        | _ => result)
      else
        (match index with
        | 0 => (BitVec.toNat 0x0000000000000#52)
        | 1 => (BitVec.toNat 0x02C9A3E778061#52)
        | 2 => (BitVec.toNat 0x059B0D3158574#52)
        | 3 => (BitVec.toNat 0x0874518759BC8#52)
        | 4 => (BitVec.toNat 0x0B5586CF9890F#52)
        | 5 => (BitVec.toNat 0x0E3EC32D3D1A2#52)
        | 6 => (BitVec.toNat 0x11301D0125B51#52)
        | 7 => (BitVec.toNat 0x1429AAEA92DE0#52)
        | 8 => (BitVec.toNat 0x172B83C7D517B#52)
        | 9 => (BitVec.toNat 0x1A35BEB6FCB75#52)
        | 10 => (BitVec.toNat 0x1D4873168B9AA#52)
        | 11 => (BitVec.toNat 0x2063B88628CD6#52)
        | 12 => (BitVec.toNat 0x2387A6E756238#52)
        | 13 => (BitVec.toNat 0x26B4565E27CDD#52)
        | 14 => (BitVec.toNat 0x29E9DF51FDEE1#52)
        | 15 => (BitVec.toNat 0x2D285A6E4030B#52)
        | 16 => (BitVec.toNat 0x306FE0A31B715#52)
        | 17 => (BitVec.toNat 0x33C08B26416FF#52)
        | 18 => (BitVec.toNat 0x371A7373AA9CB#52)
        | 19 => (BitVec.toNat 0x3A7DB34E59FF7#52)
        | 20 => (BitVec.toNat 0x3DEA64C123422#52)
        | 21 => (BitVec.toNat 0x4160A21F72E2A#52)
        | 22 => (BitVec.toNat 0x44E086061892D#52)
        | 23 => (BitVec.toNat 0x486A2B5C13CD0#52)
        | 24 => (BitVec.toNat 0x4BFDAD5362A27#52)
        | 25 => (BitVec.toNat 0x4F9B2769D2CA7#52)
        | 26 => (BitVec.toNat 0x5342B569D4F82#52)
        | 27 => (BitVec.toNat 0x56F4736B527DA#52)
        | 28 => (BitVec.toNat 0x5AB07DD485429#52)
        | 29 => (BitVec.toNat 0x5E76F15AD2148#52)
        | 30 => (BitVec.toNat 0x6247EB03A5585#52)
        | 31 => (BitVec.toNat 0x6623882552225#52)
        | 32 => (BitVec.toNat 0x6A09E667F3BCD#52)
        | 33 => (BitVec.toNat 0x6DFB23C651A2F#52)
        | 34 => (BitVec.toNat 0x71F75E8EC5F74#52)
        | 35 => (BitVec.toNat 0x75FEB564267C9#52)
        | 36 => (BitVec.toNat 0x7A11473EB0187#52)
        | 37 => (BitVec.toNat 0x7E2F336CF4E62#52)
        | 38 => (BitVec.toNat 0x82589994CCE13#52)
        | 39 => (BitVec.toNat 0x868D99B4492ED#52)
        | 40 => (BitVec.toNat 0x8ACE5422AA0DB#52)
        | 41 => (BitVec.toNat 0x8F1AE99157736#52)
        | 42 => (BitVec.toNat 0x93737B0CDC5E5#52)
        | 43 => (BitVec.toNat 0x97D829FDE4E50#52)
        | 44 => (BitVec.toNat 0x9C49182A3F090#52)
        | 45 => (BitVec.toNat 0xA0C667B5DE565#52)
        | 46 => (BitVec.toNat 0xA5503B23E255D#52)
        | 47 => (BitVec.toNat 0xA9E6B5579FDBF#52)
        | 48 => (BitVec.toNat 0xAE89F995AD3AD#52)
        | 49 => (BitVec.toNat 0xB33A2B84F15FB#52)
        | 50 => (BitVec.toNat 0xB7F76F2FB5E47#52)
        | 51 => (BitVec.toNat 0xBCC1E904BC1D2#52)
        | 52 => (BitVec.toNat 0xC199BDD85529C#52)
        | 53 => (BitVec.toNat 0xC67F12E57D14B#52)
        | 54 => (BitVec.toNat 0xCB720DCEF9069#52)
        | 55 => (BitVec.toNat 0xD072D4A07897C#52)
        | 56 => (BitVec.toNat 0xD5818DCFBA487#52)
        | 57 => (BitVec.toNat 0xDA9E603DB3285#52)
        | 58 => (BitVec.toNat 0xDFC97337B9B5F#52)
        | 59 => (BitVec.toNat 0xE502EE78B3FF6#52)
        | 60 => (BitVec.toNat 0xEA4AFA2A490DA#52)
        | 61 => (BitVec.toNat 0xEFA1BEE615A27#52)
        | 62 => (BitVec.toNat 0xF50765B6E4540#52)
        | 63 => (BitVec.toNat 0xFA7C1819E90D8#52)
        | _ => result))
  let result := result
  (pure (integer_subrange result (N -i 1) 0))

/-- Type quantifiers: esize : Int -/
def DecodePredCount (pattern : (BitVec 5)) (esize : Int) : SailM Int := do
  let VL ← do (CurrentVL_read ())
  let elements := (fdiv_int VL esize)
  let numElem ← (( do (undefined_int ()) ) : SailM Int )
  let numElem ← (( do
    match (pattern : BitVec 5) with
    | 0b00000 => (do (FloorPow2 elements))
    | 0b00001 =>
      (if ((elements ≥b 1) : Bool)
      then (pure 1)
      else (pure 0))
    | 0b00010 =>
      (if ((elements ≥b 2) : Bool)
      then (pure 2)
      else (pure 0))
    | 0b00011 =>
      (if ((elements ≥b 3) : Bool)
      then (pure 3)
      else (pure 0))
    | 0b00100 =>
      (if ((elements ≥b 4) : Bool)
      then (pure 4)
      else (pure 0))
    | 0b00101 =>
      (if ((elements ≥b 5) : Bool)
      then (pure 5)
      else (pure 0))
    | 0b00110 =>
      (if ((elements ≥b 6) : Bool)
      then (pure 6)
      else (pure 0))
    | 0b00111 =>
      (if ((elements ≥b 7) : Bool)
      then (pure 7)
      else (pure 0))
    | 0b01000 =>
      (if ((elements ≥b 8) : Bool)
      then (pure 8)
      else (pure 0))
    | 0b01001 =>
      (if ((elements ≥b 16) : Bool)
      then (pure 16)
      else (pure 0))
    | 0b01010 =>
      (if ((elements ≥b 32) : Bool)
      then (pure 32)
      else (pure 0))
    | 0b01011 =>
      (if ((elements ≥b 64) : Bool)
      then (pure 64)
      else (pure 0))
    | 0b01100 =>
      (if ((elements ≥b 128) : Bool)
      then (pure 128)
      else (pure 0))
    | 0b01101 =>
      (if ((elements ≥b 256) : Bool)
      then (pure 256)
      else (pure 0))
    | 0b11101 => (pure (elements -i (fmod_int elements 4)))
    | 0b11110 => (pure (elements -i (fmod_int elements 3)))
    | 0b11111 => (pure elements)
    | _ => (pure 0) ) : SailM Int )
  let numElem := numElem
  (pure numElem)

/-- Type quantifiers: M : Nat, k_immediate : Bool, M ≥ 0 -/
def DecodeBitMasks (immN : (BitVec 1)) (imms : (BitVec 6)) (immr : (BitVec 6)) (immediate : Bool) (M : Nat) : SailM ((BitVec M) × (BitVec M)) := do
  let len := (HighestSetBit (immN +++ (Complement.complement imms)))
  if ((len <b 1) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  sail_assert (M ≥b (Int.shiftl 1 len)) "src/v8_base.sail:30900.26-30900.27"
  sail_assert (6 ≥b len) "src/v8_base.sail:30901.32-30901.33"
  let levels : (BitVec 6) := (Sail.BitVec.zeroExtend (Ones (n := len)) 6)
  if ((immediate && ((imms &&& levels) == levels)) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let s := (BitVec.toNat (imms &&& levels))
  let r := (BitVec.toNat (immr &&& levels))
  let diff := (s -i r)
  let esize := (Int.shiftl 1 len)
  let d := (BitVec.toNat (integer_subrange diff (len -i 1) 0))
  sail_assert (esize ≥b (s +i 1)) "src/v8_base.sail:30911.39-30911.40"
  let welem : (BitVec esize) := (Sail.BitVec.zeroExtend (Ones (n := (s +i 1))) esize)
  sail_assert (esize ≥b (d +i 1)) "src/v8_base.sail:30913.39-30913.40"
  let telem : (BitVec esize) := (Sail.BitVec.zeroExtend (Ones (n := (d +i 1))) esize)
  sail_assert ((esize *i (Int.ediv M esize)) == M) "src/v8_base.sail:30915.53-30915.54"
  let wmask : (BitVec M) := (BitVec.replicateBits (ROR welem r) (Int.ediv M esize))
  let tmask : (BitVec M) := (BitVec.replicateBits telem (Int.ediv M esize))
  (pure (wmask, tmask))

/-- Type quantifiers: val_name : Int -/
def IsEven (val_name : Int) : Bool :=
  ((fmod_int val_name 2) == 0)

/-- Type quantifiers: esize : Int, shift : Int -/
def ShiftSat (shift : Int) (esize : Int) : Int :=
  if ((shift >b (esize +i 1)) : Bool)
  then (esize +i 1)
  else
    (if ((shift <b (Neg.neg (esize +i 1))) : Bool)
    then (Neg.neg (esize +i 1))
    else shift)

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def BitDeposit (data : (BitVec k_N)) (mask : (BitVec k_N)) : SailM (BitVec k_N) := do
  let res : (BitVec k_N) := (Zeros (n := (Sail.BitVec.length mask)))
  let db : Int := 0
  let (db, res) ← (( do
    let loop_rb_lower := 0
    let loop_rb_upper := ((Sail.BitVec.length res) -i 1)
    let mut loop_vars := (db, res)
    for rb in [loop_rb_lower:loop_rb_upper:1]i do
      let (db, res) := loop_vars
      loop_vars ← do
        let (db, res) ← (( do
          if (((BitVec.join1 [(BitVec.access mask rb)]) == 1#1) : Bool)
          then
            (do
              let res ← (( do
                let db := db
                sail_assert ((0 ≤b db) && (db <b (Sail.BitVec.length res))) "src/v8_base.sail:31027.58-31027.59"
                (pure (BitVec.update res rb (Bit (BitVec.join1 [(BitVec.access data db)])))) ) : SailM (BitVec k_N) )
              let db : Int := (db +i 1)
              (pure (db, res)))
          else (pure (db, res)) ) : SailM (Int × (BitVec k_N)) )
        (pure (db, res))
    (pure loop_vars) ) : SailM (Int × (BitVec k_N)) )
  (pure res)

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def BitExtract (data : (BitVec k_N)) (mask : (BitVec k_N)) : SailM (BitVec k_N) := do
  let res : (BitVec k_N) := (Zeros (n := (Sail.BitVec.length mask)))
  let rb : Int := 0
  let (rb, res) ← (( do
    let loop_db_lower := 0
    let loop_db_upper := ((Sail.BitVec.length res) -i 1)
    let mut loop_vars := (rb, res)
    for db in [loop_db_lower:loop_db_upper:1]i do
      let (rb, res) := loop_vars
      loop_vars ← do
        let (rb, res) ← (( do
          if (((BitVec.join1 [(BitVec.access mask db)]) == 1#1) : Bool)
          then
            (do
              let res ← (( do
                let rb := rb
                sail_assert ((0 ≤b rb) && (rb <b (Sail.BitVec.length res))) "src/v8_base.sail:31046.58-31046.59"
                (pure (BitVec.update res rb (Bit (BitVec.join1 [(BitVec.access data db)])))) ) : SailM (BitVec k_N) )
              let rb : Int := (rb +i 1)
              (pure (rb, res)))
          else (pure (rb, res)) ) : SailM (Int × (BitVec k_N)) )
        (pure (rb, res))
    (pure loop_vars) ) : SailM (Int × (BitVec k_N)) )
  (pure res)

/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def BitGroup (data : (BitVec k_N)) (mask : (BitVec k_N)) : SailM (BitVec k_N) := do
  let res ← (( do (undefined_bitvector (Sail.BitVec.length mask)) ) : SailM (BitVec k_N) )
  let rb : Int := 0
  let (rb, res) ← (( do
    let loop_db_lower := 0
    let loop_db_upper := ((Sail.BitVec.length res) -i 1)
    let mut loop_vars := (rb, res)
    for db in [loop_db_lower:loop_db_upper:1]i do
      let (rb, res) := loop_vars
      loop_vars ← do
        let (rb, res) ← (( do
          if (((BitVec.join1 [(BitVec.access mask db)]) == 1#1) : Bool)
          then
            (do
              let res ← (( do
                let rb := rb
                sail_assert ((0 ≤b rb) && (rb <b (Sail.BitVec.length res))) "src/v8_base.sail:31065.58-31065.59"
                (pure (BitVec.update res rb (Bit (BitVec.join1 [(BitVec.access data db)])))) ) : SailM (BitVec k_N) )
              let rb : Int := (rb +i 1)
              (pure (rb, res)))
          else (pure (rb, res)) ) : SailM (Int × (BitVec k_N)) )
        (pure (rb, res))
    (pure loop_vars) ) : SailM (Int × (BitVec k_N)) )
  let (rb, res) ← (( do
    let loop_db_lower := 0
    let loop_db_upper := ((Sail.BitVec.length res) -i 1)
    let mut loop_vars_1 := (rb, res)
    for db in [loop_db_lower:loop_db_upper:1]i do
      let (rb, res) := loop_vars_1
      loop_vars_1 ← do
        let (rb, res) ← (( do
          if (((BitVec.join1 [(BitVec.access mask db)]) == 0#1) : Bool)
          then
            (do
              let res ← (( do
                let rb := rb
                sail_assert ((0 ≤b rb) && (rb <b (Sail.BitVec.length res))) "src/v8_base.sail:31076.58-31076.59"
                (pure (BitVec.update res rb (Bit (BitVec.join1 [(BitVec.access data db)])))) ) : SailM (BitVec k_N) )
              let rb : Int := (rb +i 1)
              (pure (rb, res)))
          else (pure (rb, res)) ) : SailM (Int × (BitVec k_N)) )
        (pure (rb, res))
    (pure loop_vars_1) ) : SailM (Int × (BitVec k_N)) )
  (pure res)

/-- Type quantifiers: index : Int, width : Nat, width ≥ 0 -/
def ZAvector_read (index : Int) (width : Nat) : SailM (BitVec width) := do
  let SVL ← do (CurrentSVL_read ())
  sail_assert (width == SVL) "src/v8_base.sail:31134.23-31134.24"
  sail_assert ((index ≥b 0) && (index <b (Int.ediv width 8))) "src/v8_base.sail:31135.45-31135.46"
  (pure (Sail.BitVec.extractLsb (GetElem?.getElem! (← readReg _ZA) index) (width -i 1) 0))

/-- Type quantifiers: index : Int, width : Nat, width ≥ 0 -/
def ZAvector_set (index : Int) (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  let SVL ← do (CurrentSVL_read ())
  sail_assert (width == SVL) "src/v8_base.sail:31144.23-31144.24"
  sail_assert ((index ≥b 0) && (index <b (Int.ediv width 8))) "src/v8_base.sail:31145.45-31145.46"
  if ((← (ConstrainUnpredictableBool Unpredictable_SMEZEROUPPER)) : Bool)
  then writeReg _ZA (vectorUpdate (← readReg _ZA) index (Sail.BitVec.zeroExtend value_name MAX_VL))
  else writeReg _ZA (vectorUpdate (← readReg _ZA) index (Sail.BitVec.updateSubrange (GetElem?.getElem! (← readReg _ZA) index) (width -i 1) 0 value_name))

/-- Type quantifiers: width : Nat, width = 512 -/
def ZT0_read (width : Nat) : SailM (BitVec width) := do
  sail_assert (width == 512) "src/v8_base.sail:31298.23-31298.24"
  (pure (Sail.BitVec.extractLsb (← readReg _ZT0) (width -i 1) 0))

/-- Type quantifiers: width : Nat, width = 512 -/
def ZT0_set (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  sail_assert (width == 512) "src/v8_base.sail:31305.23-31305.24"
  writeReg _ZT0 (Sail.BitVec.updateSubrange (← readReg _ZT0) (width -i 1) 0 value_name)

/-- Type quantifiers: width : Nat, width ≥ 0 -/
def CounterToPredicate (pred : (BitVec 16)) (width : Nat) : SailM (BitVec width) := do
  let VL ← do (CurrentVL_read ())
  let count ← (( do (undefined_int ()) ) : SailM Int )
  let esize : Nat := 8
  let VL := VL
  let PL := (Int.ediv VL 8)
  let maxbit ← do (pure (HighestSetBit (integer_subrange (← (CeilPow2 (PL *i 4))) 15 0)))
  sail_assert (maxbit ≤b 14) "src/v8_base.sail:31319.23-31319.24"
  let invert : Bool := ((BitVec.join1 [(BitVec.access pred 15)]) == 1#1)
  sail_assert ((((width == PL) || (width == (PL *i 2))) || (width == (PL *i 3))) || (width == (PL *i 4))) "src/v8_base.sail:31321.80-31321.81"
  if ((IsZero (Sail.BitVec.extractLsb pred 3 0)) : Bool)
  then (pure (Zeros (n := width)))
  else
    (do
      let (count, esize) ← (( do
        let b__0 := (Sail.BitVec.extractLsb pred 3 0)
        let (count, esize) ← (( do
          if (((Sail.BitVec.extractLsb b__0 0 0) == (1#1 : (BitVec 1))) : Bool)
          then
            (do
              sail_assert ((1 ≤b maxbit) && (maxbit <b 16)) "src/v8_base.sail:31327.58-31327.59"
              let count : Int := (BitVec.toNat (Sail.BitVec.extractLsb pred maxbit 1))
              let esize : Nat := 8
              (pure (count, esize)))
          else
            (do
              let (count, esize) ← (( do
                if (((Sail.BitVec.extractLsb b__0 1 0) == (0b10#2 : (BitVec 2))) : Bool)
                then
                  (do
                    sail_assert ((2 ≤b maxbit) && (maxbit <b 16)) "src/v8_base.sail:31332.58-31332.59"
                    let count : Int := (BitVec.toNat (Sail.BitVec.extractLsb pred maxbit 2))
                    let esize : Nat := 16
                    (pure (count, esize)))
                else
                  (do
                    let (count, esize) ← (( do
                      if (((Sail.BitVec.extractLsb b__0 2 0) == (0b100#3 : (BitVec 3))) : Bool)
                      then
                        (do
                          sail_assert ((3 ≤b maxbit) && (maxbit <b 16)) "src/v8_base.sail:31337.58-31337.59"
                          let count : Int := (BitVec.toNat (Sail.BitVec.extractLsb pred maxbit 3))
                          let esize : Nat := 32
                          (pure (count, esize)))
                      else
                        (do
                          let (count, esize) ← (( do
                            if ((b__0 == (0x8#4 : (BitVec 4))) : Bool)
                            then
                              (do
                                sail_assert ((4 ≤b maxbit) && (maxbit <b 16)) "src/v8_base.sail:31342.58-31342.59"
                                let count : Int := (BitVec.toNat (Sail.BitVec.extractLsb pred maxbit 4))
                                let esize : Nat := 64
                                (pure (count, esize)))
                            else (pure (count, esize)) ) : SailM (Int × Int) )
                          (pure (count, esize))) ) : SailM (Int × Int) )
                    (pure (count, esize))) ) : SailM (Int × Int) )
              (pure (count, esize))) ) : SailM (Int × Int) )
        (pure (count, esize)) ) : SailM (Int × Int) )
      let esize := esize
      let count := count
      let elements := (Int.ediv (VL *i 4) esize)
      let result : (BitVec (PL * 4)) := (Zeros (n := (PL *i 4)))
      let psize := (Int.ediv esize 8)
      let result ← (( do
        let loop_e_lower := 0
        let loop_e_upper := (elements -i 1)
        let mut loop_vars := result
        for e in [loop_e_lower:loop_e_upper:1]i do
          let result := loop_vars
          loop_vars ← do
            let pbit : (BitVec 1) :=
              if ((e <b count) : Bool)
              then 1#1
              else 0#1
            let pbit : (BitVec 1) :=
              if (invert : Bool)
              then (Complement.complement pbit)
              else pbit
            (Elem_set result e psize (Sail.BitVec.zeroExtend pbit psize))
        (pure loop_vars) ) : SailM (BitVec (PL * 4)) )
      (pure (Sail.BitVec.extractLsb result (width -i 1) 0)))

/-- Type quantifiers: count_in : Int, elements : Int, esize : Int, k_invert_in : Bool, width : Nat, width ≥ 0 -/
def EncodePredCount (esize : Int) (elements : Int) (count_in : Int) (invert_in : Bool) (width : Nat) : SailM (BitVec width) := do
  let VL ← do (CurrentVL_read ())
  let count : Int := count_in
  let invert : Bool := invert_in
  let PL := (Int.ediv VL 8)
  sail_assert (width == PL) "src/v8_base.sail:31372.22-31372.23"
  sail_assert ((esize == 8) || ((esize == 16) || ((esize == 32) || (esize == 64)))) "src/v8_base.sail:31373.63-31373.64"
  sail_assert ((count ≥b 0) && (count ≤b elements)) "src/v8_base.sail:31374.41-31374.42"
  let pred ← (( do (undefined_bitvector 16) ) : SailM (BitVec 16) )
  if ((count == 0) : Bool)
  then (pure (Zeros (n := width)))
  else
    (let (count, invert) : (Int × Bool) :=
      if (invert : Bool)
      then
        (let count : Int := (elements -i count)
        (count, invert))
      else
        (let (count, invert) : (Int × Bool) :=
          if ((count == elements) : Bool)
          then
            (let count : Int := 0
            let invert : Bool := true
            (count, invert))
          else (count, invert)
        (count, invert))
    let count := count
    let inv : (BitVec 1) :=
      if (invert : Bool)
      then 1#1
      else 0#1
    let pred : (BitVec 16) :=
      match esize with
      | 8 => ((inv +++ (integer_subrange count 13 0)) +++ 1#1)
      | 16 => ((inv +++ (integer_subrange count 12 0)) +++ 0b10#2)
      | 32 => ((inv +++ (integer_subrange count 11 0)) +++ 0b100#3)
      | 64 => ((inv +++ (integer_subrange count 10 0)) +++ 0b1000#4)
      | _ => pred
    (pure (Sail.BitVec.zeroExtend pred width)))

/-- Type quantifiers: count : Int, elements : Int, k_invert : Bool -/
def PredCountTest (elements : Int) (count : Int) (invert : Bool) : SailM (BitVec 4) := do
  let c ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let n ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let z : (BitVec 1) :=
    if ((count == 0) : Bool)
    then 1#1
    else 0#1
  let (c, n) : ((BitVec 1) × (BitVec 1)) :=
    if ((! invert) : Bool)
    then
      (let n : (BitVec 1) :=
        if ((count != 0) : Bool)
        then 1#1
        else 0#1
      let c : (BitVec 1) :=
        if ((count == elements) : Bool)
        then 0#1
        else 1#1
      (c, n))
    else
      (let n : (BitVec 1) :=
        if ((count == elements) : Bool)
        then 1#1
        else 0#1
      let c : (BitVec 1) :=
        if ((count != 0) : Bool)
        then 0#1
        else 1#1
      (c, n))
  let v : (BitVec 1) := 0#1
  (pure (((n +++ z) +++ c) +++ v))

def GCSSynchronizationBarrier (_ : Unit) : Unit :=
  ()

def AddGCSExRecord (elr : (BitVec 64)) (spsr : (BitVec 64)) (lr : (BitVec 64)) : SailM Unit := do
  let accdesc ← (( do (CreateAccDescGCS (← readReg PSTATE).EL MemOp_STORE) ) : SailM AccessDescriptor )
  let ptr ← (( do (GetCurrentGCSPointer ()) ) : SailM (BitVec 64) )
  (Mem_set (BitVec.subInt ptr 8) 8 accdesc lr)
  (Mem_set (BitVec.subInt ptr 16) 8 accdesc spsr)
  (Mem_set (BitVec.subInt ptr 24) 8 accdesc elr)
  (Mem_set (BitVec.subInt ptr 32) 8 accdesc ((Zeros (n := 60)) +++ 0b1001#4))
  let ptr : (BitVec 64) := (BitVec.subInt ptr 32)
  (SetCurrentGCSPointer ptr)

def CheckGCSExRecord (elr : (BitVec 64)) (spsr : (BitVec 64)) (lr : (BitVec 64)) (gcsinst_type : GCSInstruction) : SailM Unit := do
  let accdesc ← (( do (CreateAccDescGCS (← readReg PSTATE).EL MemOp_LOAD) ) : SailM AccessDescriptor )
  let ptr ← (( do (GetCurrentGCSPointer ()) ) : SailM (BitVec 64) )
  let recorded_first_dword ← (( do (Mem_read ptr 8 accdesc) ) : SailM (BitVec 64) )
  if ((recorded_first_dword != ((Zeros (n := 60)) +++ 0b1001#4)) : Bool)
  then (GCSDataCheckException gcsinst_type)
  else (pure ())
  let recorded_elr ← (( do (Mem_read (BitVec.addInt ptr 8) 8 accdesc) ) : SailM (BitVec 64) )
  if ((recorded_elr != elr) : Bool)
  then (GCSDataCheckException gcsinst_type)
  else (pure ())
  let recorded_spsr ← (( do (Mem_read (BitVec.addInt ptr 16) 8 accdesc) ) : SailM (BitVec 64) )
  if ((recorded_spsr != spsr) : Bool)
  then (GCSDataCheckException gcsinst_type)
  else (pure ())
  let recorded_lr ← (( do (Mem_read (BitVec.addInt ptr 24) 8 accdesc) ) : SailM (BitVec 64) )
  if ((recorded_lr != lr) : Bool)
  then (GCSDataCheckException gcsinst_type)
  else (pure ())
  let ptr : (BitVec 64) := (BitVec.addInt ptr 32)
  (SetCurrentGCSPointer ptr)

def EXLOCKException (_ : Unit) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_GCSFail) ) : SailM ExceptionRecord )
  let except : ExceptionRecord := { except with syndrome := (BitVec.update except.syndrome 24 (Bit (Zeros (n := 1)))) }
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 23 20 0b0001#4) }
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 19 0 (Zeros (n := 20))) }
  (AArch64_TakeException (← readReg PSTATE).EL except preferred_exception_return vect_offset)

def GCSSTRTrapException (target_el : (BitVec 2)) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_GCSFail) ) : SailM ExceptionRecord )
  let except : ExceptionRecord := { except with syndrome := (BitVec.update except.syndrome 24 (Bit (Zeros (n := 1)))) }
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 23 20 0b0010#4) }
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 19 15 (Zeros (n := 5))) }
  let except ← (pure { except with syndrome := ← (do (pure (Sail.BitVec.updateSubrange except.syndrome 14 10 (Sail.BitVec.extractLsb (← (ThisInstr ())) 9 5)))) })
  let except ← (pure { except with syndrome := ← (do (pure (Sail.BitVec.updateSubrange except.syndrome 9 5 (Sail.BitVec.extractLsb (← (ThisInstr ())) 4 0)))) })
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 0 (Zeros (n := 5))) }
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)

def GCSPUSHM (value_name : (BitVec 64)) : SailM Unit := do
  if ((! (← (GCSEnabled (← readReg PSTATE).EL))) : Bool)
  then (EndOfInstruction ())
  else (pure ())
  (AddGCSRecord value_name)

def GCSPOPM (_ : Unit) : SailM (BitVec 64) := do
  let accdesc ← (( do (CreateAccDescGCS (← readReg PSTATE).EL MemOp_LOAD) ) : SailM AccessDescriptor )
  if ((! (← (GCSEnabled (← readReg PSTATE).EL))) : Bool)
  then (EndOfInstruction ())
  else (pure ())
  let ptr ← (( do (GetCurrentGCSPointer ()) ) : SailM (BitVec 64) )
  let entry ← (( do (Mem_read ptr 8 accdesc) ) : SailM (BitVec 64) )
  if (((Sail.BitVec.extractLsb entry 1 0) != 0b00#2) : Bool)
  then (GCSDataCheckException GCSInstType_POPM)
  else (pure ())
  let ptr : (BitVec 64) := (BitVec.addInt ptr 8)
  (SetCurrentGCSPointer ptr)
  (pure entry)

def GCSPOPX (_ : Unit) : SailM Unit := do
  if ((! (← (GCSEnabled (← readReg PSTATE).EL))) : Bool)
  then (EndOfInstruction ())
  else (pure ())
  let accdesc ← (( do (CreateAccDescGCS (← readReg PSTATE).EL MemOp_LOAD) ) : SailM AccessDescriptor )
  let ptr ← (( do (GetCurrentGCSPointer ()) ) : SailM (BitVec 64) )
  let recorded_first_dword ← (( do (Mem_read ptr 8 accdesc) ) : SailM (BitVec 64) )
  if ((recorded_first_dword != ((Zeros (n := 60)) +++ 0b1001#4)) : Bool)
  then (GCSDataCheckException GCSInstType_POPX)
  else (pure ())
  let recorded_elr ← (( do (Mem_read (BitVec.addInt ptr 8) 8 accdesc) ) : SailM (BitVec 64) )
  let recorded_spsr ← (( do (Mem_read (BitVec.addInt ptr 16) 8 accdesc) ) : SailM (BitVec 64) )
  let recorded_lr ← (( do (Mem_read (BitVec.addInt ptr 24) 8 accdesc) ) : SailM (BitVec 64) )
  let ptr : (BitVec 64) := (BitVec.addInt ptr 32)
  (SetCurrentGCSPointer ptr)

def undefined_HFGITR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_HFGITR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_HFGITR_EL2_Type_ATS1E0R (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_HFGITR_EL2_Type_ATS1E0R (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_HFGITR_EL2_Type_ATS1E0W (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_HFGITR_EL2_Type_ATS1E0W (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_HFGITR_EL2_Type_ATS1E1R (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_HFGITR_EL2_Type_ATS1E1R (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_HFGITR_EL2_Type_ATS1E1RP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_HFGITR_EL2_Type_ATS1E1RP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_HFGITR_EL2_Type_ATS1E1W (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_HFGITR_EL2_Type_ATS1E1W (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_HFGITR_EL2_Type_ATS1E1WP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_HFGITR_EL2_Type_ATS1E1WP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_HFGITR_EL2_Type_CFPRCTX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _update_HFGITR_EL2_Type_CFPRCTX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _get_HFGITR_EL2_Type_COSPRCTX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _update_HFGITR_EL2_Type_COSPRCTX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _get_HFGITR_EL2_Type_CPPRCTX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)

def _update_HFGITR_EL2_Type_CPPRCTX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _get_HFGITR_EL2_Type_DCCISW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_HFGITR_EL2_Type_DCCISW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_HFGITR_EL2_Type_DCCIVAC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_HFGITR_EL2_Type_DCCIVAC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_HFGITR_EL2_Type_DCCSW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_HFGITR_EL2_Type_DCCSW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_HFGITR_EL2_Type_DCCVAC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)

def _update_HFGITR_EL2_Type_DCCVAC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _get_HFGITR_EL2_Type_DCCVADP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_HFGITR_EL2_Type_DCCVADP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_HFGITR_EL2_Type_DCCVAP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_HFGITR_EL2_Type_DCCVAP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_HFGITR_EL2_Type_DCCVAU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_HFGITR_EL2_Type_DCCVAU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_HFGITR_EL2_Type_DCISW (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_HFGITR_EL2_Type_DCISW (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_HFGITR_EL2_Type_DCIVAC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_HFGITR_EL2_Type_DCIVAC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_HFGITR_EL2_Type_DCZVA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_HFGITR_EL2_Type_DCZVA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_HFGITR_EL2_Type_DVPRCTX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)

def _update_HFGITR_EL2_Type_DVPRCTX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def _get_HFGITR_EL2_Type_ERET (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 51 51)

def _update_HFGITR_EL2_Type_ERET (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)

def _get_HFGITR_EL2_Type_ICIALLU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_HFGITR_EL2_Type_ICIALLU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_HFGITR_EL2_Type_ICIALLUIS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_HFGITR_EL2_Type_ICIALLUIS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_HFGITR_EL2_Type_ICIVAU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_HFGITR_EL2_Type_ICIVAU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_HFGITR_EL2_Type_SVC_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)

def _update_HFGITR_EL2_Type_SVC_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _get_HFGITR_EL2_Type_SVC_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)

def _update_HFGITR_EL2_Type_SVC_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _get_HFGITR_EL2_Type_TLBIASIDE1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)

def _update_HFGITR_EL2_Type_TLBIASIDE1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _get_HFGITR_EL2_Type_TLBIASIDE1IS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_HFGITR_EL2_Type_TLBIASIDE1IS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_HFGITR_EL2_Type_TLBIASIDE1OS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_HFGITR_EL2_Type_TLBIASIDE1OS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_HFGITR_EL2_Type_TLBIRVAAE1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 39 39)

def _update_HFGITR_EL2_Type_TLBIRVAAE1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)

def _get_HFGITR_EL2_Type_TLBIRVAAE1IS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)

def _update_HFGITR_EL2_Type_TLBIRVAAE1IS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _get_HFGITR_EL2_Type_TLBIRVAAE1OS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_HFGITR_EL2_Type_TLBIRVAAE1OS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_HFGITR_EL2_Type_TLBIRVAALE1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)

def _update_HFGITR_EL2_Type_TLBIRVAALE1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _get_HFGITR_EL2_Type_TLBIRVAALE1IS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)

def _update_HFGITR_EL2_Type_TLBIRVAALE1IS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _get_HFGITR_EL2_Type_TLBIRVAALE1OS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_HFGITR_EL2_Type_TLBIRVAALE1OS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_HFGITR_EL2_Type_TLBIRVAE1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)

def _update_HFGITR_EL2_Type_TLBIRVAE1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _get_HFGITR_EL2_Type_TLBIRVAE1IS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)

def _update_HFGITR_EL2_Type_TLBIRVAE1IS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _get_HFGITR_EL2_Type_TLBIRVAE1OS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_HFGITR_EL2_Type_TLBIRVAE1OS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_HFGITR_EL2_Type_TLBIRVALE1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)

def _update_HFGITR_EL2_Type_TLBIRVALE1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _get_HFGITR_EL2_Type_TLBIRVALE1IS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)

def _update_HFGITR_EL2_Type_TLBIRVALE1IS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _get_HFGITR_EL2_Type_TLBIRVALE1OS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_HFGITR_EL2_Type_TLBIRVALE1OS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_HFGITR_EL2_Type_TLBIVAAE1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)

def _update_HFGITR_EL2_Type_TLBIVAAE1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _get_HFGITR_EL2_Type_TLBIVAAE1IS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_HFGITR_EL2_Type_TLBIVAAE1IS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_HFGITR_EL2_Type_TLBIVAAE1OS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_HFGITR_EL2_Type_TLBIVAAE1OS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_HFGITR_EL2_Type_TLBIVAALE1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 47 47)

def _update_HFGITR_EL2_Type_TLBIVAALE1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 47 x)

def _get_HFGITR_EL2_Type_TLBIVAALE1IS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _update_HFGITR_EL2_Type_TLBIVAALE1IS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _get_HFGITR_EL2_Type_TLBIVAALE1OS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_HFGITR_EL2_Type_TLBIVAALE1OS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_HFGITR_EL2_Type_TLBIVAE1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)

def _update_HFGITR_EL2_Type_TLBIVAE1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _get_HFGITR_EL2_Type_TLBIVAE1IS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_HFGITR_EL2_Type_TLBIVAE1IS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_HFGITR_EL2_Type_TLBIVAE1OS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_HFGITR_EL2_Type_TLBIVAE1OS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_HFGITR_EL2_Type_TLBIVALE1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)

def _update_HFGITR_EL2_Type_TLBIVALE1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _get_HFGITR_EL2_Type_TLBIVALE1IS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _update_HFGITR_EL2_Type_TLBIVALE1IS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _get_HFGITR_EL2_Type_TLBIVALE1OS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_HFGITR_EL2_Type_TLBIVALE1OS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_HFGITR_EL2_Type_TLBIVMALLE1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 42 42)

def _update_HFGITR_EL2_Type_TLBIVMALLE1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _get_HFGITR_EL2_Type_TLBIVMALLE1IS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_HFGITR_EL2_Type_TLBIVMALLE1IS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_HFGITR_EL2_Type_TLBIVMALLE1OS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_HFGITR_EL2_Type_TLBIVMALLE1OS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_HFGITR_EL2_Type_nBRBIALL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)

def _update_HFGITR_EL2_Type_nBRBIALL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _get_HFGITR_EL2_Type_nBRBINJ (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)

def _update_HFGITR_EL2_Type_nBRBINJ (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _get_HFGITR_EL2_Type_nGCSEPP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _update_HFGITR_EL2_Type_nGCSEPP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _get_HFGITR_EL2_Type_nGCSPUSHM_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)

def _update_HFGITR_EL2_Type_nGCSPUSHM_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _get_HFGITR_EL2_Type_nGCSSTR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _update_HFGITR_EL2_Type_nGCSSTR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def CPYOptionA (_ : Unit) : SailM Bool := do
  (__IMPDEF_boolean "CPY* instructions use Option A")

def CPYFOptionA (_ : Unit) : SailM Bool := do
  (__IMPDEF_boolean "CPYF* instructions use Option A")

def SETOptionA (_ : Unit) : SailM Bool := do
  (__IMPDEF_boolean "SET* instructions use Option A")

def SETGOptionA (_ : Unit) : SailM Bool := do
  (__IMPDEF_boolean "SETG* instructions use Option A")

def MaxBlockSizeCopiedBytes (_ : Unit) : SailM Nat := do
  let nbytes ← do (__IMPDEF_integer "Maximum bytes used in a single block of a copy")
  sail_assert (nbytes ≥b 0) "src/v8_base.sail:31968.22-31968.23"
  (pure nbytes)

/-- Type quantifiers: N : Nat, N = 16 -/
def BFInfinity (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  sail_assert (N == 16) "src/v8_base.sail:32474.18-32474.19"
  let E := 8
  let F := (N -i (E +i 1))
  (pure ((sign +++ (Ones (n := E))) +++ (Zeros (n := F))))

/-- Type quantifiers: N : Nat, N = 16 -/
def BFZero (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  sail_assert (N == 16) "src/v8_base.sail:32483.18-32483.19"
  let E := 8
  let F := (N -i (E +i 1))
  (pure ((sign +++ (Zeros (n := E))) +++ (Zeros (n := F))))

def AArch32_PhysicalSErrorSyndrome (_ : Unit) : SailM (BitVec 16) := do
  let syndrome : (BitVec 32) := (Zeros (n := 32))
  let fault ← (( do (GetPendingPhysicalSError ()) ) : SailM FaultRecord )
  let syndrome ← (( do
    if (((← readReg PSTATE).EL == EL2) : Bool)
    then
      (do
        let errstate ← (( do (AArch32_PEErrorState fault) ) : SailM ErrorState )
        let syndrome ← (pure (Sail.BitVec.updateSubrange syndrome 11 10 (← (AArch32_EncodeAsyncErrorSyndrome errstate))))
        let syndrome : (BitVec 32) := (BitVec.update syndrome 9 (Bit fault.extflag))
        (pure (Sail.BitVec.updateSubrange syndrome 5 0 0b010001#6)))
    else
      (do
        let long_format ← (( do (pure ((_get_TTBCR_Type_EAE (← (TTBCR_read ()))) == 1#1)) ) : SailM Bool )
        (AArch32_CommonFaultStatus fault long_format)) ) : SailM (BitVec 32) )
  (pure (Sail.BitVec.extractLsb syndrome 15 0))

def undefined_DISR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_DISR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_DISR_EL1_Type_DFSC (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 5 0)

def _update_DISR_EL1_Type_DFSC (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 0 x)

def _update_DISR_Type_DFSC (v : (BitVec 32)) (x : (BitVec 6)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 0 x)

def _get_DISR_Type_DFSC (v : (BitVec 32)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 5 0)

def _get_DISR_EL1_Type_IDS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_DISR_EL1_Type_IDS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_ID_AA64MMFR2_EL1_Type_IDS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 36 x)

def _update_VDISR_EL2_Type_IDS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_VSESR_EL2_Type_IDS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_ID_AA64MMFR2_EL1_Type_IDS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 39 36)

def _get_VDISR_EL2_Type_IDS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def undefined_DISR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DISR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def DISR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DISR_Type := value_name
  writeReg DISR_EL1 (Sail.BitVec.updateSubrange (← readReg DISR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _DISR r

def ExternalDebugInterruptsDisabled (target : (BitVec 2)) : SailM Bool := do
  let int_dis ← (( do (undefined_bool ()) ) : SailM Bool )
  let ss ← (( do (SecurityStateAtEL target) ) : SailM SecurityState )
  if ((← (Havev8p4Debug ())) : Bool)
  then
    (do
      if (((BitVec.join1 [(BitVec.access (_get_EDSCR_Type_INTdis (← (EDSCR_read ()))) 0)]) == 1#1) : Bool)
      then
        (do
          match ss with
          | .SS_NonSecure => (do (ExternalInvasiveDebugEnabled ()))
          | .SS_Secure => (do (ExternalSecureInvasiveDebugEnabled ()))
          | .SS_Realm => (do (ExternalRealmInvasiveDebugEnabled ()))
          | .SS_Root => (do (ExternalRootInvasiveDebugEnabled ())))
      else (pure false))
  else
    (do
      let questionMark := target
      if ((questionMark == EL3) : Bool)
      then (do (pure ((_get_EDSCR_Type_INTdis (← (EDSCR_read ()))) == 0b11#2)) <&&> (do (ExternalSecureInvasiveDebugEnabled ())))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              (do
                let b__0 ← do (pure (_get_EDSCR_Type_INTdis (← (EDSCR_read ()))))
                if (((Sail.BitVec.extractLsb b__0 1 1) == (1#1 : (BitVec 1))) : Bool)
                then (pure true)
                else (pure false)) <&&> (do
                (ExternalInvasiveDebugEnabled ())))
          else
            (do
              if ((questionMark == EL1) : Bool)
              then
                (do
                  if ((BEq.beq ss SS_Secure) : Bool)
                  then
                    (do
                      (do
                        let b__1 ← do (pure (_get_EDSCR_Type_INTdis (← (EDSCR_read ()))))
                        if (((Sail.BitVec.extractLsb b__1 1 1) == (1#1 : (BitVec 1))) : Bool)
                        then (pure true)
                        else (pure false)) <&&> (do
                        (ExternalSecureInvasiveDebugEnabled ())))
                  else (do (pure ((_get_EDSCR_Type_INTdis (← (EDSCR_read ()))) != 0b00#2)) <&&> (do (ExternalInvasiveDebugEnabled ()))))
              else (pure int_dis))))

def IsSynchronizablePhysicalSErrorPending (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())

def undefined_VDFSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_VDFSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_VSESR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_VSESR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_VDISR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_VDISR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_VDISR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_VDISR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def VDISR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : VDISR_Type := value_name
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange (← readReg VDISR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _VDISR r

def IsTMEEnabled (_ : Unit) : SailM Bool := SailME.run do
  if (((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
         (pure ((← readReg PSTATE).EL == EL1)) <||> (do
           (pure ((← readReg PSTATE).EL == EL2)))))) && (HaveEL EL3)) : Bool)
  then
    (do
      if (((_get_SCR_EL3_Type_TME (← readReg SCR_EL3)) == 0#1) : Bool)
      then SailME.throw (false : Bool)
      else (pure ()))
  else (pure ())
  if ((←((pure ((← readReg PSTATE).EL == EL0)) <||> (do
       (pure ((← readReg PSTATE).EL == EL1))) <&&> (do
       (EL2Enabled ())))) : Bool)
  then
    (do
      if (((_get_HCR_EL2_Type_TME (← readReg HCR_EL2)) == 0#1) : Bool)
      then SailME.throw (false : Bool)
      else (pure ()))
  else (pure ())
  (pure true)

/-- Type quantifiers: dreg : Int -/
def TransactionStartTrap (dreg : Int) : SailM Unit := do
  let targetEL ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_TSTARTAccessTrap) ) : SailM ExceptionRecord )
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 9 5 (integer_subrange dreg 4 0)) }
  let targetEL ← (( do
    if (((BitVec.toNat (← readReg PSTATE).EL) >b (BitVec.toNat EL1)) : Bool)
    then (do (pure (← readReg PSTATE).EL))
    else
      (do
        if ((←((EL2Enabled ()) <&&> (do
             (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))))) : Bool)
        then (pure EL2)
        else (pure EL1)) ) : SailM (BitVec 2) )
  (AArch64_TakeException targetEL except preferred_exception_return vect_offset)

def undefined_RVBAR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_RVBAR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_RVBAR_EL1_Type_ResetAddress (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _update_RVBAR_EL1_Type_ResetAddress (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_RVBAR_EL2_Type_ResetAddress (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_RVBAR_EL3_Type_ResetAddress (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _get_RVBAR_EL2_Type_ResetAddress (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_RVBAR_EL3_Type_ResetAddress (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def undefined_RVBAR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_RVBAR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_RVBAR_EL3_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_RVBAR_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def AMCFGR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMCFGR ) : SailM AMCFGR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AMCFGR_EL0) 0 32)))

def AMCFGR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMCFGR_Type := value_name
  writeReg AMCFGR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCFGR_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _AMCFGR r

def AMCGCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMCGCR ) : SailM AMCGCR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AMCGCR_EL0) 0 32)))

def AMCGCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMCGCR_Type := value_name
  writeReg AMCGCR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCGCR_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _AMCGCR r

def AMCNTENCLR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMCNTENCLR0 ) : SailM AMCNTENCLR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AMCNTENCLR0_EL0) 0 32)))

def AMCNTENCLR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMCNTENCLR0_Type := value_name
  writeReg AMCNTENCLR0_EL0 (Sail.BitVec.updateSubrange (← readReg AMCNTENCLR0_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _AMCNTENCLR0 r

def AMCNTENCLR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMCNTENCLR1 ) : SailM AMCNTENCLR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AMCNTENCLR1_EL0) 0 32)))

def AMCNTENCLR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMCNTENCLR1_Type := value_name
  writeReg AMCNTENCLR1_EL0 (Sail.BitVec.updateSubrange (← readReg AMCNTENCLR1_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _AMCNTENCLR1 r

def AMCNTENSET0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMCNTENSET0 ) : SailM AMCNTENSET0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AMCNTENSET0_EL0) 0 32)))

def AMCNTENSET0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMCNTENSET0_Type := value_name
  writeReg AMCNTENSET0_EL0 (Sail.BitVec.updateSubrange (← readReg AMCNTENSET0_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _AMCNTENSET0 r

def AMCNTENSET1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMCNTENSET1 ) : SailM AMCNTENSET1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AMCNTENSET1_EL0) 0 32)))

def AMCNTENSET1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMCNTENSET1_Type := value_name
  writeReg AMCNTENSET1_EL0 (Sail.BitVec.updateSubrange (← readReg AMCNTENSET1_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _AMCNTENSET1 r

def AMCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMCR ) : SailM AMCR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AMCR_EL0) 0 32)))

def AMCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMCR_Type := value_name
  writeReg AMCR_EL0 (Sail.BitVec.updateSubrange (← readReg AMCR_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _AMCR r

def AMUSERENR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _AMUSERENR ) : SailM AMUSERENR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg AMUSERENR_EL0) 0 32)))

def AMUSERENR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AMUSERENR_Type := value_name
  writeReg AMUSERENR_EL0 (Sail.BitVec.updateSubrange (← readReg AMUSERENR_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _AMUSERENR r

def CCSIDR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CCSIDR2 ) : SailM CCSIDR2_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg CCSIDR2_EL1) 0 32)))

def CCSIDR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CCSIDR2_Type := value_name
  writeReg CCSIDR2_EL1 (Sail.BitVec.updateSubrange (← readReg CCSIDR2_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _CCSIDR2 r

def CCSIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CCSIDR ) : SailM CCSIDR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg CCSIDR_EL1) 0 32)))

def CCSIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CCSIDR_Type := value_name
  writeReg CCSIDR_EL1 (Sail.BitVec.updateSubrange (← readReg CCSIDR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _CCSIDR r

def CNTHCTL_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CNTHCTL ) : SailM CNTHCTL_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg CNTHCTL_EL2) 0 32)))

def CNTHCTL_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTHCTL_Type := value_name
  writeReg CNTHCTL_EL2 (Sail.BitVec.updateSubrange (← readReg CNTHCTL_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _CNTHCTL r

def CNTHPS_CTL_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CNTHPS_CTL ) : SailM CNTHPS_CTL_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg CNTHPS_CTL_EL2) 0 32)))

def CNTHPS_CTL_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTHPS_CTL_Type := value_name
  writeReg CNTHPS_CTL_EL2 (Sail.BitVec.updateSubrange (← readReg CNTHPS_CTL_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _CNTHPS_CTL r

def CNTHVS_CTL_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CNTHVS_CTL ) : SailM CNTHVS_CTL_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg CNTHVS_CTL_EL2) 0 32)))

def CNTHVS_CTL_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTHVS_CTL_Type := value_name
  writeReg CNTHVS_CTL_EL2 (Sail.BitVec.updateSubrange (← readReg CNTHVS_CTL_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _CNTHVS_CTL r

def CNTHV_CTL_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CNTHV_CTL ) : SailM CNTHV_CTL_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg CNTHV_CTL_EL2) 0 32)))

def CNTHV_CTL_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTHV_CTL_Type := value_name
  writeReg CNTHV_CTL_EL2 (Sail.BitVec.updateSubrange (← readReg CNTHV_CTL_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _CNTHV_CTL r

def CNTKCTL_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTKCTL_Type := value_name
  writeReg CNTKCTL_EL1 (Sail.BitVec.updateSubrange (← readReg CNTKCTL_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _CNTKCTL r

def CNTV_CTL_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CNTV_CTL ) : SailM CNTV_CTL_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg CNTV_CTL_EL0) 0 32)))

def CNTV_CTL_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTV_CTL_Type := value_name
  writeReg CNTV_CTL_EL0 (Sail.BitVec.updateSubrange (← readReg CNTV_CTL_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _CNTV_CTL r

def CPACR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CPACR_Type := value_name
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange (← readReg CPACR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _CPACR r

def CSSELR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CSSELR_NS ) : SailM CSSELR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg CSSELR_EL1) 0 32)))

def undefined_CSSELR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def CSSELR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CSSELR_Type := value_name
  writeReg CSSELR_EL1 (Sail.BitVec.updateSubrange (← readReg CSSELR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _CSSELR_NS r

def CTR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CTR ) : SailM CTR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg CTR_EL0) 0 32)))

def CTR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CTR_Type := value_name
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange (← readReg CTR_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _CTR r

def DBGAUTHSTATUS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGAUTHSTATUS ) : SailM DBGAUTHSTATUS_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg DBGAUTHSTATUS_EL1) 0 32)))

def DBGAUTHSTATUS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGAUTHSTATUS_Type := value_name
  writeReg DBGAUTHSTATUS_EL1 (Sail.BitVec.updateSubrange (← readReg DBGAUTHSTATUS_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _DBGAUTHSTATUS r

def DBGCLAIMCLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGCLAIMCLR ) : SailM DBGCLAIMCLR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg DBGCLAIMCLR_EL1) 0 32)))

def DBGCLAIMCLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGCLAIMCLR_Type := value_name
  writeReg DBGCLAIMCLR_EL1 (Sail.BitVec.updateSubrange (← readReg DBGCLAIMCLR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _DBGCLAIMCLR r

def DBGCLAIMSET_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGCLAIMSET ) : SailM DBGCLAIMSET_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg DBGCLAIMSET_EL1) 0 32)))

def DBGCLAIMSET_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGCLAIMSET_Type := value_name
  writeReg DBGCLAIMSET_EL1 (Sail.BitVec.updateSubrange (← readReg DBGCLAIMSET_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _DBGCLAIMSET r

def DBGDCCINT_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGDCCINT ) : SailM DBGDCCINT_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg MDCCINT_EL1) 0 32)))

def DBGDCCINT_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGDCCINT_Type := value_name
  writeReg MDCCINT_EL1 (Sail.BitVec.updateSubrange (← readReg MDCCINT_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _DBGDCCINT r

def DBGDRAR_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _DBGDRAR ) : SailM DBGDRAR_Type )
  (pure (Sail.BitVec.updateSubrange r 63 0 (BitVec.slice (← readReg MDRAR_EL1) 0 64)))

def DBGDRAR_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : DBGDRAR_Type := value_name
  writeReg MDRAR_EL1 (Sail.BitVec.updateSubrange (← readReg MDRAR_EL1) 63 0 (BitVec.slice r 0 64))
  writeReg _DBGDRAR r

def DBGOSDLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGOSDLR_Type := value_name
  writeReg OSDLR_EL1 (Sail.BitVec.updateSubrange (← readReg OSDLR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _DBGOSDLR r

def DBGOSLSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGOSLSR_Type := value_name
  writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange (← readReg OSLSR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _DBGOSLSR r

def DBGPRCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGPRCR_Type := value_name
  writeReg DBGPRCR_EL1 (Sail.BitVec.updateSubrange (← readReg DBGPRCR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _DBGPRCR r

def DBGVCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGVCR_Type := value_name
  writeReg DBGVCR32_EL2 (Sail.BitVec.updateSubrange (← readReg DBGVCR32_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _DBGVCR r

def DFSR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DFSR_NS ) : SailM DFSR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ESR_EL1) 0 32)))

def DISR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DISR ) : SailM DISR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg DISR_EL1) 0 32)))

def DSPSR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DSPSR2 ) : SailM DSPSR2_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg DSPSR_EL0) 32 32)))

def EDECCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : EDECCR_Type := value_name
  writeReg OSECCR_EL1 (Sail.BitVec.updateSubrange (← readReg OSECCR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _EDECCR r

def EDSCR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : EDSCR2_Type := value_name
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange (← readReg MDSCR_EL1) 63 32 (BitVec.slice r 0 32))
  writeReg _EDSCR2 r

def ERRIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERRIDR ) : SailM ERRIDR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERRIDR_EL1) 0 32)))

def ERRIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERRIDR_Type := value_name
  writeReg ERRIDR_EL1 (Sail.BitVec.updateSubrange (← readReg ERRIDR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ERRIDR r

def ERRSELR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ERRSELR ) : SailM ERRSELR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ERRSELR_EL1) 0 32)))

def ERRSELR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ERRSELR_Type := value_name
  writeReg ERRSELR_EL1 (Sail.BitVec.updateSubrange (← readReg ERRSELR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ERRSELR r

def HCPTR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HCPTR_Type := value_name
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange (← readReg CPTR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _HCPTR r

def HCR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HCR2_Type := value_name
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange (← readReg HCR_EL2) 63 32 (BitVec.slice r 0 32))
  writeReg _HCR2 r

def HDCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HDCR_Type := value_name
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange (← readReg MDCR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _HDCR r

def HRMR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HRMR ) : SailM HRMR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg RMR_EL2) 0 32)))

def HRMR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HRMR_Type := value_name
  writeReg RMR_EL2 (Sail.BitVec.updateSubrange (← readReg RMR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _HRMR r

def HSCTLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HSCTLR_Type := value_name
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _HSCTLR r

def HSTR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HSTR ) : SailM HSTR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg HSTR_EL2) 0 32)))

def HSTR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HSTR_Type := value_name
  writeReg HSTR_EL2 (Sail.BitVec.updateSubrange (← readReg HSTR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _HSTR r

def HTCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HTCR_Type := value_name
  writeReg TCR_EL2 (Sail.BitVec.updateSubrange (← readReg TCR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _HTCR r

def HTRFCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HTRFCR ) : SailM HTRFCR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg TRFCR_EL2) 0 32)))

def HTRFCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HTRFCR_Type := value_name
  writeReg TRFCR_EL2 (Sail.BitVec.updateSubrange (← readReg TRFCR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _HTRFCR r

def HVBAR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HVBAR_Type := value_name
  writeReg VBAR_EL2 (Sail.BitVec.updateSubrange (← readReg VBAR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _HVBAR r

def ICC_ASGI1R_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _ICC_ASGI1R ) : SailM ICC_ASGI1R_Type )
  (pure (Sail.BitVec.updateSubrange r 63 0 (BitVec.slice (← readReg ICC_ASGI1R_EL1) 0 64)))

def ICC_ASGI1R_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_ASGI1R_Type := value_name
  writeReg ICC_ASGI1R_EL1 (Sail.BitVec.updateSubrange (← readReg ICC_ASGI1R_EL1) 63 0 (BitVec.slice r 0 64))
  writeReg _ICC_ASGI1R r

def ICC_BPR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_BPR0 ) : SailM ICC_BPR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_BPR0_EL1) 0 32)))

def ICC_BPR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_BPR0_Type := value_name
  writeReg ICC_BPR0_EL1 (Sail.BitVec.updateSubrange (← readReg ICC_BPR0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_BPR0 r

def ICC_BPR1_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_BPR1_NS ) : SailM ICC_BPR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_BPR1_EL1_NS) 0 32)))

def ICC_BPR1_S_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_BPR1_S ) : SailM ICC_BPR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_BPR1_EL1_S) 0 32)))

def undefined_ICC_BPR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def ICC_BPR1_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_BPR1_Type := value_name
  writeReg ICC_BPR1_EL1_NS (Sail.BitVec.updateSubrange (← readReg ICC_BPR1_EL1_NS) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_BPR1_NS r

def ICC_BPR1_S_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_BPR1_Type := value_name
  writeReg ICC_BPR1_EL1_S (Sail.BitVec.updateSubrange (← readReg ICC_BPR1_EL1_S) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_BPR1_S r

def ICC_CTLR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_CTLR_NS ) : SailM ICC_CTLR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_CTLR_EL1_NS) 0 32)))

def ICC_CTLR_S_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_CTLR_S ) : SailM ICC_CTLR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_CTLR_EL1_S) 0 32)))

def undefined_ICC_CTLR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def ICC_CTLR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_CTLR_Type := value_name
  writeReg ICC_CTLR_EL1_NS (Sail.BitVec.updateSubrange (← readReg ICC_CTLR_EL1_NS) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_CTLR_NS r

def ICC_CTLR_S_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_CTLR_Type := value_name
  writeReg ICC_CTLR_EL1_S (Sail.BitVec.updateSubrange (← readReg ICC_CTLR_EL1_S) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_CTLR_S r

def ICC_DIR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_DIR ) : SailM ICC_DIR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_DIR_EL1) 0 32)))

def ICC_DIR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_DIR_Type := value_name
  writeReg ICC_DIR_EL1 (Sail.BitVec.updateSubrange (← readReg ICC_DIR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_DIR r

def ICC_EOIR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_EOIR0 ) : SailM ICC_EOIR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_EOIR0_EL1) 0 32)))

def ICC_EOIR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_EOIR0_Type := value_name
  writeReg ICC_EOIR0_EL1 (Sail.BitVec.updateSubrange (← readReg ICC_EOIR0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_EOIR0 r

def ICC_EOIR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_EOIR1 ) : SailM ICC_EOIR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_EOIR1_EL1) 0 32)))

def ICC_EOIR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_EOIR1_Type := value_name
  writeReg ICC_EOIR1_EL1 (Sail.BitVec.updateSubrange (← readReg ICC_EOIR1_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_EOIR1 r

def ICC_HPPIR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_HPPIR0 ) : SailM ICC_HPPIR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_HPPIR0_EL1) 0 32)))

def ICC_HPPIR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_HPPIR0_Type := value_name
  writeReg ICC_HPPIR0_EL1 (Sail.BitVec.updateSubrange (← readReg ICC_HPPIR0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_HPPIR0 r

def ICC_HPPIR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_HPPIR1 ) : SailM ICC_HPPIR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_HPPIR1_EL1) 0 32)))

def ICC_HPPIR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_HPPIR1_Type := value_name
  writeReg ICC_HPPIR1_EL1 (Sail.BitVec.updateSubrange (← readReg ICC_HPPIR1_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_HPPIR1 r

def ICC_HSRE_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_HSRE ) : SailM ICC_HSRE_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_SRE_EL2) 0 32)))

def ICC_HSRE_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_HSRE_Type := value_name
  writeReg ICC_SRE_EL2 (Sail.BitVec.updateSubrange (← readReg ICC_SRE_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_HSRE r

def ICC_IAR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_IAR0 ) : SailM ICC_IAR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_IAR0_EL1) 0 32)))

def ICC_IAR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_IAR0_Type := value_name
  writeReg ICC_IAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ICC_IAR0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_IAR0 r

def ICC_IAR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_IAR1 ) : SailM ICC_IAR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_IAR1_EL1) 0 32)))

def ICC_IAR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_IAR1_Type := value_name
  writeReg ICC_IAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ICC_IAR1_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_IAR1 r

def ICC_IGRPEN0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_IGRPEN0 ) : SailM ICC_IGRPEN0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_IGRPEN0_EL1) 0 32)))

def ICC_IGRPEN0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_IGRPEN0_Type := value_name
  writeReg ICC_IGRPEN0_EL1 (Sail.BitVec.updateSubrange (← readReg ICC_IGRPEN0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_IGRPEN0 r

def ICC_IGRPEN1_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_IGRPEN1_NS ) : SailM ICC_IGRPEN1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_IGRPEN1_EL1_NS) 0 32)))

def ICC_IGRPEN1_S_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_IGRPEN1_S ) : SailM ICC_IGRPEN1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_IGRPEN1_EL1_S) 0 32)))

def undefined_ICC_IGRPEN1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def ICC_IGRPEN1_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_IGRPEN1_Type := value_name
  writeReg ICC_IGRPEN1_EL1_NS (Sail.BitVec.updateSubrange (← readReg ICC_IGRPEN1_EL1_NS) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_IGRPEN1_NS r

def ICC_IGRPEN1_S_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_IGRPEN1_Type := value_name
  writeReg ICC_IGRPEN1_EL1_S (Sail.BitVec.updateSubrange (← readReg ICC_IGRPEN1_EL1_S) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_IGRPEN1_S r

def ICC_PMR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_PMR ) : SailM ICC_PMR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_PMR_EL1) 0 32)))

def ICC_PMR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_PMR_Type := value_name
  writeReg ICC_PMR_EL1 (Sail.BitVec.updateSubrange (← readReg ICC_PMR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_PMR r

def ICC_RPR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_RPR ) : SailM ICC_RPR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_RPR_EL1) 0 32)))

def ICC_RPR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_RPR_Type := value_name
  writeReg ICC_RPR_EL1 (Sail.BitVec.updateSubrange (← readReg ICC_RPR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_RPR r

def ICC_SGI0R_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _ICC_SGI0R ) : SailM ICC_SGI0R_Type )
  (pure (Sail.BitVec.updateSubrange r 63 0 (BitVec.slice (← readReg ICC_SGI0R_EL1) 0 64)))

def ICC_SGI0R_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_SGI0R_Type := value_name
  writeReg ICC_SGI0R_EL1 (Sail.BitVec.updateSubrange (← readReg ICC_SGI0R_EL1) 63 0 (BitVec.slice r 0 64))
  writeReg _ICC_SGI0R r

def ICC_SGI1R_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _ICC_SGI1R ) : SailM ICC_SGI1R_Type )
  (pure (Sail.BitVec.updateSubrange r 63 0 (BitVec.slice (← readReg ICC_SGI1R_EL1) 0 64)))

def ICC_SGI1R_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_SGI1R_Type := value_name
  writeReg ICC_SGI1R_EL1 (Sail.BitVec.updateSubrange (← readReg ICC_SGI1R_EL1) 63 0 (BitVec.slice r 0 64))
  writeReg _ICC_SGI1R r

def ICC_SRE_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_SRE_NS ) : SailM ICC_SRE_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_SRE_EL1_NS) 0 32)))

def ICC_SRE_S_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICC_SRE_S ) : SailM ICC_SRE_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICC_SRE_EL1_S) 0 32)))

def undefined_ICC_SRE_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def ICC_SRE_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_SRE_Type := value_name
  writeReg ICC_SRE_EL1_NS (Sail.BitVec.updateSubrange (← readReg ICC_SRE_EL1_NS) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_SRE_NS r

def ICC_SRE_S_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICC_SRE_Type := value_name
  writeReg ICC_SRE_EL1_S (Sail.BitVec.updateSubrange (← readReg ICC_SRE_EL1_S) 31 0 (BitVec.slice r 0 32))
  writeReg _ICC_SRE_S r

def ICH_EISR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICH_EISR ) : SailM ICH_EISR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICH_EISR_EL2) 0 32)))

def ICH_EISR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_EISR_Type := value_name
  writeReg ICH_EISR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_EISR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _ICH_EISR r

def ICH_ELRSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICH_ELRSR ) : SailM ICH_ELRSR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICH_ELRSR_EL2) 0 32)))

def ICH_ELRSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_ELRSR_Type := value_name
  writeReg ICH_ELRSR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_ELRSR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _ICH_ELRSR r

def ICH_HCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICH_HCR ) : SailM ICH_HCR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICH_HCR_EL2) 0 32)))

def ICH_HCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_HCR_Type := value_name
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_HCR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _ICH_HCR r

def ICH_MISR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICH_MISR ) : SailM ICH_MISR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICH_MISR_EL2) 0 32)))

def ICH_MISR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_MISR_Type := value_name
  writeReg ICH_MISR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_MISR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _ICH_MISR r

def ICH_VMCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICH_VMCR ) : SailM ICH_VMCR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICH_VMCR_EL2) 0 32)))

def ICH_VMCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_VMCR_Type := value_name
  writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VMCR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _ICH_VMCR r

def ICH_VTR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICH_VTR ) : SailM ICH_VTR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICH_VTR_EL2) 0 32)))

def ICH_VTR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICH_VTR_Type := value_name
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange (← readReg ICH_VTR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _ICH_VTR r

def ICV_BPR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_BPR0 ) : SailM ICV_BPR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICV_BPR0_EL1) 0 32)))

def ICV_BPR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_BPR0_Type := value_name
  writeReg ICV_BPR0_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_BPR0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_BPR0 r

def ICV_BPR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_BPR1 ) : SailM ICV_BPR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICV_BPR1_EL1) 0 32)))

def ICV_BPR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_BPR1_Type := value_name
  writeReg ICV_BPR1_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_BPR1_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_BPR1 r

def ICV_CTLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_CTLR ) : SailM ICV_CTLR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICV_CTLR_EL1) 0 32)))

def ICV_CTLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_CTLR_Type := value_name
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_CTLR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_CTLR r

def ICV_DIR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_DIR ) : SailM ICV_DIR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICV_DIR_EL1) 0 32)))

def ICV_DIR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_DIR_Type := value_name
  writeReg ICV_DIR_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_DIR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_DIR r

def ICV_EOIR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_EOIR0 ) : SailM ICV_EOIR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICV_EOIR0_EL1) 0 32)))

def ICV_EOIR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_EOIR0_Type := value_name
  writeReg ICV_EOIR0_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_EOIR0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_EOIR0 r

def ICV_EOIR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_EOIR1 ) : SailM ICV_EOIR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICV_EOIR1_EL1) 0 32)))

def ICV_EOIR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_EOIR1_Type := value_name
  writeReg ICV_EOIR1_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_EOIR1_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_EOIR1 r

def ICV_HPPIR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_HPPIR0 ) : SailM ICV_HPPIR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICV_HPPIR0_EL1) 0 32)))

def ICV_HPPIR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_HPPIR0_Type := value_name
  writeReg ICV_HPPIR0_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_HPPIR0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_HPPIR0 r

def ICV_HPPIR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_HPPIR1 ) : SailM ICV_HPPIR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICV_HPPIR1_EL1) 0 32)))

def ICV_HPPIR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_HPPIR1_Type := value_name
  writeReg ICV_HPPIR1_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_HPPIR1_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_HPPIR1 r

def ICV_IAR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_IAR0 ) : SailM ICV_IAR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICV_IAR0_EL1) 0 32)))

def ICV_IAR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_IAR0_Type := value_name
  writeReg ICV_IAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_IAR0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_IAR0 r

def ICV_IAR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_IAR1 ) : SailM ICV_IAR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICV_IAR1_EL1) 0 32)))

def ICV_IAR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_IAR1_Type := value_name
  writeReg ICV_IAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_IAR1_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_IAR1 r

def ICV_IGRPEN0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_IGRPEN0 ) : SailM ICV_IGRPEN0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICV_IGRPEN0_EL1) 0 32)))

def ICV_IGRPEN0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_IGRPEN0_Type := value_name
  writeReg ICV_IGRPEN0_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_IGRPEN0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_IGRPEN0 r

def ICV_IGRPEN1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_IGRPEN1 ) : SailM ICV_IGRPEN1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICV_IGRPEN1_EL1) 0 32)))

def ICV_IGRPEN1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_IGRPEN1_Type := value_name
  writeReg ICV_IGRPEN1_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_IGRPEN1_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_IGRPEN1 r

def ICV_PMR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_PMR ) : SailM ICV_PMR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICV_PMR_EL1) 0 32)))

def ICV_PMR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_PMR_Type := value_name
  writeReg ICV_PMR_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_PMR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_PMR r

def ICV_RPR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ICV_RPR ) : SailM ICV_RPR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ICV_RPR_EL1) 0 32)))

def ICV_RPR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ICV_RPR_Type := value_name
  writeReg ICV_RPR_EL1 (Sail.BitVec.updateSubrange (← readReg ICV_RPR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ICV_RPR r

def ID_AFR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_AFR0 ) : SailM ID_AFR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_AFR0_EL1) 0 32)))

def ID_AFR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_AFR0_Type := value_name
  writeReg ID_AFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_AFR0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_AFR0 r

def ID_DFR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_DFR1 ) : SailM ID_DFR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_DFR1_EL1) 0 32)))

def ID_DFR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_DFR1_Type := value_name
  writeReg ID_DFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR1_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_DFR1 r

def ID_ISAR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_ISAR0 ) : SailM ID_ISAR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_ISAR0_EL1) 0 32)))

def ID_ISAR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_ISAR0_Type := value_name
  writeReg ID_ISAR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_ISAR0 r

def ID_ISAR5_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_ISAR5 ) : SailM ID_ISAR5_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_ISAR5_EL1) 0 32)))

def ID_ISAR5_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_ISAR5_Type := value_name
  writeReg ID_ISAR5_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR5_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_ISAR5 r

def ID_MMFR5_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_MMFR5 ) : SailM ID_MMFR5_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_MMFR5_EL1) 0 32)))

def ID_MMFR5_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_MMFR5_Type := value_name
  writeReg ID_MMFR5_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR5_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_MMFR5 r

def ID_PFR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_PFR2 ) : SailM ID_PFR2_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_PFR2_EL1) 0 32)))

def ID_PFR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_PFR2_Type := value_name
  writeReg ID_PFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_PFR2_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_PFR2 r

def IFSR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _IFSR_NS ) : SailM IFSR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg IFSR32_EL2) 0 32)))

def ISR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ISR ) : SailM ISR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ISR_EL1) 0 32)))

def ISR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ISR_Type := value_name
  writeReg ISR_EL1 (Sail.BitVec.updateSubrange (← readReg ISR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ISR r

def MPIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _MPIDR ) : SailM MPIDR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg MPIDR_EL1) 0 32)))

def MPIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MPIDR_Type := value_name
  writeReg MPIDR_EL1 (Sail.BitVec.updateSubrange (← readReg MPIDR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _MPIDR r

def MVFR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _MVFR2 ) : SailM MVFR2_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg MVFR2_EL1) 0 32)))

def MVFR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MVFR2_Type := value_name
  writeReg MVFR2_EL1 (Sail.BitVec.updateSubrange (← readReg MVFR2_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _MVFR2 r

def Mk_AMCFGR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_AMCGCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_AMCNTENCLR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_AMCNTENCLR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_AMCNTENSET0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_AMCNTENSET1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_AMCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_AMUSERENR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_CCSIDR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_CCSIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_CNTHCTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_CNTHPS_CTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_CNTHVS_CTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_CNTHV_CTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_CNTV_CTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_CSSELR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_CTR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_DBGAUTHSTATUS_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_DBGCLAIMCLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_DBGCLAIMSET_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_DBGDCCINT_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_DBGDRAR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_DBGVCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ERRIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ERRSELR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_HRMR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_HSTR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_HTCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_HTRFCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICC_ASGI1R_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_ICC_BPR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICC_BPR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICC_CTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICC_DIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICC_EOIR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICC_EOIR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICC_HPPIR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICC_HPPIR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICC_HSRE_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICC_IAR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICC_IAR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICC_IGRPEN0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICC_IGRPEN1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICC_PMR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICC_RPR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICC_SGI0R_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_ICC_SGI1R_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_ICC_SRE_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICH_EISR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICH_ELRSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICH_HCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICH_MISR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICH_VMCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICH_VTR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICV_BPR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICV_BPR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICV_CTLR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICV_DIR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICV_EOIR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICV_EOIR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICV_HPPIR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICV_HPPIR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICV_IAR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICV_IAR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICV_IGRPEN0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICV_IGRPEN1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICV_PMR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ICV_RPR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ID_DFR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ID_ISAR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ID_ISAR5_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ID_MMFR5_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ID_PFR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ISR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_MPIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_MVFR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_PAR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_PMCNTEN_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_PMINTEN_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_PMOVS_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_PMSELR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_PMSWINC_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_PMUSERENR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_PRRR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_RMR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_TRFCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_TTBCR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_VMPIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_VTCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PAR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def PAR_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : PAR_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg PAR_S r
  else writeReg PAR_NS r

def PMCCFILTR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCCFILTR_Type := value_name
  writeReg PMCCFILTR_EL0 (Sail.BitVec.updateSubrange (← readReg PMCCFILTR_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _PMCCFILTR r

def PMCNTEN_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _PMCNTEN ) : SailM PMCNTEN_Type )
  (pure (Sail.BitVec.updateSubrange r 63 0 (BitVec.slice (← readReg PMCNTENSET_EL0) 0 64)))

def PMCNTEN_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : PMCNTEN_Type := value_name
  writeReg PMCNTENSET_EL0 (Sail.BitVec.updateSubrange (← readReg PMCNTENSET_EL0) 63 0 (BitVec.slice r 0 64))
  writeReg _PMCNTEN r

def PMCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCR_Type := value_name
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange (← readReg PMCR_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _PMCR r

def PMINTEN_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _PMINTEN ) : SailM PMINTEN_Type )
  (pure (Sail.BitVec.updateSubrange r 63 0 (BitVec.slice (← readReg PMINTENSET_EL1) 0 64)))

def PMINTEN_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : PMINTEN_Type := value_name
  writeReg PMINTENSET_EL1 (Sail.BitVec.updateSubrange (← readReg PMINTENSET_EL1) 63 0 (BitVec.slice r 0 64))
  writeReg _PMINTEN r

def PMOVS_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _PMOVS ) : SailM PMOVS_Type )
  (pure (Sail.BitVec.updateSubrange r 63 0 (BitVec.slice (← readReg PMOVSSET_EL0) 0 64)))

def PMOVS_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : PMOVS_Type := value_name
  writeReg PMOVSSET_EL0 (Sail.BitVec.updateSubrange (← readReg PMOVSSET_EL0) 63 0 (BitVec.slice r 0 64))
  writeReg _PMOVS r

def PMSELR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMSELR ) : SailM PMSELR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg PMSELR_EL0) 0 32)))

def PMSELR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMSELR_Type := value_name
  writeReg PMSELR_EL0 (Sail.BitVec.updateSubrange (← readReg PMSELR_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _PMSELR r

def PMSWINC_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMSWINC ) : SailM PMSWINC_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg PMSWINC_EL0) 0 32)))

def PMSWINC_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMSWINC_Type := value_name
  writeReg PMSWINC_EL0 (Sail.BitVec.updateSubrange (← readReg PMSWINC_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _PMSWINC r

def PMUSERENR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _PMUSERENR ) : SailM PMUSERENR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg PMUSERENR_EL0) 0 32)))

def PMUSERENR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMUSERENR_Type := value_name
  writeReg PMUSERENR_EL0 (Sail.BitVec.updateSubrange (← readReg PMUSERENR_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _PMUSERENR r

def PRRR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PRRR_Type := value_name
  writeReg MAIR_EL1 (Sail.BitVec.updateSubrange (← readReg MAIR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _PRRR_NS r

def RMR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _RMR ) : SailM RMR_Type )
  if ((HaveEL EL3) : Bool)
  then (do (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg RMR_EL3) 0 32))))
  else (do (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg RMR_EL1) 0 32))))

def RMR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : RMR_Type := value_name
  if ((HaveEL EL3) : Bool)
  then writeReg RMR_EL3 (Sail.BitVec.updateSubrange (← readReg RMR_EL3) 31 0 (BitVec.slice r 0 32))
  else writeReg RMR_EL1 (Sail.BitVec.updateSubrange (← readReg RMR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _RMR r

def SCTLR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : SCTLR_Type := value_name
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange (← readReg SCTLR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _SCTLR_NS r

def SDER32_EL3_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : SDER32_EL3_Type := value_name
  writeReg SDER32_EL2 (Sail.BitVec.updateSubrange (← readReg SDER32_EL2) 63 0 (BitVec.slice r 0 64))
  writeReg _SDER32_EL3 r

def TRFCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _TRFCR ) : SailM TRFCR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg TRFCR_EL1) 0 32)))

def TRFCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TRFCR_Type := value_name
  writeReg TRFCR_EL1 (Sail.BitVec.updateSubrange (← readReg TRFCR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _TRFCR r

def TTBCR2_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TTBCR2_Type := value_name
  writeReg TCR_EL1 (Sail.BitVec.updateSubrange (← readReg TCR_EL1) 63 32 (BitVec.slice r 0 32))
  writeReg _TTBCR2_NS r

def TTBCR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TTBCR_Type := value_name
  writeReg TCR_EL1 (Sail.BitVec.updateSubrange (← readReg TCR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _TTBCR_NS r

def TTBR0_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : TTBR0_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg TTBR0_S r
  else writeReg TTBR0_NS r

def TTBR1_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : TTBR1_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg TTBR1_S r
  else writeReg TTBR1_NS r

def VBAR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : VBAR_Type := value_name
  writeReg VBAR_EL1 (Sail.BitVec.updateSubrange (← readReg VBAR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _VBAR_NS r

def VDFSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : VDFSR_Type := value_name
  writeReg VSESR_EL2 (Sail.BitVec.updateSubrange (← readReg VSESR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _VDFSR r

def VDISR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _VDISR ) : SailM VDISR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg VDISR_EL2) 0 32)))

def VMPIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _VMPIDR ) : SailM VMPIDR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg VMPIDR_EL2) 0 32)))

def VMPIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : VMPIDR_Type := value_name
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange (← readReg VMPIDR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _VMPIDR r

def VPIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _VPIDR ) : SailM VPIDR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg VPIDR_EL2) 0 32)))

def VPIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : VPIDR_Type := value_name
  writeReg VPIDR_EL2 (Sail.BitVec.updateSubrange (← readReg VPIDR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _VPIDR r

def VTCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : VTCR_Type := value_name
  writeReg VTCR_EL2 (Sail.BitVec.updateSubrange (← readReg VTCR_EL2) 31 0 (BitVec.slice r 0 32))
  writeReg _VTCR r

def _update_DBGCLAIMCLR_Type_CLAIM (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_DBGCLAIMSET_Type_CLAIM (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_DBGDCCINT_Type_RX (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_DBGDCCINT_Type_TX (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_HRMR_Type_RR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_HSTR_Type_T0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_HSTR_Type_T1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_HSTR_Type_T10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_HSTR_Type_T11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_HSTR_Type_T12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_HSTR_Type_T13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_HSTR_Type_T15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_HSTR_Type_T2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_HSTR_Type_T3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_HSTR_Type_T5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_HSTR_Type_T6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_HSTR_Type_T7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_HSTR_Type_T8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_HSTR_Type_T9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_HTRFCR_Type_E0HTRE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_HTRFCR_Type_E2TRE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICC_HSRE_Type_DFB (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICC_HSRE_Type_DIB (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICC_HSRE_Type_SRE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICC_IGRPEN0_Type_Enable (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICC_IGRPEN1_Type_Enable (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICC_SRE_Type_DFB (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICC_SRE_Type_DIB (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICC_SRE_Type_SRE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICH_EISR_Type_Status0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICH_EISR_Type_Status1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICH_EISR_Type_Status10 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_ICH_EISR_Type_Status11 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_ICH_EISR_Type_Status12 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_ICH_EISR_Type_Status13 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_ICH_EISR_Type_Status14 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_ICH_EISR_Type_Status15 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_ICH_EISR_Type_Status2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICH_EISR_Type_Status3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ICH_EISR_Type_Status4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_ICH_EISR_Type_Status5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_ICH_EISR_Type_Status6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ICH_EISR_Type_Status7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_ICH_EISR_Type_Status8 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_ICH_EISR_Type_Status9 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_ICH_HCR_Type_EOIcount (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 27 x)

def _update_ICH_HCR_Type_En (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICH_HCR_Type_LRENPIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICH_HCR_Type_NPIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ICH_HCR_Type_TALL0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_ICH_HCR_Type_TALL1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_ICH_HCR_Type_TDIR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_ICH_HCR_Type_TSEI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_ICH_HCR_Type_UIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICH_HCR_Type_VGrp0DIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_ICH_HCR_Type_VGrp0EIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_ICH_HCR_Type_VGrp1DIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_ICH_HCR_Type_VGrp1EIE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ICH_HCR_Type_vSGIEOICount (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_ICH_MISR_Type_EOI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICH_MISR_Type_LRENP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICH_MISR_Type_NP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ICH_MISR_Type_VGrp0D (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_ICH_MISR_Type_VGrp0E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_ICH_MISR_Type_VGrp1D (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_ICH_MISR_Type_VGrp1E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ICV_IGRPEN0_Type_Enable (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICV_IGRPEN1_Type_Enable (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_RMR_Type_RR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_TRFCR_Type_E0TRE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_TRFCR_Type_E1TRE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_VMPIDR_Type_Aff0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_VMPIDR_Type_Aff1 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_VMPIDR_Type_Aff2 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_VPIDR_Type_Architecture (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_VPIDR_Type_Implementer (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_VPIDR_Type_PartNum (v : (BitVec 32)) (x : (BitVec 12)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 4 x)

def _update_VPIDR_Type_Revision (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_VPIDR_Type_Variant (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def CLIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CLIDR ) : SailM CLIDR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg CLIDR_EL1) 0 32)))

def CLIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CLIDR_Type := value_name
  writeReg CLIDR_EL1 (Sail.BitVec.updateSubrange (← readReg CLIDR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _CLIDR r

def ID_DFR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_DFR0 ) : SailM ID_DFR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_DFR0_EL1) 0 32)))

def ID_DFR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_DFR0_Type := value_name
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_DFR0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_DFR0 r

def ID_ISAR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_ISAR1 ) : SailM ID_ISAR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_ISAR1_EL1) 0 32)))

def ID_ISAR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_ISAR1_Type := value_name
  writeReg ID_ISAR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR1_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_ISAR1 r

def ID_ISAR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_ISAR2 ) : SailM ID_ISAR2_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_ISAR2_EL1) 0 32)))

def ID_ISAR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_ISAR2_Type := value_name
  writeReg ID_ISAR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR2_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_ISAR2 r

def ID_ISAR3_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_ISAR3 ) : SailM ID_ISAR3_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_ISAR3_EL1) 0 32)))

def ID_ISAR3_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_ISAR3_Type := value_name
  writeReg ID_ISAR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR3_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_ISAR3 r

def ID_ISAR4_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_ISAR4 ) : SailM ID_ISAR4_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_ISAR4_EL1) 0 32)))

def ID_ISAR4_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_ISAR4_Type := value_name
  writeReg ID_ISAR4_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR4_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_ISAR4 r

def ID_ISAR6_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_ISAR6 ) : SailM ID_ISAR6_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_ISAR6_EL1) 0 32)))

def ID_ISAR6_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_ISAR6_Type := value_name
  writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange (← readReg ID_ISAR6_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_ISAR6 r

def ID_MMFR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_MMFR0 ) : SailM ID_MMFR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_MMFR0_EL1) 0 32)))

def ID_MMFR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_MMFR0_Type := value_name
  writeReg ID_MMFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_MMFR0 r

def ID_MMFR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_MMFR1 ) : SailM ID_MMFR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_MMFR1_EL1) 0 32)))

def ID_MMFR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_MMFR1_Type := value_name
  writeReg ID_MMFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR1_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_MMFR1 r

def ID_MMFR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_MMFR2 ) : SailM ID_MMFR2_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_MMFR2_EL1) 0 32)))

def ID_MMFR2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_MMFR2_Type := value_name
  writeReg ID_MMFR2_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR2_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_MMFR2 r

def ID_MMFR3_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_MMFR3 ) : SailM ID_MMFR3_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_MMFR3_EL1) 0 32)))

def ID_MMFR3_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_MMFR3_Type := value_name
  writeReg ID_MMFR3_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR3_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_MMFR3 r

def ID_MMFR4_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_MMFR4 ) : SailM ID_MMFR4_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_MMFR4_EL1) 0 32)))

def ID_MMFR4_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_MMFR4_Type := value_name
  writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange (← readReg ID_MMFR4_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_MMFR4 r

def ID_PFR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_PFR0 ) : SailM ID_PFR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_PFR0_EL1) 0 32)))

def ID_PFR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_PFR0_Type := value_name
  writeReg ID_PFR0_EL1 (Sail.BitVec.updateSubrange (← readReg ID_PFR0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_PFR0 r

def ID_PFR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _ID_PFR1 ) : SailM ID_PFR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg ID_PFR1_EL1) 0 32)))

def ID_PFR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ID_PFR1_Type := value_name
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange (← readReg ID_PFR1_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _ID_PFR1 r

def MIDR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _MIDR ) : SailM MIDR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg MIDR_EL1) 0 32)))

def MIDR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MIDR_Type := value_name
  writeReg MIDR_EL1 (Sail.BitVec.updateSubrange (← readReg MIDR_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _MIDR r

def MVFR0_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _MVFR0 ) : SailM MVFR0_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg MVFR0_EL1) 0 32)))

def MVFR0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MVFR0_Type := value_name
  writeReg MVFR0_EL1 (Sail.BitVec.updateSubrange (← readReg MVFR0_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _MVFR0 r

def MVFR1_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _MVFR1 ) : SailM MVFR1_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg MVFR1_EL1) 0 32)))

def MVFR1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MVFR1_Type := value_name
  writeReg MVFR1_EL1 (Sail.BitVec.updateSubrange (← readReg MVFR1_EL1) 31 0 (BitVec.slice r 0 32))
  writeReg _MVFR1 r

def Mk_CLIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_ID_ISAR6_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_NMRR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_PMCEID0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_PMCEID1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_PMCEID2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_PMCEID3_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def NMRR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : NMRR_Type := value_name
  writeReg MAIR_EL1 (Sail.BitVec.updateSubrange (← readReg MAIR_EL1) 63 32 (BitVec.slice r 0 32))
  writeReg _NMRR_NS r

def PMCEID0_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCEID0_Type := value_name
  writeReg PMCEID0_EL0 (Sail.BitVec.updateSubrange (← readReg PMCEID0_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _PMCEID0 r

def PMCEID1_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCEID1_Type := value_name
  writeReg PMCEID1_EL0 (Sail.BitVec.updateSubrange (← readReg PMCEID1_EL0) 31 0 (BitVec.slice r 0 32))
  writeReg _PMCEID1 r

def PMCEID2_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCEID2_Type := value_name
  writeReg PMCEID0_EL0 (Sail.BitVec.updateSubrange (← readReg PMCEID0_EL0) 63 32 (BitVec.slice r 0 32))
  writeReg _PMCEID2 r

def PMCEID3_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : PMCEID3_Type := value_name
  writeReg PMCEID1_EL0 (Sail.BitVec.updateSubrange (← readReg PMCEID1_EL0) 63 32 (BitVec.slice r 0 32))
  writeReg _PMCEID3 r

def _get_ID_DFR0_EL1_Type_CopDbg (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_DFR0_Type_CopDbg (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_CCSIDR_Type_Associativity (v : (BitVec 32)) (x : (BitVec 21)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 3 x)

def _update_CCSIDR_Type_LineSize (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)

def _update_ID_DFR0_Type_CopDbg (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_DFR0_Type_CopSDbg (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_DFR0_Type_CopTrc (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_DFR0_Type_MMapDbg (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_DFR0_Type_MMapTrc (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_ID_DFR0_Type_MProfDbg (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_DFR0_Type_PerfMon (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_DFR0_Type_TraceFilt (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_DFR1_Type_MTPMU (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_ISAR0_Type_BitCount (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_ISAR0_Type_BitField (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_ISAR0_Type_CmpBranch (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_ISAR0_Type_Coproc (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_ID_ISAR0_Type_Debug (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_ISAR0_Type_Divide (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_ISAR0_Type_Swap (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_ISAR1_Type_Endian (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_ISAR1_Type_Except (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_ISAR1_Type_Except_AR (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_ISAR1_Type_Extend (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_ISAR1_Type_IfThen (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_ID_ISAR1_Type_Immediate (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_ISAR1_Type_Interwork (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_ISAR1_Type_Jazelle (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_ISAR2_Type_LoadStore (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_ISAR2_Type_MemHint (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_ISAR2_Type_Mult (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_ISAR2_Type_MultS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_ID_ISAR2_Type_MultU (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_ISAR2_Type_MultiAccessInt (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_ISAR2_Type_PSR_AR (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_ISAR2_Type_Reversal (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_ISAR3_Type_SIMD (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_ISAR3_Type_SVC (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_ISAR3_Type_Saturate (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_ISAR3_Type_SynchPrim (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_ISAR3_Type_T32Copy (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_ISAR3_Type_T32EE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_ISAR3_Type_TabBranch (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_ID_ISAR3_Type_TrueNOP (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_ISAR4_Type_Barrier (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_ID_ISAR4_Type_PSR_M (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_ISAR4_Type_SMC (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_ISAR4_Type_SWP_frac (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_ISAR4_Type_SynchPrim_frac (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_ISAR4_Type_Unpriv (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_ISAR4_Type_WithShifts (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_ISAR4_Type_Writeback (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_ISAR5_Type_AES (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_ISAR5_Type_CRC32 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_ID_ISAR5_Type_RDM (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_ISAR5_Type_SEVL (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_ISAR5_Type_SHA1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_ISAR5_Type_SHA2 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_ISAR5_Type_VCMA (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_ISAR6_Type_BF16 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_ISAR6_Type_FHM (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_ISAR6_Type_I8MM (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_ISAR6_Type_JSCVT (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_ISAR6_Type_SPECRES (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_ID_MMFR0_Type_AuxReg (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_MMFR0_Type_FCSE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_MMFR0_Type_InnerShr (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_MMFR0_Type_OuterShr (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_MMFR0_Type_PMSA (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_MMFR0_Type_ShareLvl (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_MMFR0_Type_TCM (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_ID_MMFR0_Type_VMSA (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_MMFR1_Type_BPred (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_MMFR1_Type_L1Hvd (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_ID_MMFR1_Type_L1HvdSW (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_MMFR1_Type_L1HvdVA (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_MMFR1_Type_L1TstCln (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_MMFR1_Type_L1Uni (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_MMFR1_Type_L1UniSW (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_MMFR1_Type_L1UniVA (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_MMFR2_Type_HWAccFlg (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_MMFR2_Type_HvdTLB (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_MMFR2_Type_L1HvdBG (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_MMFR2_Type_L1HvdFG (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_MMFR2_Type_L1HvdRng (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_MMFR2_Type_MemBarr (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_MMFR2_Type_UniTLB (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_ID_MMFR2_Type_WFIStall (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_MMFR3_Type_BPMaint (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_MMFR3_Type_CMaintSW (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_MMFR3_Type_CMaintVA (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_MMFR3_Type_CMemSz (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_MMFR3_Type_CohWalk (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_MMFR3_Type_MaintBcst (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_MMFR3_Type_Supersec (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_MMFR4_Type_CCIDX (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_MMFR5_Type_ETS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_PFR0_Type_AMU (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_PFR0_Type_CSV2 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_ID_PFR0_Type_RAS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_PFR0_Type_State0 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_PFR0_Type_State1 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_PFR0_Type_State2 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_PFR0_Type_State3 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_PFR1_Type_GIC (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_PFR1_Type_GenTimer (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_ID_PFR1_Type_MProgMod (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_PFR1_Type_ProgMod (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_PFR1_Type_Sec_frac (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_PFR1_Type_Security (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_PFR1_Type_Virt_frac (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_PFR1_Type_Virtualization (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_MIDR_Type_Architecture (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_MIDR_Type_Implementer (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 24 x)

def _update_MIDR_Type_PartNum (v : (BitVec 32)) (x : (BitVec 12)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 4 x)

def _update_MIDR_Type_Revision (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_MIDR_Type_Variant (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_MPIDR_Type_Aff0 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)

def _update_MPIDR_Type_Aff1 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 8 x)

def _update_MPIDR_Type_Aff2 (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _update_MVFR0_Type_FPDP (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_MVFR0_Type_FPDivide (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_MVFR0_Type_FPRound (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_MVFR0_Type_FPSP (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_MVFR0_Type_FPShVec (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_MVFR0_Type_FPSqrt (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_MVFR0_Type_FPTrap (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_MVFR0_Type_SIMDReg (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_MVFR1_Type_FPDNaN (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_MVFR1_Type_FPFtZ (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_MVFR1_Type_FPHP (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_MVFR1_Type_SIMDFMAC (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_MVFR1_Type_SIMDHP (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_MVFR1_Type_SIMDInt (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_MVFR1_Type_SIMDLS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_MVFR1_Type_SIMDSP (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_MVFR2_Type_FPMisc (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_MVFR2_Type_SIMDMisc (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_PRRR_Type_DS0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PRRR_Type_DS1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PRRR_Type_NS0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PRRR_Type_NS1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def undefined_ICC_BPR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def ICC_BPR1_EL1_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_BPR1_EL1_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg ICC_BPR1_EL1_S r
  else writeReg ICC_BPR1_EL1_NS r

def undefined_ICC_CTLR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def ICC_CTLR_EL1_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_CTLR_EL1_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg ICC_CTLR_EL1_S r
  else writeReg ICC_CTLR_EL1_NS r

def undefined_ICC_IGRPEN1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def ICC_IGRPEN1_EL1_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_IGRPEN1_EL1_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg ICC_IGRPEN1_EL1_S r
  else writeReg ICC_IGRPEN1_EL1_NS r

def undefined_ICC_SRE_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def ICC_SRE_EL1_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_SRE_EL1_Type := value_name
  if ((←((ELUsingAArch32 EL3) <&&> (do
       (pure (BEq.beq (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
  then writeReg ICC_SRE_EL1_S r
  else writeReg ICC_SRE_EL1_NS r

def MPAM3_EL3_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : MPAM3_EL3_Type := value_name
  writeReg MPAM2_EL2 (BitVec.update (← readReg MPAM2_EL2) 63 (Bit (BitVec.slice r 63 1)))
  writeReg _MPAM3_EL3 r

def Mk_ICC_BPR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_ICC_CTLR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_ICC_IGRPEN1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_ICC_SRE_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_PAR_EL1_Type (v : (BitVec 128)) : (BitVec 128) :=
  v

def TTBR0_EL2_write (value_name : (BitVec 128)) : SailM Unit := do
  let r : TTBR0_EL2_Type := value_name
  writeReg HTTBR (Sail.BitVec.updateSubrange (← readReg HTTBR) 47 1 (BitVec.slice r 1 47))
  writeReg _TTBR0_EL2 r

def VTTBR_EL2_write (value_name : (BitVec 128)) : SailM Unit := do
  let r : VTTBR_EL2_Type := value_name
  writeReg VTTBR (Sail.BitVec.updateSubrange (← readReg VTTBR) 63 0 (BitVec.slice r 0 64))
  writeReg _VTTBR_EL2 r

def _update_ICC_IGRPEN1_EL1_Type_Enable (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ICC_SRE_EL1_Type_DFB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ICC_SRE_EL1_Type_DIB (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ICC_SRE_EL1_Type_SRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def EncodePARange (_ : Unit) : SailM (BitVec 4) := do
  match (← readReg __supported_pa_size) with
  | 32 => (pure 0b0000#4)
  | 36 => (pure 0b0001#4)
  | 40 => (pure 0b0010#4)
  | 42 => (pure 0b0011#4)
  | 44 => (pure 0b0100#4)
  | 48 => (pure 0b0101#4)
  | 52 =>
    (do
      sail_assert (← (Have52BitPAExt ())) "src/reset.sail:79.33-79.34"
      (pure 0b0110#4))
  | 56 =>
    (do
      sail_assert (← (Have56BitPAExt ())) "src/reset.sail:83.33-83.34"
      (pure 0b0111#4))
  | _ => (pure 0b0110#4)

def EncodeVARange (_ : Unit) : SailM (BitVec 4) := do
  match (← readReg __supported_va_size) with
  | 48 => (pure 0b0000#4)
  | 52 =>
    (do
      sail_assert (← (Have52BitVAExt ())) "src/reset.sail:98.33-98.34"
      (pure 0b0001#4))
  | 56 =>
    (do
      sail_assert (← (Have56BitVAExt ())) "src/reset.sail:102.33-102.34"
      (pure 0b0001#4))
  | _ => (do (undefined_bitvector 4))

/-- Type quantifiers: i : Int -/
def IsG1ActivityMonitorImplemented (i : Int) : SailM Bool := do
  sail_assert ((0 ≤b i) && (i <b 16)) "src/impdefs.sail:870.26-870.27"
  (pure ((BitVec.access (← readReg __g1_activity_monitor_implemented) i) == 1#1))

/-- Type quantifiers: i : Int -/
def IsG1ActivityMonitorOffsetImplemented (i : Int) : SailM Bool := do
  sail_assert ((0 ≤b i) && (i <b 16)) "src/impdefs.sail:877.26-877.27"
  (pure ((BitVec.access (← readReg __g1_activity_monitor_offset_implemented) i) == 1#1))

def Mk_CCSIDR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_CNTFID0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def Mk_PMCEID0_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def Mk_PMCEID1_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ERRIDR_EL1_Type_NUM (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _get_ID_AA64DFR0_EL1_Type_BRPs (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_AA64DFR0_EL1_Type_CTX_CMPs (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_ID_AA64DFR0_EL1_Type_PMUVer (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_AA64DFR0_EL1_Type_TraceFilt (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_ID_AA64DFR0_EL1_Type_TraceVer (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_AA64DFR0_EL1_Type_WRPs (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_AA64PFR0_EL1_Type_AdvSIMD (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_AA64PFR0_EL1_Type_EL0 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_AA64PFR0_EL1_Type_EL1 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_AA64PFR0_EL1_Type_EL2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_AA64PFR0_EL1_Type_EL3 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_AA64PFR0_EL1_Type_GIC (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_AA64PFR0_EL1_Type_MPAM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 43 40)

def _get_ID_AA64PFR1_EL1_Type_MPAM_frac (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ICC_CTLR_EL1_Type_A3V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_ICC_CTLR_EL1_Type_ExtRange (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_ICC_CTLR_EL1_Type_IDbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 11 x)

def _update_ICC_CTLR_EL1_Type_PRIbits (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 8 x)

/-- Type quantifiers: k_cold : Bool -/
def __Reset (cold : Bool) : SailM Unit := do
  writeReg __last_cycle_count 0
  writeReg __last_branch_valid false
  writeReg sp_rel_access_pc (Ones (n := 64))
  writeReg __cycle_count 0

def _TLBInvalidate (_ : Unit) : Unit :=
  ()

/-- Type quantifiers: k_cold_reset : Bool -/
def ResetExternalDebugRegisters (cold_reset : Bool) : SailM Unit := do
  writeReg EDPRSR (Sail.BitVec.updateSubrange (← readReg EDPRSR) 0 0 1#1)
  writeReg EDPRSR (Sail.BitVec.updateSubrange (← readReg EDPRSR) 3 3 1#1)
  writeReg EDPRSR (Sail.BitVec.updateSubrange (← readReg EDPRSR) 5 5 1#1)
  if (cold_reset : Bool)
  then
    (do
      (EDSCR_write (_update_EDSCR_Type_STATUS (← (EDSCR_read ())) 0b000010#6))
      (EDSCR_write (_update_EDSCR_Type_RW (← (EDSCR_read ())) 0b1111#4)))
  else (pure ())

def AArch32_ITAdvance (_ : Unit) : SailM Unit := do
  if (((Sail.BitVec.extractLsb (← readReg PSTATE).IT 2 0) == 0b000#3) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with IT := 0b00000000#8 }
  else writeReg PSTATE { (← readReg PSTATE) with IT := ← (do (pure (Sail.BitVec.updateSubrange (← readReg PSTATE).IT 4 0 ((Sail.BitVec.extractLsb (← readReg PSTATE).IT 4 0) <<< 1)))) }

def SSAdvance (_ : Unit) : SailM Unit := do
  let target ← (( do (DebugTarget ()) ) : SailM (BitVec 2) )
  let step_enabled ← (( do (pure (! (← (ELUsingAArch32 target)))) <&&> (do (pure ((_get_MDSCR_EL1_Type_SS (← readReg MDSCR_EL1)) == 1#1))) ) : SailM Bool )
  let active_not_pending ← (( do (pure step_enabled) <&&> (do (pure ((← readReg PSTATE).SS == 1#1))) ) : SailM Bool )
  if (active_not_pending : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with SS := 0#1 }
  else (pure ())

/-- Type quantifiers: N : Nat, N ≥ 0 -/
def NextInstrAddr (N : Nat) : SailM (BitVec N) := do
  sail_assert ((0 ≤b (N -i 1)) && ((N -i 1) <b 64)) "src/fetch.sail:190.50-190.51"
  (pure (Sail.BitVec.extractLsb (BitVec.addInt (← readReg _PC) (fdiv_int (← (ThisInstrLength ())) 8)) (N -i 1) 0))

def AArch64_UndefinedFault (_ : Unit) : SailM Unit := do
  let route_to_el2 ← (( do (pure ((← readReg PSTATE).EL == EL0)) <&&> (do (EL2Enabled ())) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1))) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_Uncategorized) ) : SailM ExceptionRecord )
  if (((BitVec.toNat (← readReg PSTATE).EL) >b (BitVec.toNat EL1)) : Bool)
  then (AArch64_TakeException (← readReg PSTATE).EL except preferred_exception_return vect_offset)
  else
    (do
      if (route_to_el2 : Bool)
      then (AArch64_TakeException EL2 except preferred_exception_return vect_offset)
      else (AArch64_TakeException EL1 except preferred_exception_return vect_offset))

def LDST64BTrap (target_el : (BitVec 2)) (iss : (BitVec 25)) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_LDST64BTrap) ) : SailM ExceptionRecord )
  let except : ExceptionRecord := { except with syndrome := iss }
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)

def AArch64_CheckForSMCUndefOrTrap (imm : (BitVec 16)) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord ()) ) : SailM ExceptionRecord )
  let vect_offset ← (( do (undefined_int ()) ) : SailM Int )
  if (((← readReg PSTATE).EL == EL0) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  if ((←((pure ((! (←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do (EL2Enabled ())) <&&> (do (pure ((_get_HCR_EL2_Type_TSC (← readReg HCR_EL2)) == 1#1)))))) && (HaveEL EL3))) <&&> (do
       (pure ((_get_SCR_EL3_Type_SMD (← readReg SCR_EL3)) == 1#1))))) : Bool)
  then (sailThrow ((Error_Undefined ())) : SailM Unit)
  else (pure ())
  let route_to_el2 : Bool := false
  let route_to_el2 ← (( do
    if ((! (HaveEL EL3)) : Bool)
    then
      (do
        if ((←((pure ((← readReg PSTATE).EL == EL1)) <&&> (do
             (EL2Enabled ())))) : Bool)
        then
          (do
            if ((←((HaveNVExt ()) <&&> (do
                 (pure ((_get_HCR_EL2_Type_NV (← readReg HCR_EL2)) == 1#1))) <&&> (do
                 (pure ((_get_HCR_EL2_Type_TSC (← readReg HCR_EL2)) == 1#1))))) : Bool)
            then (pure true)
            else sailThrow ((Error_Undefined ())))
        else sailThrow ((Error_Undefined ())))
    else (do (pure ((← readReg PSTATE).EL == EL1)) <&&> (do (EL2Enabled ())) <&&> (do (pure ((_get_HCR_EL2_Type_TSC (← readReg HCR_EL2)) == 1#1)))) ) : SailM Bool )
  if (route_to_el2 : Bool)
  then
    (do
      let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
      let vect_offset := (BitVec.toNat 0x0#4)
      let except ← (( do (ExceptionSyndrome Exception_MonitorCall) ) : SailM ExceptionRecord )
      let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 imm) }
      let except : ExceptionRecord := { except with trappedsyscallinst := true }
      (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
  else (pure ())

def AArch64_MonitorModeTrap (_ : Unit) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_Uncategorized) ) : SailM ExceptionRecord )
  if ((← (IsSecureEL2Enabled ())) : Bool)
  then (AArch64_TakeException EL2 except preferred_exception_return vect_offset)
  else (pure ())
  (AArch64_TakeException EL3 except preferred_exception_return vect_offset)

def undefined_HSTR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_HSTR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_HSTR_EL2_Type_T0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_HSTR_EL2_Type_T0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_HSTR_Type_T0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_HSTR_EL2_Type_T1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_HSTR_EL2_Type_T1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_HSTR_Type_T1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_HSTR_EL2_Type_T10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_HSTR_EL2_Type_T10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_HSTR_Type_T10 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_HSTR_EL2_Type_T11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_HSTR_EL2_Type_T11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_HSTR_Type_T11 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_HSTR_EL2_Type_T12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_HSTR_EL2_Type_T12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_HSTR_Type_T12 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_HSTR_EL2_Type_T13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_HSTR_EL2_Type_T13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_HSTR_Type_T13 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_HSTR_EL2_Type_T15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_HSTR_EL2_Type_T15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_HSTR_Type_T15 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_HSTR_EL2_Type_T2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_HSTR_EL2_Type_T2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_HSTR_Type_T2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_HSTR_EL2_Type_T3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_HSTR_EL2_Type_T3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_HSTR_Type_T3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_HSTR_EL2_Type_T5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_HSTR_EL2_Type_T5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_HSTR_Type_T5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_HSTR_EL2_Type_T6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_HSTR_EL2_Type_T6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_HSTR_Type_T6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_HSTR_EL2_Type_T7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_HSTR_EL2_Type_T7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_HSTR_Type_T7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_HSTR_EL2_Type_T8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_HSTR_EL2_Type_T8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_HSTR_Type_T8 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_HSTR_EL2_Type_T9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_HSTR_EL2_Type_T9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_HSTR_Type_T9 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def AArch64_SoftwareBreakpoint (immediate : (BitVec 16)) : SailM Unit := do
  let route_to_el2 ← (( do (pure ((← readReg PSTATE).EL == EL0)) <||> (do (pure ((← readReg PSTATE).EL == EL1))) <&&> (do (EL2Enabled ())) <&&> (do (pure ((_get_HCR_EL2_Type_TGE (← readReg HCR_EL2)) == 1#1)) <||> (do (pure ((_get_MDCR_EL2_Type_TDE (← readReg MDCR_EL2)) == 1#1)))) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_SoftwareBreakpoint) ) : SailM ExceptionRecord )
  let except : ExceptionRecord := { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 immediate) }
  if (((BitVec.toNat (← readReg PSTATE).EL) >b (BitVec.toNat EL1)) : Bool)
  then (AArch64_TakeException (← readReg PSTATE).EL except preferred_exception_return vect_offset)
  else
    (do
      if (route_to_el2 : Bool)
      then (AArch64_TakeException EL2 except preferred_exception_return vect_offset)
      else (AArch64_TakeException EL1 except preferred_exception_return vect_offset))

def undefined_MDSELR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MDSELR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PMCCNTR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def _get_PMCCNTR_EL0_Type_CCNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _update_PMCCNTR_EL0_Type_CCNT (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_PMCCNTR_Type_CCNT (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _update_PMCCNTSVR_EL1_Type_CCNT (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)

def _get_PMCCNTR_Type_CCNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def _get_PMCCNTSVR_EL1_Type_CCNT (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)

def undefined_PMSICR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMSICR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMSICR_EL1_Type_COUNT (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_PMSICR_EL1_Type_COUNT (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _get_PMSICR_EL1_Type_ECOUNT (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)

def _update_PMSICR_EL1_Type_ECOUNT (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 56 x)

def undefined_PMSIRR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMSIRR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMSIRR_EL1_Type_INTERVAL (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 31 8)

def _update_PMSIRR_EL1_Type_INTERVAL (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 8 x)

def _get_PMSIRR_EL1_Type_RND (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_PMSIRR_EL1_Type_RND (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def undefined_PMBPTR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMBPTR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PMSDSFR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMSDSFR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMSDSFR_EL1_Type_S0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_PMSDSFR_EL1_Type_S0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_ERXGSR_EL1_Type_S0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_ERXGSR_EL1_Type_S0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMSDSFR_EL1_Type_S1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_PMSDSFR_EL1_Type_S1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_ERXGSR_EL1_Type_S1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_ERXGSR_EL1_Type_S1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMSDSFR_EL1_Type_S10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_PMSDSFR_EL1_Type_S10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_ERXGSR_EL1_Type_S10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_ERXGSR_EL1_Type_S10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMSDSFR_EL1_Type_S11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_PMSDSFR_EL1_Type_S11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_ERXGSR_EL1_Type_S11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_ERXGSR_EL1_Type_S11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMSDSFR_EL1_Type_S12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_PMSDSFR_EL1_Type_S12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_ERXGSR_EL1_Type_S12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_ERXGSR_EL1_Type_S12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMSDSFR_EL1_Type_S13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_PMSDSFR_EL1_Type_S13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_ERXGSR_EL1_Type_S13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_ERXGSR_EL1_Type_S13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMSDSFR_EL1_Type_S14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_PMSDSFR_EL1_Type_S14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_ERXGSR_EL1_Type_S14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_ERXGSR_EL1_Type_S14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMSDSFR_EL1_Type_S15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_PMSDSFR_EL1_Type_S15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_ERXGSR_EL1_Type_S15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_ERXGSR_EL1_Type_S15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMSDSFR_EL1_Type_S16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_PMSDSFR_EL1_Type_S16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_ERXGSR_EL1_Type_S16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_ERXGSR_EL1_Type_S16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMSDSFR_EL1_Type_S17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_PMSDSFR_EL1_Type_S17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_ERXGSR_EL1_Type_S17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_ERXGSR_EL1_Type_S17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMSDSFR_EL1_Type_S18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_PMSDSFR_EL1_Type_S18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_ERXGSR_EL1_Type_S18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_ERXGSR_EL1_Type_S18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMSDSFR_EL1_Type_S19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_PMSDSFR_EL1_Type_S19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_ERXGSR_EL1_Type_S19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_ERXGSR_EL1_Type_S19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMSDSFR_EL1_Type_S2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_PMSDSFR_EL1_Type_S2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_ERXGSR_EL1_Type_S2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_ERXGSR_EL1_Type_S2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMSDSFR_EL1_Type_S20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_PMSDSFR_EL1_Type_S20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_ERXGSR_EL1_Type_S20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_ERXGSR_EL1_Type_S20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMSDSFR_EL1_Type_S21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_PMSDSFR_EL1_Type_S21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_ERXGSR_EL1_Type_S21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_ERXGSR_EL1_Type_S21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMSDSFR_EL1_Type_S22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_PMSDSFR_EL1_Type_S22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_ERXGSR_EL1_Type_S22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_ERXGSR_EL1_Type_S22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMSDSFR_EL1_Type_S23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_PMSDSFR_EL1_Type_S23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_ERXGSR_EL1_Type_S23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_ERXGSR_EL1_Type_S23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMSDSFR_EL1_Type_S24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_PMSDSFR_EL1_Type_S24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_ERXGSR_EL1_Type_S24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_ERXGSR_EL1_Type_S24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMSDSFR_EL1_Type_S25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_PMSDSFR_EL1_Type_S25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_ERXGSR_EL1_Type_S25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_ERXGSR_EL1_Type_S25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMSDSFR_EL1_Type_S26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_PMSDSFR_EL1_Type_S26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_ERXGSR_EL1_Type_S26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_ERXGSR_EL1_Type_S26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMSDSFR_EL1_Type_S27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_PMSDSFR_EL1_Type_S27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_ERXGSR_EL1_Type_S27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_ERXGSR_EL1_Type_S27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMSDSFR_EL1_Type_S28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_PMSDSFR_EL1_Type_S28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_ERXGSR_EL1_Type_S28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_ERXGSR_EL1_Type_S28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMSDSFR_EL1_Type_S29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_PMSDSFR_EL1_Type_S29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_ERXGSR_EL1_Type_S29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_ERXGSR_EL1_Type_S29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMSDSFR_EL1_Type_S3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_PMSDSFR_EL1_Type_S3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_ERXGSR_EL1_Type_S3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_ERXGSR_EL1_Type_S3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMSDSFR_EL1_Type_S30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_PMSDSFR_EL1_Type_S30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_ERXGSR_EL1_Type_S30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_ERXGSR_EL1_Type_S30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMSDSFR_EL1_Type_S31 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_PMSDSFR_EL1_Type_S31 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_ERXGSR_EL1_Type_S31 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_ERXGSR_EL1_Type_S31 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMSDSFR_EL1_Type_S32 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _update_PMSDSFR_EL1_Type_S32 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_ERXGSR_EL1_Type_S32 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _get_ERXGSR_EL1_Type_S32 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _get_PMSDSFR_EL1_Type_S33 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _update_PMSDSFR_EL1_Type_S33 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _update_ERXGSR_EL1_Type_S33 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _get_ERXGSR_EL1_Type_S33 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _get_PMSDSFR_EL1_Type_S34 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)

def _update_PMSDSFR_EL1_Type_S34 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _update_ERXGSR_EL1_Type_S34 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _get_ERXGSR_EL1_Type_S34 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)

def _get_PMSDSFR_EL1_Type_S35 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)

def _update_PMSDSFR_EL1_Type_S35 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _update_ERXGSR_EL1_Type_S35 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _get_ERXGSR_EL1_Type_S35 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)

def _get_PMSDSFR_EL1_Type_S36 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)

def _update_PMSDSFR_EL1_Type_S36 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _update_ERXGSR_EL1_Type_S36 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _get_ERXGSR_EL1_Type_S36 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)

def _get_PMSDSFR_EL1_Type_S37 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)

def _update_PMSDSFR_EL1_Type_S37 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _update_ERXGSR_EL1_Type_S37 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _get_ERXGSR_EL1_Type_S37 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)

def _get_PMSDSFR_EL1_Type_S38 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)

def _update_PMSDSFR_EL1_Type_S38 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _update_ERXGSR_EL1_Type_S38 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)

def _get_ERXGSR_EL1_Type_S38 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)

def _get_PMSDSFR_EL1_Type_S39 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 39 39)

def _update_PMSDSFR_EL1_Type_S39 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)

def _update_ERXGSR_EL1_Type_S39 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)

def _get_ERXGSR_EL1_Type_S39 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 39 39)

def _get_PMSDSFR_EL1_Type_S4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_PMSDSFR_EL1_Type_S4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_ERXGSR_EL1_Type_S4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_ERXGSR_EL1_Type_S4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMSDSFR_EL1_Type_S40 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)

def _update_PMSDSFR_EL1_Type_S40 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _update_ERXGSR_EL1_Type_S40 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _get_ERXGSR_EL1_Type_S40 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)

def _get_PMSDSFR_EL1_Type_S41 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)

def _update_PMSDSFR_EL1_Type_S41 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _update_ERXGSR_EL1_Type_S41 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _get_ERXGSR_EL1_Type_S41 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)

def _get_PMSDSFR_EL1_Type_S42 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 42 42)

def _update_PMSDSFR_EL1_Type_S42 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _update_ERXGSR_EL1_Type_S42 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)

def _get_ERXGSR_EL1_Type_S42 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 42 42)

def _get_PMSDSFR_EL1_Type_S43 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)

def _update_PMSDSFR_EL1_Type_S43 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _update_ERXGSR_EL1_Type_S43 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _get_ERXGSR_EL1_Type_S43 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)

def _get_PMSDSFR_EL1_Type_S44 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)

def _update_PMSDSFR_EL1_Type_S44 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_ERXGSR_EL1_Type_S44 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _get_ERXGSR_EL1_Type_S44 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)

def _get_PMSDSFR_EL1_Type_S45 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)

def _update_PMSDSFR_EL1_Type_S45 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _update_ERXGSR_EL1_Type_S45 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _get_ERXGSR_EL1_Type_S45 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)

def _get_PMSDSFR_EL1_Type_S46 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)

def _update_PMSDSFR_EL1_Type_S46 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _update_ERXGSR_EL1_Type_S46 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _get_ERXGSR_EL1_Type_S46 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)

def _get_PMSDSFR_EL1_Type_S47 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 47 47)

def _update_PMSDSFR_EL1_Type_S47 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 47 x)

def _update_ERXGSR_EL1_Type_S47 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 47 x)

def _get_ERXGSR_EL1_Type_S47 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 47 47)

def _get_PMSDSFR_EL1_Type_S48 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _update_PMSDSFR_EL1_Type_S48 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _update_ERXGSR_EL1_Type_S48 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _get_ERXGSR_EL1_Type_S48 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _get_PMSDSFR_EL1_Type_S49 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)

def _update_PMSDSFR_EL1_Type_S49 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def _update_ERXGSR_EL1_Type_S49 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def _get_ERXGSR_EL1_Type_S49 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)

def _get_PMSDSFR_EL1_Type_S5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_PMSDSFR_EL1_Type_S5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_ERXGSR_EL1_Type_S5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_ERXGSR_EL1_Type_S5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMSDSFR_EL1_Type_S50 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)

def _update_PMSDSFR_EL1_Type_S50 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _update_ERXGSR_EL1_Type_S50 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _get_ERXGSR_EL1_Type_S50 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)

def _get_PMSDSFR_EL1_Type_S51 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 51 51)

def _update_PMSDSFR_EL1_Type_S51 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)

def _update_ERXGSR_EL1_Type_S51 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)

def _get_ERXGSR_EL1_Type_S51 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 51 51)

def _get_PMSDSFR_EL1_Type_S52 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)

def _update_PMSDSFR_EL1_Type_S52 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _update_ERXGSR_EL1_Type_S52 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _get_ERXGSR_EL1_Type_S52 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)

def _get_PMSDSFR_EL1_Type_S53 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)

def _update_PMSDSFR_EL1_Type_S53 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _update_ERXGSR_EL1_Type_S53 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _get_ERXGSR_EL1_Type_S53 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)

def _get_PMSDSFR_EL1_Type_S54 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)

def _update_PMSDSFR_EL1_Type_S54 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _update_ERXGSR_EL1_Type_S54 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _get_ERXGSR_EL1_Type_S54 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)

def _get_PMSDSFR_EL1_Type_S55 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)

def _update_PMSDSFR_EL1_Type_S55 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _update_ERXGSR_EL1_Type_S55 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _get_ERXGSR_EL1_Type_S55 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)

def _get_PMSDSFR_EL1_Type_S56 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)

def _update_PMSDSFR_EL1_Type_S56 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _update_ERXGSR_EL1_Type_S56 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _get_ERXGSR_EL1_Type_S56 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)

def _get_PMSDSFR_EL1_Type_S57 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)

def _update_PMSDSFR_EL1_Type_S57 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _update_ERXGSR_EL1_Type_S57 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _get_ERXGSR_EL1_Type_S57 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)

def _get_PMSDSFR_EL1_Type_S58 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _update_PMSDSFR_EL1_Type_S58 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _update_ERXGSR_EL1_Type_S58 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _get_ERXGSR_EL1_Type_S58 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _get_PMSDSFR_EL1_Type_S59 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _update_PMSDSFR_EL1_Type_S59 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_ERXGSR_EL1_Type_S59 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _get_ERXGSR_EL1_Type_S59 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _get_PMSDSFR_EL1_Type_S6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_PMSDSFR_EL1_Type_S6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_ERXGSR_EL1_Type_S6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_ERXGSR_EL1_Type_S6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMSDSFR_EL1_Type_S60 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _update_PMSDSFR_EL1_Type_S60 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _update_ERXGSR_EL1_Type_S60 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _get_ERXGSR_EL1_Type_S60 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _get_PMSDSFR_EL1_Type_S61 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _update_PMSDSFR_EL1_Type_S61 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_ERXGSR_EL1_Type_S61 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _get_ERXGSR_EL1_Type_S61 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _get_PMSDSFR_EL1_Type_S62 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _update_PMSDSFR_EL1_Type_S62 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_ERXGSR_EL1_Type_S62 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _get_ERXGSR_EL1_Type_S62 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _get_PMSDSFR_EL1_Type_S63 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _update_PMSDSFR_EL1_Type_S63 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_ERXGSR_EL1_Type_S63 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _get_ERXGSR_EL1_Type_S63 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_PMSDSFR_EL1_Type_S7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_PMSDSFR_EL1_Type_S7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_ERXGSR_EL1_Type_S7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_ERXGSR_EL1_Type_S7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMSDSFR_EL1_Type_S8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_PMSDSFR_EL1_Type_S8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_ERXGSR_EL1_Type_S8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_ERXGSR_EL1_Type_S8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMSDSFR_EL1_Type_S9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_PMSDSFR_EL1_Type_S9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_ERXGSR_EL1_Type_S9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_ERXGSR_EL1_Type_S9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def undefined_PMSEVFR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMSEVFR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMSEVFR_EL1_Type_E1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_PMSEVFR_EL1_Type_E1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMSNEVFR_EL1_Type_E1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_PMSNEVFR_EL1_Type_E1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMSEVFR_EL1_Type_E10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_PMSEVFR_EL1_Type_E10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_PMSNEVFR_EL1_Type_E10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_PMSNEVFR_EL1_Type_E10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_PMSEVFR_EL1_Type_E11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_PMSEVFR_EL1_Type_E11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_PMSNEVFR_EL1_Type_E11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_PMSNEVFR_EL1_Type_E11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_PMSEVFR_EL1_Type_E12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_PMSEVFR_EL1_Type_E12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_PMSNEVFR_EL1_Type_E12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_PMSNEVFR_EL1_Type_E12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_PMSEVFR_EL1_Type_E13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_PMSEVFR_EL1_Type_E13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_PMSNEVFR_EL1_Type_E13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_PMSNEVFR_EL1_Type_E13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_PMSEVFR_EL1_Type_E14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_PMSEVFR_EL1_Type_E14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_PMSNEVFR_EL1_Type_E14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_PMSNEVFR_EL1_Type_E14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_PMSEVFR_EL1_Type_E15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_PMSEVFR_EL1_Type_E15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_PMSNEVFR_EL1_Type_E15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_PMSNEVFR_EL1_Type_E15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_PMSEVFR_EL1_Type_E16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_PMSEVFR_EL1_Type_E16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_PMSNEVFR_EL1_Type_E16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_PMSNEVFR_EL1_Type_E16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PMSEVFR_EL1_Type_E17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_PMSEVFR_EL1_Type_E17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_PMSNEVFR_EL1_Type_E17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_PMSNEVFR_EL1_Type_E17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PMSEVFR_EL1_Type_E18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_PMSEVFR_EL1_Type_E18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_PMSNEVFR_EL1_Type_E18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_PMSNEVFR_EL1_Type_E18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_PMSEVFR_EL1_Type_E19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_PMSEVFR_EL1_Type_E19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_PMSNEVFR_EL1_Type_E19 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_PMSNEVFR_EL1_Type_E19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_PMSEVFR_EL1_Type_E2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_PMSEVFR_EL1_Type_E2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_EDVIDSR_Type_E2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMSNEVFR_EL1_Type_E2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_EDVIDSR_Type_E2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMSNEVFR_EL1_Type_E2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_PMSEVFR_EL1_Type_E20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _update_PMSEVFR_EL1_Type_E20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _update_PMSNEVFR_EL1_Type_E20 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)

def _get_PMSNEVFR_EL1_Type_E20 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)

def _get_PMSEVFR_EL1_Type_E21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _update_PMSEVFR_EL1_Type_E21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _update_PMSNEVFR_EL1_Type_E21 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)

def _get_PMSNEVFR_EL1_Type_E21 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)

def _get_PMSEVFR_EL1_Type_E22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_PMSEVFR_EL1_Type_E22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _update_PMSNEVFR_EL1_Type_E22 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_PMSNEVFR_EL1_Type_E22 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _get_PMSEVFR_EL1_Type_E23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_PMSEVFR_EL1_Type_E23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_PMSNEVFR_EL1_Type_E23 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_PMSNEVFR_EL1_Type_E23 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_PMSEVFR_EL1_Type_E24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_PMSEVFR_EL1_Type_E24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_PMSNEVFR_EL1_Type_E24 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_PMSNEVFR_EL1_Type_E24 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_PMSEVFR_EL1_Type_E25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_PMSEVFR_EL1_Type_E25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_PMSNEVFR_EL1_Type_E25 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_PMSNEVFR_EL1_Type_E25 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_PMSEVFR_EL1_Type_E26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_PMSEVFR_EL1_Type_E26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_PMSNEVFR_EL1_Type_E26 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_PMSNEVFR_EL1_Type_E26 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_PMSEVFR_EL1_Type_E27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_PMSEVFR_EL1_Type_E27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_PMSNEVFR_EL1_Type_E27 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_PMSNEVFR_EL1_Type_E27 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_PMSEVFR_EL1_Type_E28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_PMSEVFR_EL1_Type_E28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_PMSNEVFR_EL1_Type_E28 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_PMSNEVFR_EL1_Type_E28 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_PMSEVFR_EL1_Type_E29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_PMSEVFR_EL1_Type_E29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMSNEVFR_EL1_Type_E29 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_PMSNEVFR_EL1_Type_E29 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMSEVFR_EL1_Type_E3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_PMSEVFR_EL1_Type_E3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_EDVIDSR_Type_E3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_PMSNEVFR_EL1_Type_E3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_EDVIDSR_Type_E3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_PMSNEVFR_EL1_Type_E3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_PMSEVFR_EL1_Type_E30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_PMSEVFR_EL1_Type_E30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_PMSNEVFR_EL1_Type_E30 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_PMSNEVFR_EL1_Type_E30 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_PMSEVFR_EL1_Type_E31 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_PMSEVFR_EL1_Type_E31 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_PMSNEVFR_EL1_Type_E31 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_PMSNEVFR_EL1_Type_E31 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_PMSEVFR_EL1_Type_E4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_PMSEVFR_EL1_Type_E4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_PMSNEVFR_EL1_Type_E4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_PMSNEVFR_EL1_Type_E4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_PMSEVFR_EL1_Type_E48 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _update_PMSEVFR_EL1_Type_E48 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _update_PMSNEVFR_EL1_Type_E48 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _get_PMSNEVFR_EL1_Type_E48 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _get_PMSEVFR_EL1_Type_E49 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)

def _update_PMSEVFR_EL1_Type_E49 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def _update_PMSNEVFR_EL1_Type_E49 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)

def _get_PMSNEVFR_EL1_Type_E49 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)

def _get_PMSEVFR_EL1_Type_E5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_PMSEVFR_EL1_Type_E5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_PMSNEVFR_EL1_Type_E5 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_PMSNEVFR_EL1_Type_E5 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_PMSEVFR_EL1_Type_E50 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)

def _update_PMSEVFR_EL1_Type_E50 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _update_PMSNEVFR_EL1_Type_E50 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)

def _get_PMSNEVFR_EL1_Type_E50 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)

def _get_PMSEVFR_EL1_Type_E51 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 51 51)

def _update_PMSEVFR_EL1_Type_E51 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)

def _update_PMSNEVFR_EL1_Type_E51 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)

def _get_PMSNEVFR_EL1_Type_E51 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 51 51)

def _get_PMSEVFR_EL1_Type_E52 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)

def _update_PMSEVFR_EL1_Type_E52 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _update_PMSNEVFR_EL1_Type_E52 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)

def _get_PMSNEVFR_EL1_Type_E52 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)

def _get_PMSEVFR_EL1_Type_E53 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)

def _update_PMSEVFR_EL1_Type_E53 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _update_PMSNEVFR_EL1_Type_E53 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)

def _get_PMSNEVFR_EL1_Type_E53 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)

def _get_PMSEVFR_EL1_Type_E54 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)

def _update_PMSEVFR_EL1_Type_E54 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _update_PMSNEVFR_EL1_Type_E54 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)

def _get_PMSNEVFR_EL1_Type_E54 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)

def _get_PMSEVFR_EL1_Type_E55 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)

def _update_PMSEVFR_EL1_Type_E55 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _update_PMSNEVFR_EL1_Type_E55 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)

def _get_PMSNEVFR_EL1_Type_E55 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)

def _get_PMSEVFR_EL1_Type_E56 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)

def _update_PMSEVFR_EL1_Type_E56 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _update_PMSNEVFR_EL1_Type_E56 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)

def _get_PMSNEVFR_EL1_Type_E56 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)

def _get_PMSEVFR_EL1_Type_E57 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)

def _update_PMSEVFR_EL1_Type_E57 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _update_PMSNEVFR_EL1_Type_E57 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _get_PMSNEVFR_EL1_Type_E57 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)

def _get_PMSEVFR_EL1_Type_E58 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _update_PMSEVFR_EL1_Type_E58 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _update_PMSNEVFR_EL1_Type_E58 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _get_PMSNEVFR_EL1_Type_E58 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _get_PMSEVFR_EL1_Type_E59 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _update_PMSEVFR_EL1_Type_E59 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _update_PMSNEVFR_EL1_Type_E59 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _get_PMSNEVFR_EL1_Type_E59 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _get_PMSEVFR_EL1_Type_E6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_PMSEVFR_EL1_Type_E6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_PMSNEVFR_EL1_Type_E6 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_PMSNEVFR_EL1_Type_E6 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_PMSEVFR_EL1_Type_E60 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _update_PMSEVFR_EL1_Type_E60 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _update_PMSNEVFR_EL1_Type_E60 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _get_PMSNEVFR_EL1_Type_E60 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _get_PMSEVFR_EL1_Type_E61 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _update_PMSEVFR_EL1_Type_E61 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_PMSNEVFR_EL1_Type_E61 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _get_PMSNEVFR_EL1_Type_E61 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _get_PMSEVFR_EL1_Type_E62 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _update_PMSEVFR_EL1_Type_E62 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_PMSNEVFR_EL1_Type_E62 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _get_PMSNEVFR_EL1_Type_E62 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _get_PMSEVFR_EL1_Type_E63 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _update_PMSEVFR_EL1_Type_E63 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _update_PMSNEVFR_EL1_Type_E63 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _get_PMSNEVFR_EL1_Type_E63 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _get_PMSEVFR_EL1_Type_E7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_PMSEVFR_EL1_Type_E7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_PMSNEVFR_EL1_Type_E7 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_PMSNEVFR_EL1_Type_E7 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_PMSEVFR_EL1_Type_E8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_PMSEVFR_EL1_Type_E8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _update_PMSNEVFR_EL1_Type_E8 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_PMSNEVFR_EL1_Type_E8 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _get_PMSEVFR_EL1_Type_E9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_PMSEVFR_EL1_Type_E9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _update_PMSNEVFR_EL1_Type_E9 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_PMSNEVFR_EL1_Type_E9 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def undefined_PMSFCR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMSFCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMSFCR_EL1_Type_B (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_PMSFCR_EL1_Type_B (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_PMSFCR_EL1_Type_LD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_PMSFCR_EL1_Type_LD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_LORID_EL1_Type_LD (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 16 x)

def _get_LORID_EL1_Type_LD (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 23 16)

def undefined_PMSLATFR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMSLATFR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMSLATFR_EL1_Type_MINLAT (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)

def _update_PMSLATFR_EL1_Type_MINLAT (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)

def undefined_PMSNEVFR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMSNEVFR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_PMBIDR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMBIDR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMBIDR_EL1_Type_Align (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_PMBIDR_EL1_Type_Align (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def SPEGetDataSourcePayloadSize (_ : Unit) : SailM Int := do
  (__IMPDEF_integer "SPE Data Source packet payload size")

def SPEGetEventsPayloadSize (_ : Unit) : SailM Int := do
  let size ← do (__IMPDEF_integer "SPE Events packet payload size")
  (pure size)

def DebugWriteExternalAbort (memstatus : PhysMemRetStatus) (addrdesc : AddressDescriptor) (start_vaddr : (BitVec 64)) : SailM Unit := do
  let iswrite : Bool := true
  let handle_as_SError : Bool := false
  let async_external_abort : Bool := false
  let syndrome ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let (async_external_abort, handle_as_SError, syndrome) ← (( do
    match addrdesc.fault.access.acctype with
    | .AccessType_SPE =>
      (do
        let handle_as_SError ← (__IMPDEF_boolean "SPE SyncExternal as SError")
        let async_external_abort ← (__IMPDEF_boolean "SPE async External abort")
        let syndrome ← (pure (Sail.BitVec.extractLsb (← readReg PMBSR_EL1) 63 0))
        (pure (async_external_abort, handle_as_SError, syndrome)))
    | _ =>
      (do
        (Unreachable ())
        (pure (async_external_abort, handle_as_SError, syndrome))) ) : SailM (Bool × Bool × (BitVec 64)) )
  let ttw_abort : Bool := ((BEq.beq addrdesc.fault.statuscode Fault_SyncExternalOnWalk) || (BEq.beq addrdesc.fault.statuscode Fault_SyncParityOnWalk))
  let statuscode : Fault :=
    if (ttw_abort : Bool)
    then addrdesc.fault.statuscode
    else memstatus.statuscode
  let extflag : (BitVec 1) :=
    if (ttw_abort : Bool)
    then addrdesc.fault.extflag
    else memstatus.extflag
  if ((((BEq.beq statuscode Fault_AsyncExternal) || (BEq.beq statuscode Fault_AsyncParity)) || handle_as_SError) : Bool)
  then
    (do
      let fault ← (( do (NoFault ()) ) : SailM FaultRecord )
      let parity : Bool := ((BEq.beq statuscode Fault_SyncParity) || ((BEq.beq statuscode Fault_AsyncParity) || (BEq.beq statuscode Fault_SyncParityOnWalk)))
      let fault : FaultRecord :=
        { fault with statuscode := 
          if (parity : Bool)
          then Fault_AsyncParity
          else Fault_AsyncExternal }
      let fault ← (( do
        if ((← (HaveRASExt ())) : Bool)
        then (pure { fault with merrorstate := memstatus.merrorstate })
        else (pure fault) ) : SailM FaultRecord )
      let fault : FaultRecord := { fault with extflag := extflag }
      let fault : FaultRecord := { fault with access := { fault.access with acctype := addrdesc.fault.access.acctype } }
      (pure (PendSErrorInterrupt fault)))
  else
    (do
      let syndrome : (BitVec 64) := (BitVec.update syndrome 18 (Bit 1#1))
      let syndrome : (BitVec 64) :=
        if (((BEq.beq addrdesc.fault.access.acctype AccessType_SPE) && (async_external_abort || (start_vaddr != addrdesc.vaddress))) : Bool)
        then (BitVec.update syndrome 19 (Bit 1#1))
        else syndrome
      let syndrome ← (( do
        if ((IsZero (BitVec.join1 [(BitVec.access syndrome 17)])) : Bool)
        then
          (do
            let syndrome : (BitVec 64) := (BitVec.update syndrome 17 (Bit 1#1))
            let ec ← (( do (undefined_bitvector 6) ) : SailM (BitVec 6) )
            let ec ← (( do
              if ((((← (HaveRME ())) && (bne addrdesc.fault.gpcf.gpf GPCF_None)) && (bne addrdesc.fault.gpcf.gpf GPCF_Fail)) : Bool)
              then (pure 0b011110#6)
              else
                (if (addrdesc.fault.secondstage : Bool)
                then (pure 0b100101#6)
                else (pure 0b100100#6)) ) : SailM (BitVec 6) )
            let syndrome : (BitVec 64) := (Sail.BitVec.updateSubrange syndrome 31 26 ec)
            if (async_external_abort : Bool)
            then (pure (Sail.BitVec.updateSubrange syndrome 15 0 ((Zeros (n := 10)) +++ 0b010001#6)))
            else (do (pure (Sail.BitVec.updateSubrange syndrome 15 0 ((Zeros (n := 10)) +++ (← (EncodeLDFSC statuscode addrdesc.fault.level)))))))
        else (pure syndrome) ) : SailM (BitVec 64) )
      match addrdesc.fault.access.acctype with
      | .AccessType_SPE => writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange (← readReg PMBSR_EL1) 63 0 syndrome)
      | _ => (Unreachable ()))

def DebugWriteFault (vaddress : (BitVec 64)) (fault : FaultRecord) : SailM Unit := do
  let syndrome ← (( do (undefined_bitvector 64) ) : SailM (BitVec 64) )
  let syndrome ← (( do
    match fault.access.acctype with
    | .AccessType_SPE => (do (pure (Sail.BitVec.extractLsb (← readReg PMBSR_EL1) 63 0)))
    | _ =>
      (do
        (Unreachable ())
        (pure syndrome)) ) : SailM (BitVec 64) )
  let syndrome ← (pure (Sail.BitVec.updateSubrange syndrome 15 0 ((Zeros (n := 10)) +++ (← (EncodeLDFSC fault.statuscode fault.level)))))
  let syndrome : (BitVec 64) := (Sail.BitVec.updateSubrange syndrome 55 32 (Zeros (n := 24)))
  let ec ← (( do (undefined_bitvector 6) ) : SailM (BitVec 6) )
  let ec ← (( do
    if ((((← (HaveRME ())) && (bne fault.gpcf.gpf GPCF_None)) && (bne fault.gpcf.gpf GPCF_Fail)) : Bool)
    then (pure 0b011110#6)
    else
      (if (fault.secondstage : Bool)
      then (pure 0b100101#6)
      else (pure 0b100100#6)) ) : SailM (BitVec 6) )
  let syndrome : (BitVec 64) := (Sail.BitVec.updateSubrange syndrome 31 26 ec)
  let syndrome : (BitVec 64) := (BitVec.update syndrome 17 (Bit 1#1))
  let syndrome : (BitVec 64) :=
    if ((BEq.beq fault.statuscode Fault_Permission) : Bool)
    then
      (let syndrome : (BitVec 64) :=
        (BitVec.update syndrome 39
          (Bit
            (if (fault.assuredonly : Bool)
            then 1#1
            else 0#1)))
      let syndrome : (BitVec 64) :=
        (BitVec.update syndrome 38
          (Bit
            (if (fault.overlay : Bool)
            then 1#1
            else 0#1)))
      (BitVec.update syndrome 37
        (Bit
          (if (fault.dirtybit : Bool)
          then 1#1
          else 0#1))))
    else syndrome
  match fault.access.acctype with
  | .AccessType_SPE => writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange (← readReg PMBSR_EL1) 63 0 syndrome)
  | _ => (Unreachable ())

def SPE_PMBIDR_P_Read (_ : Unit) : SailM (BitVec 1) := do
  let owning_ss ← (( do (undefined_SecurityState ()) ) : SailM SecurityState )
  let owning_el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let (owning_el, owning_ss) ← (( do
    let (tup__0, tup__1) ← do (ProfilingBufferOwner ())
    let owning_ss : SecurityState := tup__0
    let owning_el : (BitVec 2) := tup__1
    (pure (owning_el, owning_ss)) ) : SailM ((BitVec 2) × SecurityState) )
  if ((←((pure ((BitVec.toNat owning_el) >b (BitVec.toNat (← readReg PSTATE).EL))) <||> (do
       (pure ((← readReg PSTATE).EL != EL3)) <&&> (do
         (pure (bne owning_ss (← (CurrentSecurityState ())))))))) : Bool)
  then (pure 1#1)
  else (pure 0#1)

/-- Type quantifiers: k_is_load : Bool -/
def SPESampleExtendedLoadStore (ar : (BitVec 1)) (excl : (BitVec 1)) (at' : (BitVec 1)) (is_load : Bool) : SailM Unit := do
  writeReg SPESampleClass 0b01#2
  let ldst : (BitVec 1) :=
    if (is_load : Bool)
    then 0#1
    else 1#1
  writeReg SPESampleSubclass (((((0b000#3 +++ ar) +++ excl) +++ at') +++ 1#1) +++ ldst)
  writeReg SPESampleSubclassValid true
  if (is_load : Bool)
  then
    (do
      if ((at' == 1#1) : Bool)
      then writeReg SPESampleOpType OpType_LoadAtomic
      else writeReg SPESampleOpType OpType_Load)
  else writeReg SPESampleOpType OpType_Store

def SPESampleSIMDFPLoadStore (_ : Unit) : SailM Unit := do
  writeReg SPESampleClass 0b01#2
  writeReg SPESampleSubclass (Sail.BitVec.updateSubrange (← readReg SPESampleSubclass) 7 1 0b0000010#7)
  writeReg SPESampleSubclassValid true

def SPESampleMemSet (_ : Unit) : SailM Unit := do
  writeReg SPESampleClass 0b01#2
  writeReg SPESampleSubclass (Sail.BitVec.updateSubrange (← readReg SPESampleSubclass) 7 0 0b00100101#8)
  writeReg SPESampleSubclassValid true
  writeReg SPESampleOpType OpType_Store

def SPEISB (_ : Unit) : SailM Unit := do
  let address ← (( do (pure (BitVec.addInt (← (PC_read ())) 4)) ) : SailM (BitVec 64) )
  let branch_type : BranchType := BranchType_DIR
  let branch_conditional : Bool := false
  let taken : Bool := false
  let is_isb : Bool := true
  (SPEBranch__1 address branch_type branch_conditional taken is_isb)

def undefined_BRBINFINJ_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_BRBINFINJ_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_BRBSRCINJ_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_BRBSRCINJ_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_BRBTGTINJ_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_BRBTGTINJ_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def BRBEBranchOnISB (_ : Unit) : SailM Bool := do
  (__IMPDEF_boolean "ISB generates Branch records")

def BRBEISB (_ : Unit) : SailM Unit := do
  let branch_conditional : Bool := false
  (BRBEBranch BranchType_DIR branch_conditional (BitVec.addInt (← (PC_read ())) 4))

/-- Type quantifiers: N : Nat, reg : Int, shift : Int, N ≥ 0 ∧ N = 8 ∨ N = 16 ∨ N = 32 ∨ N = 64 ∨ (not (shift ≥ 0 ∧ shift ≤ 4)) -/
def ExtendReg (reg : Int) (exttype : ExtendType) (shift : Int) (N : Nat) : SailM (BitVec N) := do
  sail_assert ((shift ≥b 0) && (shift ≤b 4)) "src/v8_base.sail:35781.34-35781.35"
  let val_name ← (( do (X_read reg N) ) : SailM (BitVec N) )
  let is_unsigned ← (( do (undefined_bool ()) ) : SailM Bool )
  let len ← (( do (undefined_int ()) ) : SailM Int )
  let (is_unsigned, len) : (Bool × Int) :=
    match exttype with
    | .ExtendType_SXTB =>
      (let is_unsigned : Bool := false
      let len : Int := 8
      (is_unsigned, len))
    | .ExtendType_SXTH =>
      (let is_unsigned : Bool := false
      let len : Int := 16
      (is_unsigned, len))
    | .ExtendType_SXTW =>
      (let is_unsigned : Bool := false
      let len : Int := 32
      (is_unsigned, len))
    | .ExtendType_SXTX =>
      (let is_unsigned : Bool := false
      let len : Int := 64
      (is_unsigned, len))
    | .ExtendType_UXTB =>
      (let is_unsigned : Bool := true
      let len : Int := 8
      (is_unsigned, len))
    | .ExtendType_UXTH =>
      (let is_unsigned : Bool := true
      let len : Int := 16
      (is_unsigned, len))
    | .ExtendType_UXTW =>
      (let is_unsigned : Bool := true
      let len : Int := 32
      (is_unsigned, len))
    | .ExtendType_UXTX =>
      (let is_unsigned : Bool := true
      let len : Int := 64
      (is_unsigned, len))
  let is_unsigned := is_unsigned
  let len := (Min.min len (N -i shift))
  sail_assert ((0 ≤b (len -i 1)) || (! ((shift ≥b 0) && (shift ≤b 4)))) "src/v8_base.sail:35821.73-35821.74"
  (Extend ((Sail.BitVec.extractLsb val_name (len -i 1) 0) +++ (Zeros (n := shift))) N is_unsigned)

def report_tlbi (r : TLBIRecord) (s : Shareability) : SailM Unit := do
  (sail_tlbi
    { rec' := r
      shareability := s })

def Broadcast (shareability : Shareability) (r : TLBIRecord) : Unit :=
  ()

def HasLargeAddress (regime : Regime) : SailM Bool := do
  if ((! (← (Have52BitIPAAndPASpaceExt ()))) : Bool)
  then (pure false)
  else
    (do
      match regime with
      | .Regime_EL3 => (pure ((BitVec.join1 [(BitVec.access (← readReg TCR_EL3) 32)]) == 1#1))
      | .Regime_EL2 => (pure ((BitVec.join1 [(BitVec.access (← readReg TCR_EL2) 32)]) == 1#1))
      | .Regime_EL20 => (pure ((BitVec.join1 [(BitVec.access (← readReg TCR_EL2) 59)]) == 1#1))
      | .Regime_EL10 => (pure ((BitVec.join1 [(BitVec.access (← readReg TCR_EL1) 59)]) == 1#1))
      | _ =>
        (do
          (Unreachable ())
          (undefined_bool ())))

def TLBIPRange (regime : Regime) (Xt : (BitVec 128)) : SailM (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)) := do
  let valid_name : Bool := true
  let start_address : (BitVec 64) := (Zeros (n := 64))
  let end_address_name : (BitVec 64) := (Zeros (n := 64))
  let tg : (BitVec 2) := (Sail.BitVec.extractLsb Xt 47 46)
  let scale := (BitVec.toNat (Sail.BitVec.extractLsb Xt 45 44))
  let num := (BitVec.toNat (Sail.BitVec.extractLsb Xt 43 39))
  let tg_bits : Nat := 12
  if ((tg == 0b00#2) : Bool)
  then (pure (false, tg, start_address, end_address_name))
  else
    (do
      let (start_address, tg_bits) ← (( do
        match (tg : BitVec 2) with
        | 0b01 =>
          (let tg_bits : Nat := 12
          let start_address : (BitVec 64) := (Sail.BitVec.updateSubrange start_address 55 12 (Sail.BitVec.extractLsb Xt 107 64))
          let start_address : (BitVec 64) := (Sail.BitVec.updateSubrange start_address 63 56 (BitVec.replicateBits (BitVec.join1 [(BitVec.access Xt 107)]) 8))
          (pure (start_address, tg_bits)))
        | 0b10 =>
          (let tg_bits : Nat := 14
          let start_address : (BitVec 64) := (Sail.BitVec.updateSubrange start_address 55 14 (Sail.BitVec.extractLsb Xt 107 66))
          let start_address : (BitVec 64) := (Sail.BitVec.updateSubrange start_address 63 56 (BitVec.replicateBits (BitVec.join1 [(BitVec.access Xt 107)]) 8))
          (pure (start_address, tg_bits)))
        | 0b11 =>
          (let tg_bits : Nat := 16
          let start_address : (BitVec 64) := (Sail.BitVec.updateSubrange start_address 55 16 (Sail.BitVec.extractLsb Xt 107 68))
          let start_address : (BitVec 64) := (Sail.BitVec.updateSubrange start_address 63 56 (BitVec.replicateBits (BitVec.join1 [(BitVec.access Xt 107)]) 8))
          (pure (start_address, tg_bits)))
        | _ =>
          (do
            (Unreachable ())
            (pure (start_address, tg_bits))) ) : SailM ((BitVec 64) × Int) )
      let tg_bits := tg_bits
      let range := (Int.shiftl (num +i 1) (((5 *i scale) +i 1) +i tg_bits))
      let end_address_name : (BitVec 64) := (start_address + (integer_subrange range 63 0))
      let end_address_name : (BitVec 64) :=
        if (((BitVec.join1 [(BitVec.access end_address_name 55)]) != (BitVec.join1 [(BitVec.access start_address 55)])) : Bool)
        then ((BitVec.replicateBits (BitVec.join1 [(BitVec.access start_address 55)]) (64 -i 55)) +++ (Ones (n := 55)))
        else end_address_name
      (pure (valid_name, tg, start_address, end_address_name)))

def CACHE_OP (r : CacheRecord) : SailM Unit := do
  (sail_cache_op r)

def undefined_DCZID_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_DCZID_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_DCZID_EL0_Type_BS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_DCZID_EL0_Type_BS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_GMID_EL1_Type_BS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_GMID_EL1_Type_BS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_DCZID_EL0_Type_DZP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_DCZID_EL0_Type_DZP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def Mk_MAIR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_PRRR_Type_DS0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_PRRR_Type_DS1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_PRRR_Type_NOS0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_PRRR_Type_NOS0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_PRRR_Type_NOS1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_PRRR_Type_NOS1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_PRRR_Type_NOS2 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_PRRR_Type_NOS2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_PRRR_Type_NOS3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_PRRR_Type_NOS3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_PRRR_Type_NOS4 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_PRRR_Type_NOS4 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_PRRR_Type_NOS5 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_PRRR_Type_NOS5 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_PRRR_Type_NOS6 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_PRRR_Type_NOS6 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_PRRR_Type_NOS7 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_PRRR_Type_NOS7 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_CNTNSAR_Type_NS0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_CNTNSAR_Type_NS0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_CNTNSAR_Type_NS1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_CNTNSAR_Type_NS1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PRRR_Type_TR0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _update_PRRR_Type_TR0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _get_PRRR_Type_TR1 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)

def _update_PRRR_Type_TR1 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 2 x)

def _get_PRRR_Type_TR2 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _update_PRRR_Type_TR2 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _get_PRRR_Type_TR3 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def _update_PRRR_Type_TR3 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _get_PRRR_Type_TR4 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)

def _update_PRRR_Type_TR4 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def _get_PRRR_Type_TR5 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _update_PRRR_Type_TR5 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _get_PRRR_Type_TR6 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)

def _update_PRRR_Type_TR6 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _get_PRRR_Type_TR7 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)

def _update_PRRR_Type_TR7 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def Mk_MAIR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_NMRR_Type_IR0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _update_NMRR_Type_IR0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _get_NMRR_Type_IR1 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)

def _update_NMRR_Type_IR1 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 2 x)

def _get_NMRR_Type_IR2 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _update_NMRR_Type_IR2 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _get_NMRR_Type_IR3 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def _update_NMRR_Type_IR3 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _get_NMRR_Type_IR4 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)

def _update_NMRR_Type_IR4 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def _get_NMRR_Type_IR5 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _update_NMRR_Type_IR5 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _get_NMRR_Type_IR6 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)

def _update_NMRR_Type_IR6 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _get_NMRR_Type_IR7 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)

def _update_NMRR_Type_IR7 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _get_NMRR_Type_OR0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 17 16)

def _update_NMRR_Type_OR0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 16 x)

def _get_NMRR_Type_OR1 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 19 18)

def _update_NMRR_Type_OR1 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 18 x)

def _get_NMRR_Type_OR2 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)

def _update_NMRR_Type_OR2 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 20 x)

def _get_NMRR_Type_OR3 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)

def _update_NMRR_Type_OR3 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 22 x)

def _get_NMRR_Type_OR4 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)

def _update_NMRR_Type_OR4 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 24 x)

def _get_NMRR_Type_OR5 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 27 26)

def _update_NMRR_Type_OR5 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 26 x)

def _get_NMRR_Type_OR6 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 29 28)

def _update_NMRR_Type_OR6 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 28 x)

def _get_NMRR_Type_OR7 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)

def _update_NMRR_Type_OR7 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 30 x)

def undefined_HMAIR0_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_HMAIR0_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_HMAIR1_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_HMAIR1_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_HTCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_VTCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_DACR32_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_DACR32_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_DACR32_EL2_Type_D0 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _update_DACR32_EL2_Type_D0 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _update_DACR_Type_D0 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _get_DACR_Type_D0 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)

def _get_DACR32_EL2_Type_D1 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)

def _update_DACR32_EL2_Type_D1 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 2 x)

def _update_DACR_Type_D1 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 2 x)

def _get_DACR_Type_D1 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)

def _get_DACR32_EL2_Type_D10 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)

def _update_DACR32_EL2_Type_D10 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 20 x)

def _update_DACR_Type_D10 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 21 20 x)

def _get_DACR_Type_D10 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)

def _get_DACR32_EL2_Type_D11 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)

def _update_DACR32_EL2_Type_D11 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 22 x)

def _update_DACR_Type_D11 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 22 x)

def _get_DACR_Type_D11 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)

def _get_DACR32_EL2_Type_D12 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)

def _update_DACR32_EL2_Type_D12 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)

def _update_DACR_Type_D12 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 25 24 x)

def _get_DACR_Type_D12 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)

def _get_DACR32_EL2_Type_D13 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 27 26)

def _update_DACR32_EL2_Type_D13 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 26 x)

def _update_DACR_Type_D13 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 26 x)

def _get_DACR_Type_D13 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 27 26)

def _get_DACR32_EL2_Type_D14 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 29 28)

def _update_DACR32_EL2_Type_D14 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 28 x)

def _update_DACR_Type_D14 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 28 x)

def _get_DACR_Type_D14 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 29 28)

def _get_DACR32_EL2_Type_D15 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)

def _update_DACR32_EL2_Type_D15 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 30 x)

def _update_DACR_Type_D15 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 30 x)

def _get_DACR_Type_D15 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 31 30)

def _get_DACR32_EL2_Type_D2 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _update_DACR32_EL2_Type_D2 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _update_DACR_Type_D2 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 4 x)

def _get_DACR_Type_D2 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)

def _get_DACR32_EL2_Type_D3 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def _update_DACR32_EL2_Type_D3 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _update_DACR_Type_D3 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 6 x)

def _get_DACR_Type_D3 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)

def _get_DACR32_EL2_Type_D4 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)

def _update_DACR32_EL2_Type_D4 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def _update_DACR_Type_D4 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 8 x)

def _get_DACR_Type_D4 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)

def _get_DACR32_EL2_Type_D5 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _update_DACR32_EL2_Type_D5 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _update_DACR_Type_D5 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 10 x)

def _get_DACR_Type_D5 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)

def _get_DACR32_EL2_Type_D6 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)

def _update_DACR32_EL2_Type_D6 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _update_DACR_Type_D6 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 12 x)

def _get_DACR_Type_D6 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 13 12)

def _get_DACR32_EL2_Type_D7 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)

def _update_DACR32_EL2_Type_D7 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _update_DACR_Type_D7 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)

def _get_DACR_Type_D7 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)

def _get_DACR32_EL2_Type_D8 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 17 16)

def _update_DACR32_EL2_Type_D8 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 16 x)

def _update_DACR_Type_D8 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 16 x)

def _get_DACR_Type_D8 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 17 16)

def _get_DACR32_EL2_Type_D9 (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 19 18)

def _update_DACR32_EL2_Type_D9 (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 18 x)

def _update_DACR_Type_D9 (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 18 x)

def _get_DACR_Type_D9 (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 19 18)

def Mk_DACR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def AArch64_PARFaultStatus (fault : FaultRecord) : SailM (BitVec 6) := do
  let fst ← (( do (undefined_bitvector 6) ) : SailM (BitVec 6) )
  if ((BEq.beq fault.statuscode Fault_Domain) : Bool)
  then
    (do
      sail_assert ((fault.level == 1) || (fault.level == 2)) "src/v8_base.sail:39066.50-39066.51"
      let fst : (BitVec 6) :=
        (Sail.BitVec.updateSubrange fst 1 0
          (if ((fault.level == 1) : Bool)
          then 0b01#2
          else 0b10#2))
      (pure (Sail.BitVec.updateSubrange fst 5 2 0b1111#4)))
  else (do (EncodeLDFSC fault.statuscode fault.level))

/-- Type quantifiers: k_is_ATS1Ex : Bool -/
def AArch64_isPARFormatD128 (regime : Regime) (is_ATS1Ex : Bool) : SailM Bool := do
  let isPARFormatD128 ← (( do (undefined_bool ()) ) : SailM Bool )
  if ((←((pure (BEq.beq regime Regime_EL2)) <||> (do
       (pure (! (← (Have128BitDescriptorExt ()))))))) : Bool)
  then (pure false)
  else
    (do
      let isPARFormatD128 : Bool := false
      match regime with
      | .Regime_EL3 => (do (pure ((_get_TCR_EL3_Type_D128 (← readReg TCR_EL3)) == 1#1)))
      | .Regime_EL20 => (do (pure ((_get_TCR2_EL2_Type_D128 (← readReg TCR2_EL2)) == 1#1)))
      | .Regime_EL10 =>
        (do
          if ((←((pure is_ATS1Ex) <||> (do
               (pure (! (← (EL2Enabled ()))))) <||> (do
               (pure (((_get_HCR_EL2_Type_VM (← readReg HCR_EL2)) +++ (_get_HCR_EL2_Type_DC (← readReg HCR_EL2))) == 0b00#2))))) : Bool)
          then (do (pure ((_get_TCR2_EL1_Type_D128 (← readReg TCR2_EL1)) == 1#1)))
          else (do (pure ((_get_VTCR_EL2_Type_D128 (← readReg VTCR_EL2)) == 1#1))))
      | _ => (pure isPARFormatD128))

def _get_PAR_Type_ATTR (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)

def _update_PAR_Type_ATTR (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 56 x)

def _update_PAR_EL1_Type_ATTR (v : (BitVec 128)) (x : (BitVec 8)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 63 56 x)

def _get_PAR_EL1_Type_ATTR (v : (BitVec 128)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 63 56)

def _get_PAR_Type_FST (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 6 1)

def _update_PAR_Type_FST (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 1 x)

def _update_PAR_EL1_Type_FST (v : (BitVec 128)) (x : (BitVec 6)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 6 1 x)

def _get_PAR_EL1_Type_FST (v : (BitVec 128)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 6 1)

def _get_PAR_Type_FSTAGE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_PAR_Type_FSTAGE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_PAR_Type_Inner (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 6 4)

def _update_PAR_Type_Inner (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 4 x)

def _get_PAR_Type_Outer (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 3 2)

def _update_PAR_Type_Outer (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 2 x)

def _get_PAR_Type_S2WLK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_PAR_Type_S2WLK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def undefined_PAR_EL1_Type (_ : Unit) : SailM (BitVec 128) := do
  (undefined_bitvector 128)

def _get_PAR_EL1_Type_TopLevel (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_PAR_EL1_Type_TopLevel (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def ReportedPARAttrs (parattrs : (BitVec 8)) : SailM (BitVec 8) := do
  (__UNKNOWN_bits 8)

def ReportedPARShareability (sh : (BitVec 2)) : SailM (BitVec 2) := do
  (__UNKNOWN_bits 2)

def undefined_CTILSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTILSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_CTILSR_Type_SLI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_CTILSR_Type_SLI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_EDLSR_Type_SLI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_PMLSR_Type_SLI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_EDLSR_Type_SLI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_PMLSR_Type_SLI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_CTILSR_Type_SLK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_CTILSR_Type_SLK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_EDLSR_Type_SLK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_PMLSR_Type_SLK (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_EDLSR_Type_SLK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_PMLSR_Type_SLK (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def undefined_EDLSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDLSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_PMLSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMLSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_DBGDTR_EL0_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_DBGDTR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_DBGDTR_EL0_Type_HighWord (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 63 32)

def _update_DBGDTR_EL0_Type_HighWord (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 32 x)

def _get_DBGDTR_EL0_Type_LowWord (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_DBGDTR_EL0_Type_LowWord (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def DBGDTR_EL0_read__1 (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _DBGDTR_EL0 ) : SailM DBGDTR_EL0_Type )
  let r ← (( do
    if ((← (__IMPDEF_boolean "read")) : Bool)
    then (do (pure (Sail.BitVec.updateSubrange r 63 32 (BitVec.slice (← readReg DBGDTRTX_EL0) 0 32))))
    else
      (do
        if ((← (__IMPDEF_boolean "read")) : Bool)
        then (do (pure (Sail.BitVec.updateSubrange r 63 32 (BitVec.slice (← readReg DBGDTRTX_EL0) 0 32))))
        else (do (pure (Sail.BitVec.updateSubrange r 63 32 (BitVec.slice (← readReg DBGDTRRX_EL0) 0 32))))) ) : SailM (BitVec 64) )
  if ((← (__IMPDEF_boolean "read")) : Bool)
  then (do (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg DBGDTRRX_EL0) 0 32))))
  else
    (do
      if ((← (__IMPDEF_boolean "read")) : Bool)
      then (do (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg DBGDTRRX_EL0) 0 32))))
      else (do (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg DBGDTRTX_EL0) 0 32)))))

def undefined_EDPRSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDPRSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_EDPRSR_Type_HALTED (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_EDPRSR_Type_HALTED (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_EDPRSR_Type_PU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_EDPRSR_Type_PU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_EDPRSR_Type_R (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_EDPRSR_Type_R (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_EDPRSR_Type_SDAD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)

def _update_EDPRSR_Type_SDAD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 8 8 x)

def _get_EDPRSR_Type_SDR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_EDPRSR_Type_SDR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_EDPRSR_Type_SPMAD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_EDPRSR_Type_SPMAD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_EDPRSR_Type_SR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_EDPRSR_Type_SR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_GICM_TYPER_Type_SR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_GICM_TYPER_Type_SR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def undefined_DBGDCCINT_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def _get_DBGDCCINT_Type_RX (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_MDCCINT_EL1_Type_RX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_MDCCINT_EL1_Type_RX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_DBGDCCINT_Type_TX (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_MDCCINT_EL1_Type_TX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_MDCCINT_EL1_Type_TX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def undefined_MDCCINT_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_MDCCINT_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def LR_write (value_name : (BitVec 32)) : SailM Unit := do
  (R_set 14 value_name)

def DLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DLR ) : SailM DLR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg DLR_EL0) 0 32)))

def DSPSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DSPSR ) : SailM DSPSR_Type )
  (pure (Sail.BitVec.updateSubrange r 31 0 (BitVec.slice (← readReg DSPSR_EL0) 0 32)))

def undefined_CTIDEVCTL_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_CTIDEVCTL_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

/-- Type quantifiers: k_is_async : Bool -/
def CheckPendingExceptionCatch (is_async : Bool) : SailM Unit := do
  if ((←((Havev8p8Debug ()) <&&> (do
       (HaltingAllowed ())) <&&> (do
       (pure ((_get_EDESR_Type_EC (← readReg EDESR)) == 1#1))))) : Bool)
  then (Halt__1 DebugHalt_ExceptionCatch is_async)
  else (pure ())

def undefined_EDVIDSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_EDVIDSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def _get_EDVIDSR_Type_CONTEXTIDR_EL2 (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)

def _update_EDVIDSR_Type_CONTEXTIDR_EL2 (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _get_EDVIDSR_Type_HV (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_EDVIDSR_Type_HV (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def undefined_PMPCSR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_PMPCSR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_PMPCSR_Type_PCSample (v : (BitVec 64)) : (BitVec 56) :=
  ((Sail.BitVec.extractLsb v 55 32) +++ (Sail.BitVec.extractLsb v 31 0))

def _update_PMPCSR_Type_PCSample (v : (BitVec 64)) (x : (BitVec 56)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange (Sail.BitVec.updateSubrange v 55 32 (Sail.BitVec.extractLsb x (56 -i 1) (((56 -i 1) -i ((55 -i 32) +i 1)) +i 1))) 31 0 (Sail.BitVec.extractLsb x ((56 -i 1) -i ((55 -i 32) +i 1)) ((((56 -i 1) -i ((55 -i 32) +i 1)) -i ((31 -i 0) +i 1)) +i 1)))

def _update_DBGDEVID_Type_PCSample (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_EDDEVID_Type_PCSample (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_PMDEVID_Type_PCSample (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_DBGDEVID_Type_PCSample (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_EDDEVID_Type_PCSample (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_PMDEVID_Type_PCSample (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def undefined_PMVIDSR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_PMVIDSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_HTRFCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def _get_HTRFCR_Type_E0HTRE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_TRFCR_EL2_Type_E0HTRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_TRFCR_EL2_Type_E0HTRE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_HTRFCR_Type_E2TRE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_TRFCR_EL2_Type_E2TRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_TRFCR_EL2_Type_E2TRE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def undefined_TRFCR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_TRFCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def undefined_TRFCR_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_TRFCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_TRFCR_EL1_Type_E0TRE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_TRFCR_EL1_Type_E0TRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_TRFCR_Type_E0TRE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_TRFCR_EL1_Type_E1TRE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_TRFCR_EL1_Type_E1TRE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_TRFCR_Type_E1TRE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def undefined_TRFCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def TraceSynchronizationBarrier (_ : Unit) : Unit :=
  ()

/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV81 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap1_IMPLEMENTED enabled

/-- Type quantifiers: value_name : Int -/
def decode_max_smeveclen (value_name : Int) : Int := Id.run do
  let svl : Int := (Int.shiftr value_name 1)
  let bitpos : Nat := 0
  let (bitpos, svl) ← (( do
    let mut loop_vars := (bitpos, svl)
    while (λ (bitpos, svl) => (svl != 0)) loop_vars do
      let (bitpos, svl) := loop_vars
      loop_vars :=
        (let svl : Int := (Int.shiftr svl 1)
        let bitpos : Int := (bitpos +i 1)
        (bitpos, svl) : (Int × Int))
    (pure loop_vars) ) : Id (Int × Int) )
  let bitpos : Int :=
    if (((value_name == 0) || ((bitpos >b 4) : Bool)) : Bool)
    then 2
    else bitpos
  let bitpos := bitpos
  let max_svl := (128 *i (2 ^i bitpos))
  (pure max_svl)

/-- Type quantifiers: value_name : Int -/
def decode_max_sveveclen (value_name : Int) : SailM Int := do
  let max_vl : Int := (value_name *i 64)
  let max_vl : Int :=
    if ((max_vl >b 2048) : Bool)
    then 2048
    else max_vl
  let max_vl := max_vl
  if ((! (← (IsPow2 max_vl))) : Bool)
  then (FloorPow2 max_vl)
  else (pure max_vl)

def undefined_DBGBCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGBCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_DBGBVR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGBVR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_DBGBXVR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGBXVR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_DBGVCR32_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_DBGVCR32_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_DBGVCR32_EL2_Type_NSD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_DBGVCR32_EL2_Type_NSD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_DBGVCR_Type_NSD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_DBGVCR_Type_NSD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_DBGVCR32_EL2_Type_NSF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_DBGVCR32_EL2_Type_NSF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_DBGVCR_Type_NSF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_DBGVCR_Type_NSF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_DBGVCR32_EL2_Type_NSI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_DBGVCR32_EL2_Type_NSI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _update_DBGVCR_Type_NSI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_DBGVCR_Type_NSI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _get_DBGVCR32_EL2_Type_NSP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_DBGVCR32_EL2_Type_NSP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_DBGVCR_Type_NSP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_DBGVCR_Type_NSP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_DBGVCR32_EL2_Type_NSS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_DBGVCR32_EL2_Type_NSS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_DBGVCR_Type_NSS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_DBGVCR_Type_NSS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_DBGVCR32_EL2_Type_SD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_DBGVCR32_EL2_Type_SD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_DBGVCR_Type_SD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_DBGVCR_Type_SD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_DBGVCR32_EL2_Type_SF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_DBGVCR32_EL2_Type_SF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_DBGVCR_Type_SF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_DBGVCR_Type_SF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_DBGVCR32_EL2_Type_SI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_DBGVCR32_EL2_Type_SI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _update_DBGVCR_Type_SI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_DBGVCR_Type_SI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _get_DBGVCR32_EL2_Type_SP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_DBGVCR32_EL2_Type_SP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_DBGVCR_Type_SP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_DBGVCR_Type_SP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_DBGVCR32_EL2_Type_SU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_DBGVCR32_EL2_Type_SU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_DBGVCR_Type_SU (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_DBGVCR_Type_SU (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def undefined_DBGVCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def _get_DBGVCR_Type_MD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_DBGVCR_Type_MD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_DBGVCR_Type_MF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_DBGVCR_Type_MF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_DBGVCR_Type_MI (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_DBGVCR_Type_MI (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_DBGVCR_Type_MP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_DBGVCR_Type_MP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_DBGVCR_Type_MS (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_DBGVCR_Type_MS (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def undefined_DBGWCR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGWCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def undefined_DBGWVR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def Mk_DBGWVR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v

def AArch32_PARFaultStatusLD (fault : FaultRecord) : SailM (BitVec 6) := do
  let syndrome ← (( do (undefined_bitvector 6) ) : SailM (BitVec 6) )
  if ((BEq.beq fault.statuscode Fault_Domain) : Bool)
  then
    (do
      sail_assert ((fault.level == 1) || (fault.level == 2)) "src/v8_base.sail:41008.50-41008.51"
      let syndrome : (BitVec 6) :=
        (Sail.BitVec.updateSubrange syndrome 1 0
          (if ((fault.level == 1) : Bool)
          then 0b01#2
          else 0b10#2))
      (pure (Sail.BitVec.updateSubrange syndrome 5 2 0b1111#4)))
  else (do (EncodeLDFSC fault.statuscode fault.level))

def AArch32_PARFaultStatusSD (fault : FaultRecord) : SailM (BitVec 6) := do
  let syndrome ← (( do (undefined_bitvector 6) ) : SailM (BitVec 6) )
  let syndrome ←
    (pure (BitVec.update syndrome 5
        (Bit
          (← (do
            if ((← (IsExternalAbort__1 fault)) : Bool)
            then (pure fault.extflag)
            else (pure 0#1))))))
  (pure (Sail.BitVec.updateSubrange syndrome 4 0 (← (EncodeSDFSC fault.statuscode fault.level))))

def AArch32_PARInnerAttrs (memattrs : MemoryAttributes) : SailM (BitVec 3) := do
  let result ← (( do (undefined_bitvector 3) ) : SailM (BitVec 3) )
  if ((BEq.beq memattrs.memtype MemType_Device) : Bool)
  then
    (if ((BEq.beq memattrs.device DeviceType_nGnRnE) : Bool)
    then (pure 0b001#3)
    else
      (if ((BEq.beq memattrs.device DeviceType_nGnRE) : Bool)
      then (pure 0b011#3)
      else (pure result)))
  else
    (let inner : MemAttrHints := memattrs.inner
    if ((inner.attrs == MemAttr_NC) : Bool)
    then (pure 0b000#3)
    else
      (if (((inner.attrs == MemAttr_WB) && ((BitVec.join1 [(BitVec.access inner.hints 0)]) == 1#1)) : Bool)
      then (pure 0b101#3)
      else
        (if ((inner.attrs == MemAttr_WT) : Bool)
        then (pure 0b110#3)
        else
          (if (((inner.attrs == MemAttr_WB) && ((BitVec.join1 [(BitVec.access inner.hints 0)]) == 0#1)) : Bool)
          then (pure 0b111#3)
          else (pure result)))))

def AArch32_PAROuterAttrs (memattrs : MemoryAttributes) : SailM (BitVec 2) := do
  let result ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  if ((BEq.beq memattrs.memtype MemType_Device) : Bool)
  then (do (__UNKNOWN_bits 2))
  else
    (let outer : MemAttrHints := memattrs.outer
    if ((outer.attrs == MemAttr_NC) : Bool)
    then (pure 0b00#2)
    else
      (if (((outer.attrs == MemAttr_WB) && ((BitVec.join1 [(BitVec.access outer.hints 0)]) == 1#1)) : Bool)
      then (pure 0b01#2)
      else
        (if (((outer.attrs == MemAttr_WT) && ((BitVec.join1 [(BitVec.access outer.hints 0)]) == 0#1)) : Bool)
        then (pure 0b10#2)
        else
          (if (((outer.attrs == MemAttr_WB) && ((BitVec.join1 [(BitVec.access outer.hints 0)]) == 0#1)) : Bool)
          then (pure 0b11#2)
          else (pure result)))))

def AArch32_ReportedInnerAttrs (attrs : (BitVec 3)) : SailM (BitVec 3) := do
  (__UNKNOWN_bits 3)

def AArch32_ReportedOuterAttrs (attrs : (BitVec 2)) : SailM (BitVec 2) := do
  (__UNKNOWN_bits 2)

/-- Type quantifiers: k_N : Nat, k_N > 1 -/
def RRX_C (x : (BitVec k_N)) (carry_in : (BitVec 1)) : ((BitVec k_N) × (BitVec 1)) :=
  let result : (BitVec k_N) := (BitVec.update (x >>> 1) ((Sail.BitVec.length x) -i 1) (Bit carry_in))
  let carry_out : (BitVec 1) := (BitVec.join1 [(BitVec.access x 0)])
  (result, carry_out)

def T32ExpandImm_C (imm12 : (BitVec 12)) (carry_in : (BitVec 1)) : SailM ((BitVec 32) × (BitVec 1)) := do
  let unrotated_value ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let imm32 ← (( do (undefined_bitvector 32) ) : SailM (BitVec 32) )
  let carry_out ← (( do (undefined_bitvector 1) ) : SailM (BitVec 1) )
  let (carry_out, imm32) ← (( do
    if (((Sail.BitVec.extractLsb imm12 11 10) == 0b00#2) : Bool)
    then
      (let imm32 : (BitVec 32) :=
        match ((Sail.BitVec.extractLsb imm12 9 8) : BitVec 2) with
        | 0b00 => (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb imm12 7 0) 32)
        | 0b01 => (((0b00000000#8 +++ (Sail.BitVec.extractLsb imm12 7 0)) +++ 0b00000000#8) +++ (Sail.BitVec.extractLsb imm12 7 0))
        | 0b10 => ((((Sail.BitVec.extractLsb imm12 7 0) +++ 0b00000000#8) +++ (Sail.BitVec.extractLsb imm12 7 0)) +++ 0b00000000#8)
        | _ => ((((Sail.BitVec.extractLsb imm12 7 0) +++ (Sail.BitVec.extractLsb imm12 7 0)) +++ (Sail.BitVec.extractLsb imm12 7 0)) +++ (Sail.BitVec.extractLsb imm12 7 0))
      let carry_out : (BitVec 1) := carry_in
      (pure (carry_out, imm32)))
    else
      (do
        let unrotated_value : (BitVec 32) := (Sail.BitVec.zeroExtend (1#1 +++ (Sail.BitVec.extractLsb imm12 6 0)) 32)
        let (tup__0, tup__1) ← do (ROR_C unrotated_value (BitVec.toNat (Sail.BitVec.extractLsb imm12 11 7)))
        let imm32 : (BitVec 32) := tup__0
        let carry_out : (BitVec 1) := tup__1
        (pure (carry_out, imm32))) ) : SailM ((BitVec 1) × (BitVec 32)) )
  (pure (imm32, carry_out))

def AArch32_TakeHypTrapException__1 (except : ExceptionRecord) : SailM Unit := do
  sail_assert (←((pure (HaveEL EL2)) <&&> (do
    (pure (BEq.beq (← (CurrentSecurityState ())) SS_NonSecure))) <&&> (do
    (ELUsingAArch32 EL2)))) "src/v8_base.sail:41513.87-41513.88"
  let preferred_exception_return ← (( do (ThisInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset := (BitVec.toNat 0x14#8)
  (AArch32_EnterHypMode except preferred_exception_return vect_offset)

def undefined_HSTR_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def AArch32_UnalignedAccessFaults (accdesc : AccessDescriptor) : SailM Bool := do
  (pure (((((← (AlignmentEnforced ())) || accdesc.a32lsmd) || accdesc.exclusive) || accdesc.acqsc) || accdesc.relsc))

/-- Type quantifiers: k_aligned : Bool, k_ispair : Bool, size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def AArch32_MemSingle_set__1 (address : (BitVec 32)) (size : Nat) (accdesc_in : AccessDescriptor) (aligned : Bool) (ispair : Bool) (value_name : (BitVec (size * 8))) : SailM Unit := do
  sail_assert ((size == 1) || ((size == 2) || ((size == 4) || ((size == 8) || (size == 16))))) "src/v8_base.sail:41945.69-41945.70"
  let accdesc : AccessDescriptor := accdesc_in
  sail_assert (IsAligned__1 address size) "src/v8_base.sail:41947.38-41947.39"
  let memaddrdesc ← (( do (AArch32_TranslateAddress address accdesc aligned size) ) : SailM AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then (AArch32_Abort address memaddrdesc.fault)
  else (pure ())
  let _ : Unit :=
    if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
    then (ClearExclusiveByAddress memaddrdesc.paddress (ProcessorID ()) size)
    else ()
  if ((← readReg SPESampleInFlight) : Bool)
  then
    (do
      let is_load : Bool := false
      (SPESampleLoadStore is_load accdesc memaddrdesc))
  else (pure ())
  let memstatus ← (( do (PhysMemWrite memaddrdesc size accdesc none value_name) ) : SailM PhysMemRetStatus )
  if ((IsFault__2 memstatus) : Bool)
  then (HandleExternalWriteAbort memstatus memaddrdesc size accdesc)
  else (pure ())

/-- Type quantifiers: processorid : Int, size : Int -/
def AArch32_MarkExclusiveVA (address : (BitVec 32)) (processorid : Int) (size : Int) : Unit :=
  ()

/-- Type quantifiers: processorid : Int, size : Int -/
def AArch32_IsExclusiveVA (address : (BitVec 32)) (processorid : Int) (size : Int) : SailM Bool := do
  (__UNKNOWN_boolean ())

/-- Type quantifiers: n : Int -/
def Q_set (n : Int) (value_name : (BitVec 128)) : SailM Unit := do
  sail_assert ((n ≥b 0) && (n ≤b 15)) "src/v8_base.sail:42248.27-42248.28"
  (V_set n 128 value_name)

def AArch32_ResetGeneralRegisters (_ : Unit) : SailM Unit := do
  let loop_i_lower := 0
  let loop_i_upper := 7
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars
    loop_vars ← do (R_set i (← (__UNKNOWN_bits 32)))
  (pure loop_vars)
  let loop_i_lower := 8
  let loop_i_upper := 12
  let mut loop_vars_1 := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars_1
    loop_vars_1 ← do
      (Rmode_set i M32_User (← (__UNKNOWN_bits 32)))
      (Rmode_set i M32_FIQ (← (__UNKNOWN_bits 32)))
  (pure loop_vars_1)
  if ((HaveEL EL2) : Bool)
  then (Rmode_set 13 M32_Hyp (← (__UNKNOWN_bits 32)))
  else (pure ())
  let loop_i_lower := 13
  let loop_i_upper := 14
  let mut loop_vars_2 := ()
  for i in [loop_i_lower:loop_i_upper:1]i do
    let () := loop_vars_2
    loop_vars_2 ← do
      (Rmode_set i M32_User (← (__UNKNOWN_bits 32)))
      (Rmode_set i M32_FIQ (← (__UNKNOWN_bits 32)))
      (Rmode_set i M32_IRQ (← (__UNKNOWN_bits 32)))
      (Rmode_set i M32_Svc (← (__UNKNOWN_bits 32)))
      (Rmode_set i M32_Abort (← (__UNKNOWN_bits 32)))
      (Rmode_set i M32_Undef (← (__UNKNOWN_bits 32)))
      if ((HaveEL EL3) : Bool)
      then (Rmode_set i M32_Monitor (← (__UNKNOWN_bits 32)))
      else (pure ())
  (pure loop_vars_2)

def SelectInstrSet (iset : InstrSet) : SailM Unit := do
  sail_assert (←((pure (BEq.beq (← (CurrentInstrSet ())) InstrSet_A32)) <||> (do
    (pure (BEq.beq (← (CurrentInstrSet ())) InstrSet_T32))))) "src/v8_base.sail:42361.80-42361.81"
  sail_assert ((BEq.beq iset InstrSet_A32) || (BEq.beq iset InstrSet_T32)) "src/v8_base.sail:42362.54-42362.55"
  writeReg PSTATE { (← readReg PSTATE) with T := 
    if ((BEq.beq iset InstrSet_A32) : Bool)
    then 0#1
    else 1#1 }

def CBWritePC (address_in : (BitVec 32)) : SailM Unit := do
  let address : (BitVec 32) := address_in
  sail_assert (BEq.beq (← (CurrentInstrSet ())) InstrSet_T32) "src/v8_base.sail:42418.44-42418.45"
  let address : (BitVec 32) := (BitVec.update address 0 (Bit 0#1))
  let branch_conditional : Bool := true
  (BranchTo address BranchType_DIR branch_conditional)

/-- Type quantifiers: n : Int -/
def Din_read (n : Int) : SailM (BitVec 64) := do
  sail_assert ((n ≥b 0) && (n ≤b 31)) "src/v8_base.sail:42439.27-42439.28"
  (pure (GetElem?.getElem! (← readReg _Dclone) n))

def AArch32_WriteModeByInstr (mode : (BitVec 5)) : SailM Unit := do
  let el ← (( do (undefined_bitvector 2) ) : SailM (BitVec 2) )
  let valid_name ← (( do (undefined_bool ()) ) : SailM Bool )
  let (el, valid_name) ← (( do
    let (tup__0, tup__1) ← do (ELFromM32 mode)
    let valid_name : Bool := tup__0
    let el : (BitVec 2) := tup__1
    (pure (el, valid_name)) ) : SailM ((BitVec 2) × Bool) )
  let valid_name ← (( do
    if (((BitVec.toNat el) >b (BitVec.toNat (← readReg PSTATE).EL)) : Bool)
    then (pure false)
    else (pure valid_name) ) : SailM Bool )
  let valid_name ← (( do
    if ((←((pure (((← readReg PSTATE).M == M32_Hyp) || (mode == M32_Hyp))) <&&> (do
         (pure ((← readReg PSTATE).M != mode))))) : Bool)
    then (pure false)
    else (pure valid_name) ) : SailM Bool )
  let valid_name ← (( do
    if ((←((pure ((((← readReg PSTATE).M == M32_Monitor) && (HaveEL EL2)) && (el == EL1))) <&&> (do
         (pure ((_get_SCR_Type_NS (← readReg SCR)) == 1#1))) <&&> (do
         (pure ((_get_HCR_Type_TGE (← (HCR_read ()))) == 1#1))))) : Bool)
    then (pure false)
    else (pure valid_name) ) : SailM Bool )
  let valid_name := valid_name
  if ((! valid_name) : Bool)
  then writeReg PSTATE { (← readReg PSTATE) with IL := 1#1 }
  else (AArch32_WriteMode mode)

def BankedRegisterAccessValid (SYSm : (BitVec 5)) (mode : (BitVec 5)) : SailM Unit := do
  let b__0 := SYSm
  if (((Sail.BitVec.extractLsb b__0 4 2) == (0b000#3 : (BitVec 3))) : Bool)
  then
    (do
      if ((mode != M32_FIQ) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ()))
  else
    (do
      if ((b__0 == (0b00100#5 : (BitVec 5))) : Bool)
      then
        (do
          if ((mode != M32_FIQ) : Bool)
          then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
          else (pure ()))
      else
        (do
          if ((b__0 == (0b00101#5 : (BitVec 5))) : Bool)
          then
            (do
              if ((mode == M32_System) : Bool)
              then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
              else (pure ()))
          else
            (do
              if ((b__0 == (0b00110#5 : (BitVec 5))) : Bool)
              then
                (do
                  if (((mode == M32_Hyp) || (mode == M32_System)) : Bool)
                  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
                  else (pure ()))
              else
                (do
                  if (((Sail.BitVec.extractLsb b__0 4 2) == (0b010#3 : (BitVec 3))) : Bool)
                  then
                    (do
                      if ((mode == M32_FIQ) : Bool)
                      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
                      else (pure ()))
                  else
                    (do
                      if (((Sail.BitVec.extractLsb b__0 4 1) == (0x6#4 : (BitVec 4))) : Bool)
                      then
                        (do
                          if ((mode == M32_FIQ) : Bool)
                          then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
                          else (pure ()))
                      else
                        (do
                          if ((b__0 == (0b01110#5 : (BitVec 5))) : Bool)
                          then
                            (do
                              if ((mode == M32_FIQ) : Bool)
                              then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
                              else (pure ()))
                          else
                            (do
                              if (((Sail.BitVec.extractLsb b__0 4 1) == (0x8#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if ((mode == M32_IRQ) : Bool)
                                  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
                                  else (pure ()))
                              else
                                (do
                                  if (((Sail.BitVec.extractLsb b__0 4 1) == (0x9#4 : (BitVec 4))) : Bool)
                                  then
                                    (do
                                      if ((mode == M32_Svc) : Bool)
                                      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
                                      else (pure ()))
                                  else
                                    (do
                                      if (((Sail.BitVec.extractLsb b__0 4 1) == (0xA#4 : (BitVec 4))) : Bool)
                                      then
                                        (do
                                          if ((mode == M32_Abort) : Bool)
                                          then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
                                          else (pure ()))
                                      else
                                        (do
                                          if (((Sail.BitVec.extractLsb b__0 4 1) == (0xB#4 : (BitVec 4))) : Bool)
                                          then
                                            (do
                                              if ((mode == M32_Undef) : Bool)
                                              then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
                                              else (pure ()))
                                          else
                                            (do
                                              if (((Sail.BitVec.extractLsb b__0 4 1) == (0xE#4 : (BitVec 4))) : Bool)
                                              then
                                                (do
                                                  if (((←((pure (! (HaveEL EL3))) <||> (do
                                                         (pure (bne (← (CurrentSecurityState ())) SS_Secure))))) || (mode == M32_Monitor)) : Bool)
                                                  then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
                                                  else (pure ()))
                                              else
                                                (do
                                                  if ((b__0 == (0b11110#5 : (BitVec 5))) : Bool)
                                                  then
                                                    (do
                                                      if (((! (HaveEL EL2)) || (! ((mode == M32_Monitor) || (mode == M32_Hyp)))) : Bool)
                                                      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
                                                      else (pure ()))
                                                  else
                                                    (do
                                                      if ((b__0 == (0b11111#5 : (BitVec 5))) : Bool)
                                                      then
                                                        (do
                                                          if (((! (HaveEL EL2)) || (mode != M32_Monitor)) : Bool)
                                                          then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
                                                          else (pure ()))
                                                      else (sailThrow ((Error_Unpredictable ())) : SailM Unit))))))))))))))

def InITBlock (_ : Unit) : SailM Bool := do
  if ((BEq.beq (← (CurrentInstrSet ())) InstrSet_T32) : Bool)
  then (pure ((Sail.BitVec.extractLsb (← readReg PSTATE).IT 3 0) != 0b0000#4))
  else (pure false)

def LastInITBlock (_ : Unit) : SailM Bool := do
  (pure ((Sail.BitVec.extractLsb (← readReg PSTATE).IT 3 0) == 0b1000#4))

def SPSRaccessValid (SYSm : (BitVec 5)) (mode : (BitVec 5)) : SailM Unit := do
  match (SYSm : BitVec 5) with
  | 0b01110 =>
    (do
      if ((mode == M32_FIQ) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ()))
  | 0b10000 =>
    (do
      if ((mode == M32_IRQ) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ()))
  | 0b10010 =>
    (do
      if ((mode == M32_Svc) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ()))
  | 0b10100 =>
    (do
      if ((mode == M32_Abort) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ()))
  | 0b10110 =>
    (do
      if ((mode == M32_Undef) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ()))
  | 0b11100 =>
    (do
      if ((←((pure ((! (HaveEL EL3)) || (mode == M32_Monitor))) <||> (do
           (pure (bne (← (CurrentSecurityState ())) SS_Secure))))) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ()))
  | 0b11110 =>
    (do
      if (((! (HaveEL EL2)) || (mode != M32_Monitor)) : Bool)
      then (sailThrow ((Error_Unpredictable ())) : SailM Unit)
      else (pure ()))
  | _ => (sailThrow ((Error_Unpredictable ())) : SailM Unit)

/-- Type quantifiers: cp_num : Int -/
def AArch32_SysRegReadCanWriteAPSR (cp_num : Int) (instr : (BitVec 32)) : SailM Bool := do
  sail_assert (← (UsingAArch32 ())) "src/v8_base.sail:42703.25-42703.26"
  sail_assert ((cp_num == 14) || (cp_num == 15)) "src/v8_base.sail:42704.38-42704.39"
  sail_assert (cp_num == (BitVec.toNat (Sail.BitVec.extractLsb instr 11 8))) "src/v8_base.sail:42705.41-42705.42"
  let opc1 := (BitVec.toNat (Sail.BitVec.extractLsb instr 23 21))
  let opc2 := (BitVec.toNat (Sail.BitVec.extractLsb instr 7 5))
  let CRn := (BitVec.toNat (Sail.BitVec.extractLsb instr 19 16))
  let CRm := (BitVec.toNat (Sail.BitVec.extractLsb instr 3 0))
  if ((((((cp_num == 14) && (opc1 == 0)) && (CRn == 0)) && (CRm == 1)) && (opc2 == 0)) : Bool)
  then (pure true)
  else (pure false)

def AArch32_TakeMonitorTrapException (_ : Unit) : SailM Unit := do
  sail_assert (←((pure (HaveEL EL3)) <&&> (do
    (ELUsingAArch32 EL3)))) "src/v8_base.sail:42977.44-42977.45"
  let preferred_exception_return ← (( do (ThisInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset := (BitVec.toNat 0x04#8)
  let lr_offset ← do
    if ((BEq.beq (← (CurrentInstrSet ())) InstrSet_A32) : Bool)
    then (pure 4)
    else (pure 2)
  (AArch32_EnterMonitorMode preferred_exception_return lr_offset vect_offset)

def undefined_PMOVSSET_Type (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector 32)

def undefined_PMCCNTR_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def undefined_ID_MMFR2_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_MMFR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_MMFR2_EL1_Type_HWAccFlg (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_MMFR2_EL1_Type_HWAccFlg (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_ID_MMFR2_Type_HWAccFlg (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_ID_MMFR2_EL1_Type_HvdTLB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _update_ID_MMFR2_EL1_Type_HvdTLB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _get_ID_MMFR2_Type_HvdTLB (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_MMFR2_EL1_Type_L1HvdBG (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_MMFR2_EL1_Type_L1HvdBG (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_MMFR2_Type_L1HvdBG (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_MMFR2_EL1_Type_L1HvdFG (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_MMFR2_EL1_Type_L1HvdFG (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_MMFR2_Type_L1HvdFG (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_MMFR2_EL1_Type_L1HvdRng (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_MMFR2_EL1_Type_L1HvdRng (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_MMFR2_Type_L1HvdRng (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_MMFR2_EL1_Type_MemBarr (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_MMFR2_EL1_Type_MemBarr (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_MMFR2_Type_MemBarr (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_MMFR2_EL1_Type_UniTLB (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_MMFR2_EL1_Type_UniTLB (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_MMFR2_Type_UniTLB (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_MMFR2_EL1_Type_WFIStall (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_MMFR2_EL1_Type_WFIStall (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _get_ID_MMFR2_Type_WFIStall (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def undefined_ID_MMFR4_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_MMFR4_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_MMFR4_EL1_Type_AC2 (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _update_ID_MMFR4_EL1_Type_AC2 (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _update_ID_MMFR4_Type_AC2 (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _get_ID_MMFR4_Type_AC2 (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)

def _get_ID_MMFR4_EL1_Type_CCIDX (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _update_ID_MMFR4_EL1_Type_CCIDX (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_AA64MMFR2_EL1_Type_CCIDX (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_AA64MMFR2_EL1_Type_CCIDX (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_MMFR4_Type_CCIDX (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_MMFR4_EL1_Type_EVT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _update_ID_MMFR4_EL1_Type_EVT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_AA64MMFR2_EL1_Type_EVT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 56 x)

def _update_ID_MMFR4_Type_EVT (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _get_ID_AA64MMFR2_EL1_Type_EVT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 59 56)

def _get_ID_MMFR4_Type_EVT (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_ID_MMFR4_EL1_Type_HPDS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_MMFR4_EL1_Type_HPDS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _update_ID_AA64MMFR1_EL1_Type_HPDS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)

def _update_ID_MMFR4_Type_HPDS (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def _get_ID_AA64MMFR1_EL1_Type_HPDS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)

def _get_ID_MMFR4_Type_HPDS (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _get_ID_MMFR4_EL1_Type_LSM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _update_ID_MMFR4_EL1_Type_LSM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _update_ID_AA64MMFR2_EL1_Type_LSM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_MMFR4_Type_LSM (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)

def _get_ID_AA64MMFR2_EL1_Type_LSM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _get_ID_MMFR4_Type_LSM (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)

def _get_ID_MMFR4_EL1_Type_SpecSEI (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _update_ID_MMFR4_EL1_Type_SpecSEI (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_ID_AA64MMFR1_EL1_Type_SpecSEI (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ID_MMFR4_Type_SpecSEI (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _get_ID_AA64MMFR1_EL1_Type_SpecSEI (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)

def _get_ID_MMFR4_Type_SpecSEI (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)

def _get_ID_MMFR4_EL1_Type_XNX (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def _update_ID_MMFR4_EL1_Type_XNX (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _update_ID_AA64MMFR1_EL1_Type_XNX (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 28 x)

def _update_ID_MMFR4_Type_XNX (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 8 x)

def _get_ID_AA64MMFR1_EL1_Type_XNX (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 31 28)

def _get_ID_MMFR4_Type_XNX (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)

def undefined_ID_AA64MMFR2_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ID_AA64MMFR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ID_AA64MMFR2_EL1_Type_BBM (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)

def _update_ID_AA64MMFR2_EL1_Type_BBM (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)

def _get_ID_AA64MMFR2_EL1_Type_E0PD (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 63 60)

def _update_ID_AA64MMFR2_EL1_Type_E0PD (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 60 x)

def _get_ID_AA64MMFR2_EL1_Type_TTL (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 51 48)

def _update_ID_AA64MMFR2_EL1_Type_TTL (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 48 x)

def _get_ID_AA64MMFR2_EL1_Type_VARange (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)

def _update_ID_AA64MMFR2_EL1_Type_VARange (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)

def undefined_HDFGRTR_EL2_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_HDFGRTR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_HDFGRTR_EL2_Type_DBGAUTHSTATUS_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)

def _update_HDFGRTR_EL2_Type_DBGAUTHSTATUS_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _get_HDFGRTR_EL2_Type_DBGBCRn_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _update_HDFGRTR_EL2_Type_DBGBCRn_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _update_HDFGWTR_EL2_Type_DBGBCRn_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)

def _get_HDFGWTR_EL2_Type_DBGBCRn_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)

def _get_HDFGRTR_EL2_Type_DBGBVRn_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _update_HDFGRTR_EL2_Type_DBGBVRn_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _update_HDFGWTR_EL2_Type_DBGBVRn_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)

def _get_HDFGWTR_EL2_Type_DBGBVRn_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)

def _get_HDFGRTR_EL2_Type_DBGCLAIM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _update_HDFGRTR_EL2_Type_DBGCLAIM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _update_HDFGWTR_EL2_Type_DBGCLAIM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)

def _get_HDFGWTR_EL2_Type_DBGCLAIM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)

def _get_HDFGRTR_EL2_Type_DBGPRCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _update_HDFGRTR_EL2_Type_DBGPRCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _update_HDFGWTR_EL2_Type_DBGPRCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _get_HDFGWTR_EL2_Type_DBGPRCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)

def _get_HDFGRTR_EL2_Type_DBGWCRn_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _update_HDFGRTR_EL2_Type_DBGWCRn_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _update_HDFGWTR_EL2_Type_DBGWCRn_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)

def _get_HDFGWTR_EL2_Type_DBGWCRn_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)

def _get_HDFGRTR_EL2_Type_DBGWVRn_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _update_HDFGRTR_EL2_Type_DBGWVRn_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _update_HDFGWTR_EL2_Type_DBGWVRn_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)

def _get_HDFGWTR_EL2_Type_DBGWVRn_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)

def _get_HDFGRTR_EL2_Type_MDSCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _update_HDFGRTR_EL2_Type_MDSCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _update_HDFGWTR_EL2_Type_MDSCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)

def _get_HDFGWTR_EL2_Type_MDSCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)

def _get_HDFGRTR_EL2_Type_OSDLR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _update_HDFGRTR_EL2_Type_OSDLR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _update_HDFGWTR_EL2_Type_OSDLR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)

def _get_HDFGWTR_EL2_Type_OSDLR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)

def _get_HDFGRTR_EL2_Type_OSECCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _update_HDFGRTR_EL2_Type_OSECCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _update_HDFGWTR_EL2_Type_OSECCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)

def _get_HDFGWTR_EL2_Type_OSECCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)

def _get_HDFGRTR_EL2_Type_OSLSR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)

def _update_HDFGRTR_EL2_Type_OSLSR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)

def _get_HDFGRTR_EL2_Type_PMBIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)

def _update_HDFGRTR_EL2_Type_PMBIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)

def _get_HDFGRTR_EL2_Type_PMBLIMITR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _update_HDFGRTR_EL2_Type_PMBLIMITR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _update_HDFGWTR_EL2_Type_PMBLIMITR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)

def _get_HDFGWTR_EL2_Type_PMBLIMITR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)

def _get_HDFGRTR_EL2_Type_PMBPTR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _update_HDFGRTR_EL2_Type_PMBPTR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _update_HDFGWTR_EL2_Type_PMBPTR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 24 24 x)

def _get_HDFGWTR_EL2_Type_PMBPTR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 24 24)

def _get_HDFGRTR_EL2_Type_PMBSR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _update_HDFGRTR_EL2_Type_PMBSR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _update_HDFGWTR_EL2_Type_PMBSR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 25 x)

def _get_HDFGWTR_EL2_Type_PMBSR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 25 25)

def _get_HDFGRTR_EL2_Type_PMCCFILTR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _update_HDFGRTR_EL2_Type_PMCCFILTR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _update_HDFGWTR_EL2_Type_PMCCFILTR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)

def _get_HDFGWTR_EL2_Type_PMCCFILTR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)

def _get_HDFGRTR_EL2_Type_PMCCNTR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _update_HDFGRTR_EL2_Type_PMCCNTR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _update_HDFGWTR_EL2_Type_PMCCNTR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)

def _get_HDFGWTR_EL2_Type_PMCCNTR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)

def _get_HDFGRTR_EL2_Type_PMCEIDn_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)

def _update_HDFGRTR_EL2_Type_PMCEIDn_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)

def _get_HDFGRTR_EL2_Type_PMCNTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _update_HDFGRTR_EL2_Type_PMCNTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _update_HDFGWTR_EL2_Type_PMCNTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)

def _get_HDFGWTR_EL2_Type_PMCNTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)

def _get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _update_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _update_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)

def _get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)

def _get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _update_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _update_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)

def _get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)

def _get_HDFGRTR_EL2_Type_PMINTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _update_HDFGRTR_EL2_Type_PMINTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _update_HDFGWTR_EL2_Type_PMINTEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)

def _get_HDFGWTR_EL2_Type_PMINTEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)

def _get_HDFGRTR_EL2_Type_PMMIR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)

def _update_HDFGRTR_EL2_Type_PMMIR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)

def _get_HDFGRTR_EL2_Type_PMOVS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _update_HDFGRTR_EL2_Type_PMOVS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _update_HDFGWTR_EL2_Type_PMOVS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)

def _get_HDFGWTR_EL2_Type_PMOVS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)

def _get_HDFGRTR_EL2_Type_PMSCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _update_HDFGRTR_EL2_Type_PMSCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _update_HDFGWTR_EL2_Type_PMSCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)

def _get_HDFGWTR_EL2_Type_PMSCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)

def _get_HDFGRTR_EL2_Type_PMSELR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _update_HDFGRTR_EL2_Type_PMSELR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _update_HDFGWTR_EL2_Type_PMSELR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)

def _get_HDFGWTR_EL2_Type_PMSELR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)

def _get_HDFGRTR_EL2_Type_PMSEVFR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _update_HDFGRTR_EL2_Type_PMSEVFR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _update_HDFGWTR_EL2_Type_PMSEVFR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)

def _get_HDFGWTR_EL2_Type_PMSEVFR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)

def _get_HDFGRTR_EL2_Type_PMSFCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _update_HDFGRTR_EL2_Type_PMSFCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _update_HDFGWTR_EL2_Type_PMSFCR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)

def _get_HDFGWTR_EL2_Type_PMSFCR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)

def _get_HDFGRTR_EL2_Type_PMSICR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _update_HDFGRTR_EL2_Type_PMSICR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _update_HDFGWTR_EL2_Type_PMSICR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)

def _get_HDFGWTR_EL2_Type_PMSICR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)

def _get_HDFGRTR_EL2_Type_PMSIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)

def _update_HDFGRTR_EL2_Type_PMSIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)

def _get_HDFGRTR_EL2_Type_PMSIRR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _update_HDFGRTR_EL2_Type_PMSIRR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _update_HDFGWTR_EL2_Type_PMSIRR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)

def _get_HDFGWTR_EL2_Type_PMSIRR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)

def _get_HDFGRTR_EL2_Type_PMSLATFR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _update_HDFGRTR_EL2_Type_PMSLATFR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _update_HDFGWTR_EL2_Type_PMSLATFR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)

def _get_HDFGWTR_EL2_Type_PMSLATFR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)

def _get_HDFGRTR_EL2_Type_PMUSERENR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)

def _update_HDFGRTR_EL2_Type_PMUSERENR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _update_HDFGWTR_EL2_Type_PMUSERENR_EL0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)

def _get_HDFGWTR_EL2_Type_PMUSERENR_EL0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)

def _get_HDFGRTR_EL2_Type_TRC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _update_HDFGRTR_EL2_Type_TRC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _update_HDFGWTR_EL2_Type_TRC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 33 33 x)

def _get_HDFGWTR_EL2_Type_TRC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 33 33)

def _get_HDFGRTR_EL2_Type_TRCAUTHSTATUS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 34 34)

def _update_HDFGRTR_EL2_Type_TRCAUTHSTATUS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 34 34 x)

def _get_HDFGRTR_EL2_Type_TRCAUXCTLR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)

def _update_HDFGRTR_EL2_Type_TRCAUXCTLR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _update_HDFGWTR_EL2_Type_TRCAUXCTLR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)

def _get_HDFGWTR_EL2_Type_TRCAUXCTLR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)

def _get_HDFGRTR_EL2_Type_TRCCLAIM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)

def _update_HDFGRTR_EL2_Type_TRCCLAIM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _update_HDFGWTR_EL2_Type_TRCCLAIM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)

def _get_HDFGWTR_EL2_Type_TRCCLAIM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)

def _get_HDFGRTR_EL2_Type_TRCCNTVRn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)

def _update_HDFGRTR_EL2_Type_TRCCNTVRn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _update_HDFGWTR_EL2_Type_TRCCNTVRn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 37 x)

def _get_HDFGWTR_EL2_Type_TRCCNTVRn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 37 37)

def _get_HDFGRTR_EL2_Type_TRCID (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)

def _update_HDFGRTR_EL2_Type_TRCID (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)

def _get_HDFGRTR_EL2_Type_TRCIMSPECn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)

def _update_HDFGRTR_EL2_Type_TRCIMSPECn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _update_HDFGWTR_EL2_Type_TRCIMSPECn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)

def _get_HDFGWTR_EL2_Type_TRCIMSPECn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)

def _get_HDFGRTR_EL2_Type_TRCOSLSR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)

def _update_HDFGRTR_EL2_Type_TRCOSLSR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)

def _get_HDFGRTR_EL2_Type_TRCPRGCTLR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)

def _update_HDFGRTR_EL2_Type_TRCPRGCTLR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _update_HDFGWTR_EL2_Type_TRCPRGCTLR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)

def _get_HDFGWTR_EL2_Type_TRCPRGCTLR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)

def _get_HDFGRTR_EL2_Type_TRCSEQSTR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)

def _update_HDFGRTR_EL2_Type_TRCSEQSTR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _update_HDFGWTR_EL2_Type_TRCSEQSTR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)

def _get_HDFGWTR_EL2_Type_TRCSEQSTR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)

def _get_HDFGRTR_EL2_Type_TRCSSCSRn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)

def _update_HDFGRTR_EL2_Type_TRCSSCSRn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _update_HDFGWTR_EL2_Type_TRCSSCSRn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 46 46 x)

def _get_HDFGWTR_EL2_Type_TRCSSCSRn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 46 46)

def _get_HDFGRTR_EL2_Type_TRCSTATR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 47 47)

def _update_HDFGRTR_EL2_Type_TRCSTATR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 47 x)

def _get_HDFGRTR_EL2_Type_TRCVICTLR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _update_HDFGRTR_EL2_Type_TRCVICTLR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _update_HDFGWTR_EL2_Type_TRCVICTLR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)

def _get_HDFGWTR_EL2_Type_TRCVICTLR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)

def _get_HDFGRTR_EL2_Type_nBRBCTL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _update_HDFGRTR_EL2_Type_nBRBCTL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _update_HDFGWTR_EL2_Type_nBRBCTL (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)

def _get_HDFGWTR_EL2_Type_nBRBCTL (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)

def _get_HDFGRTR_EL2_Type_nBRBDATA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _update_HDFGRTR_EL2_Type_nBRBDATA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _update_HDFGWTR_EL2_Type_nBRBDATA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)

def _get_HDFGWTR_EL2_Type_nBRBDATA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)

def _get_HDFGRTR_EL2_Type_nBRBIDR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)

def _update_HDFGRTR_EL2_Type_nBRBIDR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)

def _get_HDFGRTR_EL2_Type_nPMSNEVFR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def _update_HDFGRTR_EL2_Type_nPMSNEVFR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _update_HDFGWTR_EL2_Type_nPMSNEVFR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)

def _get_HDFGWTR_EL2_Type_nPMSNEVFR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)

def undefined_ICV_NMIAR1_EL1_Type (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector 64)

def Mk_ICV_NMIAR1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v

def _get_ICV_NMIAR1_EL1_Type_INTID (v : (BitVec 64)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _update_ICV_NMIAR1_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_GICC_AEOIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_GICC_AHPPIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_GICC_AIAR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_GICC_DIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_GICC_EOIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_GICC_HPPIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_GICC_IAR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_GICD_CLRSPI_NSR_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)

def _update_GICD_CLRSPI_SR_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)

def _update_GICD_SETSPI_NSR_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)

def _update_GICD_SETSPI_SR_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)

def _update_GICD_SGIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)

def _update_GICM_CLRSPI_NSR_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)

def _update_GICM_CLRSPI_SR_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)

def _update_GICM_SETSPI_NSR_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)

def _update_GICM_SETSPI_SR_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 0 x)

def _update_GICM_TYPER_Type_INTID (v : (BitVec 32)) (x : (BitVec 13)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 16 x)

def _update_GICR_INVLPIR_Type_INTID (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)

def _update_GICV_AEOIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 25)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 0 x)

def _update_GICV_AHPPIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 25)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 0 x)

def _update_GICV_AIAR_Type_INTID (v : (BitVec 32)) (x : (BitVec 25)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 0 x)

def _update_GICV_DIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 25)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 0 x)

def _update_GICV_EOIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 25)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 0 x)

def _update_GICV_HPPIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 25)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 0 x)

def _update_GICV_IAR_Type_INTID (v : (BitVec 32)) (x : (BitVec 25)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 24 0 x)

def _update_ICC_ASGI1R_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ICC_ASGI1R_Type_INTID (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ICC_DIR_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICC_DIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICC_EOIR0_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICC_EOIR0_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICC_EOIR1_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICC_EOIR1_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICC_HPPIR0_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICC_HPPIR0_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICC_HPPIR1_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICC_HPPIR1_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICC_IAR0_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICC_IAR0_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICC_IAR1_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICC_IAR1_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICC_NMIAR1_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICC_SGI0R_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ICC_SGI0R_Type_INTID (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ICC_SGI1R_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ICC_SGI1R_Type_INTID (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)

def _update_ICV_DIR_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICV_DIR_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICV_EOIR0_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICV_EOIR0_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICV_EOIR1_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICV_EOIR1_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICV_HPPIR0_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICV_HPPIR0_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICV_HPPIR1_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICV_HPPIR1_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICV_IAR0_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICV_IAR0_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICV_IAR1_EL1_Type_INTID (v : (BitVec 64)) (x : (BitVec 24)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _update_ICV_IAR1_Type_INTID (v : (BitVec 32)) (x : (BitVec 24)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 0 x)

def _get_GICC_AEOIR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_GICC_AHPPIR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_GICC_AIAR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)

def _get_GICC_DIR_Type_INTID (v : (BitVec 32)) : (BitVec 24) :=
  (Sail.BitVec.extractLsb v 23 0)


