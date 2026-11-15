/- Symbolic-field decoding on the Sail model: `__DecodeA64 pc w` for a word known only through `w &&& K = T`
(`K`, `T` literals: the opcode bits), every dispatch test decided from the known bits. -/
import Arm.Machine
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000
set_option linter.all false

namespace ArmProof

theorem xl_and {w : Nat} (x y : BitVec w) (hi lo : Nat) :
    BitVec.extractLsb hi lo (x &&& y) = BitVec.extractLsb hi lo x &&& BitVec.extractLsb hi lo y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'; have : i ≤ hi - lo := by omega
  simp [BitVec.getLsbD_extractLsb, this]

theorem sx_false {w K T : BitVec 32} (hw : w &&& K = T) {hi lo : Nat} {C : BitVec (hi - lo + 1)}
    (h : (BitVec.extractLsb hi lo T == C &&& BitVec.extractLsb hi lo K) = false) :
    (Sail.BitVec.extractLsb w hi lo == C) = false := by
  apply Bool.eq_false_iff.mpr; intro e
  have e' : BitVec.extractLsb hi lo w = C := beq_iff_eq.mp e
  rw [← hw, xl_and, e'] at h; simp at h

theorem sx_eq {w K T : BitVec 32} (hw : w &&& K = T) {hi lo : Nat}
    (h : (BitVec.extractLsb hi lo K == BitVec.allOnes _) = true) :
    Sail.BitVec.extractLsb w hi lo = BitVec.extractLsb hi lo T := by
  have h' := beq_iff_eq.mp h
  show BitVec.extractLsb hi lo w = _
  rw [← hw, xl_and, h', BitVec.and_allOnes]

theorem sx_true {w K T : BitVec 32} (hw : w &&& K = T) {hi lo : Nat} {C : BitVec (hi - lo + 1)}
    (hk : (BitVec.extractLsb hi lo K == BitVec.allOnes _) = true) (h : (BitVec.extractLsb hi lo T == C) = true) :
    (Sail.BitVec.extractLsb w hi lo == C) = true := by
  rw [sx_eq hw hk]; exact h

theorem sw_false {w K T C : BitVec 32} (hw : w &&& K = T) (h : (T == C &&& K) = false) : (w == C) = false := by
  apply Bool.eq_false_iff.mpr; intro e
  have e' : w = C := beq_iff_eq.mp e
  subst e'; simp [hw] at h

theorem sl_eq {w K T : BitVec 32} (hw : w &&& K = T) {st len : Nat}
    (h : (BitVec.extractLsb' st len K == BitVec.allOnes _) = true) :
    Sail.BitVec.slice w st len = BitVec.extractLsb' st len T := by
  have h' := beq_iff_eq.mp h
  show BitVec.extractLsb' st len w = _
  have : BitVec.extractLsb' st len (w &&& K) = BitVec.extractLsb' st len w &&& BitVec.extractLsb' st len K := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi'; simp [BitVec.getLsbD_extractLsb', hi']
  rw [← hw, this, h', BitVec.and_allOnes]

theorem if_skip {α : Type} {C : Bool} (hc : C = false) (m : SailM Bool) (X Y : SailM α) :
    (do if ((← ((pure C) <&&> m)) : Bool) then X else Y) = Y := by subst hc; rfl

theorem if_take {α : Type} {C : Bool} (hc : C = true) (m : SailM Bool) (X Y : SailM α) :
    (do if ((← ((pure C) <&&> m)) : Bool) then X else Y) = (do if ((← m) : Bool) then X else Y) := by
  subst hc; funext s; rfl

theorem ite_f {α : Sort _} {C : Bool} (hc : C = false) (X Y : α) : (if C = true then X else Y) = Y := by simp [hc]
theorem ite_t {α : Sort _} {C : Bool} (hc : C = true) (X Y : α) : (if C = true then X else Y) = X := by simp [hc]

/-- decide one dispatch condition from the known bits -/
macro "sdisch" hK:ident : tactic => `(tactic| (simp (config := {decide := true}) (disch := decide) only
  [sx_true $hK:ident, sx_false $hK:ident, sw_false $hK:ident, Bool.false_and, Bool.and_false, Bool.true_and,
   Bool.and_true, Bool.or_false, Bool.false_or, Bool.or_true, Bool.true_or]))

/-- prune the dispatch chain of `d` (a sub-decoder or `__DecodeA64`) -/
macro "sprune" hK:ident d:ident : tactic => `(tactic| (
  rw [$d:ident]
  simp (config := {maxSteps := 4000000}) (disch := sdisch $hK) only [↓if_skip, ↓if_take, ↓ite_f, ↓ite_t]))

/-- finish: the SEE test and the fixed fields -/
macro "sfin" hK:ident h:ident hs:ident see:ident : tactic => `(tactic| (
  have hk : ∀ k : Int, 1 ≤ k → $see:ident < k := fun k hk => by omega
  simp (config := {decide := true}) (disch := decide) only [sl_eq $hK:ident, BitVec.extractLsb', BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceShiftRight, Nat.reduceAdd, Nat.reduceSub, PreSail.readReg,
    PreSail.writeReg, bind, pure, EStateM.bind, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, modify,
    modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, $h:ident, $hs:ident, hk, ↓reduceIte]))

theorem dec_bsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFC000000#32 = 0x14000000#32) :
    __DecodeA64 pc w s = decode_b_uncond_aarch64_instrs_branch_unconditional_immediate (Sail.BitVec.slice w 0 26) 0#1
      { s with regs := s.regs.insert .SEE (67 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_BranchExcSys
  sfin hK h hs see
  all_goals rfl









theorem dec_blsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFC000000#32 = 0x94000000#32) :
    __DecodeA64 pc w s = decode_bl_aarch64_instrs_branch_unconditional_immediate (Sail.BitVec.slice w 0 26) 1#1
      { s with regs := s.regs.insert .SEE (68 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_BranchExcSys
  sfin hK h hs see
  all_goals rfl

theorem dec_cbzsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFF000000#32 = 0xB4000000#32) :
    __DecodeA64 pc w s = decode_cbz_aarch64_instrs_branch_conditional_compare (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 19) 0#1 1#1
      { s with regs := s.regs.insert .SEE (118 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_BranchExcSys
  sfin hK h hs see
  all_goals rfl

theorem dec_cbnzsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFF000000#32 = 0xB5000000#32) :
    __DecodeA64 pc w s = decode_cbnz_aarch64_instrs_branch_conditional_compare (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 19) 1#1 1#1
      { s with regs := s.regs.insert .SEE (117 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_BranchExcSys
  sfin hK h hs see
  all_goals rfl

theorem dec_bcsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFF000010#32 = 0x54000000#32) :
    __DecodeA64 pc w s = decode_b_cond_aarch64_instrs_branch_conditional_cond (Sail.BitVec.slice w 0 4) (Sail.BitVec.slice w 5 19)
      { s with regs := s.regs.insert .SEE (69 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_BranchExcSys
  sfin hK h hs see
  all_goals rfl

theorem dec_movzsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFF800000#32 = 0xD2800000#32) :
    __DecodeA64 pc w s = decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 16) (Sail.BitVec.slice w 21 2) 2#2 1#1
      { s with regs := s.regs.insert .SEE (698 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcImm
  sfin hK h hs see
  all_goals rfl

theorem dec_movksym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFF800000#32 = 0xF2800000#32) :
    __DecodeA64 pc w s = decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 16) (Sail.BitVec.slice w 21 2) 3#2 1#1
      { s with regs := s.regs.insert .SEE (696 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcImm
  sfin hK h hs see
  all_goals rfl

theorem dec_addisym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFC00000#32 = 0x91000000#32) :
    __DecodeA64 pc w s = decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) (Sail.BitVec.slice w 10 12) 0#1 0#1 0#1 1#1
      { s with regs := s.regs.insert .SEE (18 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcImm
  sfin hK h hs see
  all_goals rfl

theorem dec_subisym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFC00000#32 = 0xD1000000#32) :
    __DecodeA64 pc w s = decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) (Sail.BitVec.slice w 10 12) 0#1 0#1 1#1 1#1
      { s with regs := s.regs.insert .SEE (20 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_DataProcImm
  sfin hK h hs see
  all_goals rfl

theorem dec_ldrbsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFC00000#32 = 0x39400000#32) :
    __DecodeA64 pc w s = decode_ldrb_imm_aarch64_instrs_memory_single_general_immediate_unsigned (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) (Sail.BitVec.slice w 10 12) 1#2 0#2
      { s with regs := s.regs.insert .SEE (633 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_LoadStore
  sfin hK h hs see
  all_goals rfl

theorem dec_strbsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFC00000#32 = 0x39000000#32) :
    __DecodeA64 pc w s = decode_strb_imm_aarch64_instrs_memory_single_general_immediate_unsigned (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) (Sail.BitVec.slice w 10 12) 0#2 0#2
      { s with regs := s.regs.insert .SEE (651 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_LoadStore
  sfin hK h hs see
  all_goals rfl

theorem dec_ldrsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFC00000#32 = 0xF9400000#32) :
    __DecodeA64 pc w s = decode_ldr_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) (Sail.BitVec.slice w 10 12) 1#2 3#2
      { s with regs := s.regs.insert .SEE (630 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_LoadStore
  sfin hK h hs see
  all_goals rfl

theorem dec_strsym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFC00000#32 = 0xF9000000#32) :
    __DecodeA64 pc w s = decode_str_imm_gen_aarch64_instrs_memory_single_general_immediate_unsigned (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) (Sail.BitVec.slice w 10 12) 0#2 3#2
      { s with regs := s.regs.insert .SEE (648 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_LoadStore
  sfin hK h hs see
  all_goals rfl

theorem dec_stursym (s : St) (pc see : Int) (hs : see < 1) (h : s.regs.get? .SEE = some see) {w : BitVec 32}
    (hK : w &&& 0xFFE00C00#32 = 0xF8000000#32) :
    __DecodeA64 pc w s = decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal (Sail.BitVec.slice w 0 5) (Sail.BitVec.slice w 5 5) (Sail.BitVec.slice w 12 9) 0#2 3#2
      { s with regs := s.regs.insert .SEE (687 : Int) } := by
  sprune hK __DecodeA64
  sprune hK __DecodeA64_LoadStore
  sfin hK h hs see
  all_goals rfl

end ArmProof
