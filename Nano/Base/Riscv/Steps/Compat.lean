/- Drop-in replacements for the generated per-register step lemmas (`Riscv/Legacy/Steps/{Words,BranchWords,
MemWords,ArrWords}.lean`): the lemmas the compiler proofs use, with the SAME names and statements, proved as
instances of the register-generic lemmas of `Riscv/Steps/Gen*.lean` (nothing here unfolds the Sail model).
The `Arr2Words` lemmas are in `CompatArr2.lean` (they need `Riscv/Direct/Arr2Code.lean`).
Not provided: the per-word instances (`W.*`, `MW.*`, `W8.*` other than `lbuT`/`sbT`) and the branch
dispatchers other than `x5`/`x0`; nothing used them. -/
import Spec.Code
import Spec.ArrCode
import Nano.Base.Riscv.Steps.GenMem
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven

namespace Compat

theorem getX0 (s : St) : getX s 0 = 0 := rfl

theorem T_ne0 (k : Nat) : T k ≠ 0 := by
  unfold T; split <;> decide

theorem A8_ne0 (i : Fin 8) : A8 i ≠ 0 := by
  intro e; have := congrArg Fin.val e; simp [A8] at this

theorem Next_rd0 {s s' : St} {pc : BitVec 64} {v v' : BitVec 64} {m} (hn : Next s s' pc 0 v m) :
    Next s s' pc 0 v' m :=
  ⟨hn.ret, hn.cfg, hn.pc, fun j => by rw [hn.x j]; simp, hn.mem⟩

theorem mv {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
    (rd rs : Fin 32) (hrd : rd ≠ 0) (hi : instrAt s pc (encR 0 0 rd 0 rs)) :
    ∃ s', Next s s' (pc + 4) rd (getX s rs) s.mem := by
  obtain ⟨s', hn⟩ := G.step_add h hpc hok rd 0 rs hrd hi
  rw [getX0, show (0 : BitVec 64) + getX s rs = getX s rs by simp] at hn; exact ⟨s', hn⟩

theorem se0 : (0 : BitVec 12).signExtend 64 = 0 := by decide

theorem toNat_ne0 {a : BitVec 64} (ha : ¬a = 0) : a.toNat ≠ 0 :=
  fun e => ha (BitVec.eq_of_toNat_eq (by simpa using e))

theorem ite_lt1 (a : BitVec 64) :
    (if a < (1 : BitVec 12).signExtend 64 then (1 : BitVec 64) else 0) = if a = 0 then 1 else 0 := by
  rw [show (1 : BitVec 12).signExtend 64 = 1 by decide]
  by_cases ha : a = 0
  · subst ha; decide
  · have := toNat_ne0 ha; rw [if_neg ha, if_neg]; rw [BitVec.lt_def]; simp; omega

theorem ite_0lt (a : BitVec 64) :
    (if (0 : BitVec 64) < a then (1 : BitVec 64) else 0) = if a = 0 then 0 else 1 := by
  by_cases ha : a = 0
  · subst ha; decide
  · have := toNat_ne0 ha; rw [if_neg ha, if_pos]; rw [BitVec.lt_def]; simp; omega

end Compat

open Compat

/-! ## `Words.lean` -/

section
variable {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
include h hpc hok

theorem step_op (op : Op) (k : Nat) (hk : k < 10) (hi : instrAt s pc (iOp op k)) :
    ∃ s', Next s s' (pc + 4) (T k) (op.raw (getX s (T k)) (getX s (T (k + 1)))) s.mem := by
  unfold iOp at hi
  cases op
  · exact G.step_add h hpc hok _ _ _ (T_ne0 k) hi
  · exact G.step_sub h hpc hok _ _ _ hi
  · exact G.step_and h hpc hok _ _ _ hi
  · exact G.step_or h hpc hok _ _ _ hi
  · exact G.step_xor h hpc hok _ _ _ hi
  · exact G.step_sll h hpc hok _ _ _ hi
  · exact G.step_srl h hpc hok _ _ _ hi
  · exact G.step_sra h hpc hok _ _ _ hi
  · exact G.step_sltu h hpc hok _ _ _ hi
  · exact G.step_slt h hpc hok _ _ _ hi
  · exact G.step_xor h hpc hok _ _ _ hi

theorem step_var (i k : Nat) (hk : k < 11) (hi4 : i < 4) (hi : instrAt s pc (iVar i k)) :
    ∃ s', Next s s' (pc + 4) (T k) (getX s (A i)) s.mem :=
  mv h hpc hok (T k) (A i) (T_ne0 k) hi

theorem step_zero (k : Nat) (hk : k < 11) (hi : instrAt s pc (iZero k)) :
    ∃ s', Next s s' (pc + 4) (T k) 0 s.mem := by
  obtain ⟨s', hn⟩ := G.step_addi h hpc hok (T k) 0 0 hi
  rw [getX0, se0, show (0 : BitVec 64) + 0 = 0 by decide] at hn; exact ⟨s', hn⟩

theorem step_shl (k : Nat) (hk : k < 11) (hi : instrAt s pc (iShl k)) :
    ∃ s', Next s s' (pc + 4) (T k) ((getX s (T k)) <<< 1) s.mem :=
  G.step_slli h hpc hok (T k) (T k) 1 hi

theorem step_inc (k : Nat) (hk : k < 11) (hi : instrAt s pc (iInc k)) :
    ∃ s', Next s s' (pc + 4) (T k) ((getX s (T k)) + 1) s.mem := by
  obtain ⟨s', hn⟩ := G.step_addi h hpc hok (T k) (T k) 1 hi
  rw [show (1 : BitVec 12).signExtend 64 = 1 by decide] at hn; exact ⟨s', hn⟩

theorem step_seqz (k : Nat) (hk : k < 10) (hi : instrAt s pc (iSeqz k)) :
    ∃ s', Next s s' (pc + 4) (T k) (if (getX s (T k)) = 0 then 1 else 0) s.mem := by
  obtain ⟨s', hn⟩ := G.step_sltiu h hpc hok (T k) (T k) 1 hi
  rw [ite_lt1] at hn; exact ⟨s', hn⟩

theorem step_snez (k : Nat) (hk : k < 9) (hi : instrAt s pc (iSnez k)) :
    ∃ s', Next s s' (pc + 4) (T k) (if (getX s (T k)) = 0 then 0 else 1) s.mem := by
  obtain ⟨s', hn⟩ := G.step_sltu h hpc hok (T k) 0 (T k) hi
  rw [getX0, ite_0lt] at hn; exact ⟨s', hn⟩

theorem step_neg (k : Nat) (hk : k < 9) (hi : instrAt s pc (iNeg k)) :
    ∃ s', Next s s' (pc + 4) (T k) (-(getX s (T k))) s.mem := by
  obtain ⟨s', hn⟩ := G.step_sub h hpc hok (T k) 0 (T k) hi
  rw [getX0, show (0 : BitVec 64) - getX s (T k) = -getX s (T k) by simp] at hn; exact ⟨s', hn⟩

theorem step_xor2 (k : Nat) (hk : k < 9) (hi : instrAt s pc (iXor2 k)) :
    ∃ s', Next s s' (pc + 4) (T k) ((getX s (T k)) ^^^ (getX s (T (k + 2)))) s.mem :=
  G.step_xor h hpc hok _ _ _ hi

theorem step_res (hi : instrAt s pc iRes) : ∃ s', Next s s' (pc + 4) 10 (getX s 5) s.mem :=
  mv h hpc hok 10 5 (by decide) hi

theorem step_ret (hi : instrAt s pc iRet) (he : (getX s 1).toNat % 2 = 0) :
    ∃ s', Next s s' (getX s 1) 0 0 s.mem := by
  rw [show iRet = BitVec.ofNat 32 ((0#12 : BitVec 12).toNat <<< 20 ||| (1 : Fin 32).val <<< 15 |||
    (0 : Fin 32).val <<< 7 ||| 0x67) by decide] at hi
  obtain ⟨s', hn⟩ := G.step_jalr h hpc hok 0 1 0 hi (by simpa [se0] using he)
  exact ⟨s', by simpa [se0] using (Next_rd0 hn)⟩

/-! ## `BranchWords.lean` -/

omit h hpc hok in
theorem bcond_iff_toInt (a b : BitVec 64) : a.slt b = true ↔ a.toInt < b.toInt := by simp [BitVec.slt_iff_toInt_lt]
omit h hpc hok in
theorem bcond_iff_toNat (a b : BitVec 64) : a.ult b = true ↔ a.toNat < b.toNat := by simp [BitVec.ult_iff_lt, BitVec.lt_def]

theorem beq_5_0_t (o : BitVec 12) (hi : instrAt s pc (wB 0 5 0 o)) (hc : getX s 5 = 0#64) :
    ∃ s', Next s s' (pc + boff o) 0 0 s.mem := G.beq_t h hpc hok 5 0 o hi hc
theorem beq_5_0_n (o : BitVec 12) (hi : instrAt s pc (wB 0 5 0 o)) (hc : ¬getX s 5 = 0#64) :
    ∃ s', Next s s' (pc + 4) 0 0 s.mem := G.beq_n h hpc hok 5 0 o hi hc
theorem step_beq_5_0 (o : BitVec 12) (hi : instrAt s pc (wB 0 5 0 o)) :
    ∃ s', Next s s' (if bcond 0 (getX s 5) (getX s 0) then pc + boff o else pc + 4) 0 0 s.mem := by
  have e0 : getX s 0 = 0#64 := rfl; simp only [e0]
  have key : bcond 0 (getX s 5) (0#64) = true ↔ getX s 5 = 0#64 := by simp [bcond]
  by_cases hc : getX s 5 = 0#64
  · rw [if_pos (key.2 hc)]; exact beq_5_0_t h hpc hok o hi hc
  · rw [if_neg (fun e => hc (key.1 e))]; exact beq_5_0_n h hpc hok o hi hc
theorem beq_5_6_t (o : BitVec 12) (hi : instrAt s pc (wB 0 5 6 o)) (hc : getX s 5 = getX s 6) :
    ∃ s', Next s s' (pc + boff o) 0 0 s.mem := G.beq_t h hpc hok 5 6 o hi hc

theorem step_jal_0 (o : BitVec 20) (hi : instrAt s pc (wJ 0 o)) :
    ∃ s', Next s s' (pc + joff o) 0 (pc + 4) s.mem := G.step_jal h hpc hok 0 o hi

end

/-! ## `MemWords.lean` -/

def memD : List (Fin 32) := [5, 6, 7, 28, 29, 30, 31, 14, 15, 16, 17]
def memB : List (Fin 32) := [9, 10, 11, 12, 13]

def iLbu (rd rs1 : Fin 32) : BitVec 32 := BitVec.ofNat 32 (rs1.val <<< 15 ||| 4 <<< 12 ||| rd.val <<< 7 ||| 0x03)
def iLd (rd rs1 : Fin 32) : BitVec 32 := BitVec.ofNat 32 (rs1.val <<< 15 ||| 3 <<< 12 ||| rd.val <<< 7 ||| 0x03)
def iSb (rs2 rs1 : Fin 32) : BitVec 32 := BitVec.ofNat 32 (rs2.val <<< 20 ||| rs1.val <<< 15 ||| 0 <<< 12 ||| 0x23)
def iSd (rs2 rs1 : Fin 32) : BitVec 32 := BitVec.ofNat 32 (rs2.val <<< 20 ||| rs1.val <<< 15 ||| 3 <<< 12 ||| 0x23)

namespace Compat
open G

theorem iLbu_eq (rd rs1 : Fin 32) : iLbu rd rs1 = G.encL 4 0 rd rs1 := by simp [iLbu, G.encL]
theorem iLd_eq (rd rs1 : Fin 32) : iLd rd rs1 = G.encL 3 0 rd rs1 := by simp [iLd, G.encL]
theorem iSb_eq (rs2 rs1 : Fin 32) : iSb rs2 rs1 = G.encS 0 0 rs2 rs1 := by
  rw [G.encS_eq]; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [iSb, G.fS, BitVec.getLsbD_ofNat, BitVec.getLsbD_or, Nat.testBit_or, Nat.testBit_shiftLeft]
  enc_bits
theorem iSd_eq (rs2 rs1 : Fin 32) : iSd rs2 rs1 = G.encS 3 0 rs2 rs1 := by
  rw [G.encS_eq]; apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [iSd, G.fS, BitVec.getLsbD_ofNat, BitVec.getLsbD_or, Nat.testBit_or, Nat.testBit_shiftLeft]
  enc_bits

theorem addr0 (x : BitVec 64) : x + (0 : BitVec 12).signExtend 64 = x := by rw [se0]; simp

end Compat

theorem step_lbu_raw {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (rd rs1 : Fin 32) (hd : rd ∈ memD) (hb : rs1 ∈ memB)
    (hi : instrAt s pc (iLbu rd rs1))
    (ha : 0x80000000 ≤ (getX s rs1).toNat ∧ (getX s rs1).toNat + 1 ≤ 0x100000000) {b : BitVec 8} (hb1 : s.mem[(getX s rs1).toNat]? = some b) :
    ∃ s', Next s s' (pc + 4) rd (b.setWidth 64) s.mem := by
  rw [iLbu_eq] at hi; exact G.step_lbu h hpc hok rd rs1 0 hi (addr0 _) ha hb1

theorem step_sb_raw {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (rs2 rs1 : Fin 32) (hd : rs2 ∈ memD) (hb : rs1 ∈ memB)
    (hi : instrAt s pc (iSb rs2 rs1))
    (ha : 0x80000000 ≤ (getX s rs1).toNat ∧ (getX s rs1).toNat + 1 ≤ 0x100000000) :
    ∃ s', Next s s' (pc + 4) 0 0 (s.mem.insert (getX s rs1).toNat ((getX s rs2).setWidth 8)) := by
  rw [iSb_eq] at hi; exact G.step_sb h hpc hok rs2 rs1 0 hi (addr0 _) ha

theorem step_ld_raw {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (rd rs1 : Fin 32) (hd : rd ∈ memD) (hb : rs1 ∈ memB)
    (hi : instrAt s pc (iLd rd rs1))
    (ha : 0x80000000 ≤ (getX s rs1).toNat ∧ (getX s rs1).toNat + 8 ≤ 0x100000000) (hal : (getX s rs1).toNat % 8 = 0)
    {b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8} (h0 : s.mem[(getX s rs1).toNat]? = some b0) (h1 : s.mem[(getX s rs1).toNat + 1]? = some b1) (h2 : s.mem[(getX s rs1).toNat + 2]? = some b2) (h3 : s.mem[(getX s rs1).toNat + 3]? = some b3) (h4 : s.mem[(getX s rs1).toNat + 4]? = some b4) (h5 : s.mem[(getX s rs1).toNat + 5]? = some b5) (h6 : s.mem[(getX s rs1).toNat + 6]? = some b6) (h7 : s.mem[(getX s rs1).toNat + 7]? = some b7) :
    ∃ s', Next s s' (pc + 4) rd (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) s.mem := by
  rw [iLd_eq] at hi; exact G.step_ld h hpc hok rd rs1 0 hi (addr0 _) ha hal h0 h1 h2 h3 h4 h5 h6 h7

theorem step_sd_raw {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (rs2 rs1 : Fin 32) (hd : rs2 ∈ memD) (hb : rs1 ∈ memB)
    (hi : instrAt s pc (iSd rs2 rs1))
    (ha : 0x80000000 ≤ (getX s rs1).toNat ∧ (getX s rs1).toNat + 8 ≤ 0x100000000) (hal : (getX s rs1).toNat % 8 = 0) :
    ∃ s', Next s s' (pc + 4) 0 0 (storeBytes s.mem (getX s rs1).toNat (le8 (getX s rs2))) := by
  rw [iSd_eq] at hi; exact G.step_sd h hpc hok rs2 rs1 0 hi (addr0 _) ha hal

/-! ## `ArrWords.lean` -/

namespace W8
theorem lbuT {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x0002c283#32)
    (ha : 0x80000000 ≤ (getX s 5).toNat ∧ (getX s 5).toNat + 1 ≤ 0x100000000) {b : BitVec 8}
    (hb : s.mem[(getX s 5).toNat]? = some b) :
    ∃ s', Next s s' (pc + 4) 5 (b.setWidth 64) s.mem := by
  rw [show (0x0002c283#32 : BitVec 32) = G.encL 4 0 5 5 by decide] at hi
  exact G.step_lbu h hpc hok 5 5 0 hi (addr0 _) ha hb
theorem sbT {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x00628023#32)
    (ha : 0x80000000 ≤ (getX s 5).toNat ∧ (getX s 5).toNat + 1 ≤ 0x100000000) :
    ∃ s', Next s s' (pc + 4) 0 0 (s.mem.insert (getX s 5).toNat ((getX s 6).setWidth 8)) := by
  rw [show (0x00628023#32 : BitVec 32) = G.encS 0 0 6 5 by decide] at hi
  exact G.step_sb h hpc hok 6 5 0 hi (addr0 _) ha
end W8

section
variable {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
include h hpc hok

theorem step_var8 (i : Fin 8) (k : Nat) (hk : k < 7) (hi : instrAt s pc (iVar8 i k)) :
    ∃ s', Next s s' (pc + 4) (T k) (getX s (A8 i)) s.mem :=
  mv h hpc hok (T k) (A8 i) (T_ne0 k) hi

theorem step_mv8 (v : Fin 8) (hi : instrAt s pc (iMv8 v)) :
    ∃ s', Next s s' (pc + 4) (A8 v) (getX s 5) s.mem :=
  mv h hpc hok (A8 v) 5 (A8_ne0 v) hi

end

end Proven
