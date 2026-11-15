/- Symbolic-immediate decoding on DeepMind's `Arm64.decode`: a word given as a template (literal opcode bits
appended to symbolic fields) is decoded by `simp`, each opcode test `(w &&& M) == C` being decided from the
known bits alone (`tst_false`, `tst_true`, `tst_eq`: `w &&& K = T` with `K`, `T` literals).  Used for `movz`/`movk`
(any 16-bit chunk), `b`/`bl` (26-bit offsets), `cbz` and `b.cond` (19-bit offsets). -/
import Arm64
namespace Proven.Apc

theorem tst_false {w K T M C : BitVec 32} (hw : w &&& K = T) (h : (T &&& M == C &&& K) = false) :
    (w &&& M == C) = false := by
  apply Bool.eq_false_iff.mpr; intro e
  have e' : w &&& M = C := beq_iff_eq.mp e
  have : T &&& M = C &&& K := by rw [← hw, ← e', BitVec.and_assoc, BitVec.and_comm K M, ← BitVec.and_assoc]
  simp [this] at h
theorem tst_eq {w K T C : BitVec 32} (hw : w &&& K = T) (h : (T == C &&& K) = false) : (w == C) = false := by
  apply Bool.eq_false_iff.mpr; intro e
  have e' : w = C := beq_iff_eq.mp e
  subst e'; simp [hw] at h
theorem tst_true {w K T M C : BitVec 32} (hw : w &&& K = T) (hM : (M &&& K == M) = true) (h : (T &&& M == C) = true) :
    (w &&& M == C) = true := by
  have hM' : M &&& K = M := beq_iff_eq.mp hM
  have h' : T &&& M = C := beq_iff_eq.mp h
  apply beq_iff_eq.mpr
  rw [← hM', BitVec.and_comm M K, ← BitVec.and_assoc, hw]; exact h'
theorem kbit {w K T : BitVec 32} (hw : w &&& K = T) {i : Nat} (hk : K.getLsbD i = true) : w.getLsbD i = T.getLsbD i := by
  rw [← hw, BitVec.getLsbD_and, hk, Bool.and_true]
theorem kext {w K T : BitVec 32} (hw : w &&& K = T) {i n : Nat} (hk : (K.extractLsb' i n == BitVec.allOnes n) = true) :
    w.extractLsb' i n = T.extractLsb' i n := by
  have hk' := beq_iff_eq.mp hk
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have := congrArg (·.getLsbD j) hk'
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_allOnes, hj, decide_true, Bool.true_and] at this ⊢
  rw [← hw, BitVec.getLsbD_and, this, Bool.and_true]

/-- decode a template word: every opcode test from the known bits -/
macro "decsym" hK:term : tactic => `(tactic|
  simp (disch := decide) only [Arm64.decode, tst_false $hK, tst_eq $hK, tst_true $hK, kbit $hK, kext $hK,
    Bool.false_eq_true, ↓reduceIte, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true, Bool.not_true,
    Bool.not_false])

/-! ## `movz` / `movk` (64-bit): `top ++ hw ++ imm16 ++ rd` -/
def movW (top : BitVec 9) (hw : BitVec 2) (imm : BitVec 16) (d : BitVec 5) : BitVec 32 := top ++ (hw ++ imm ++ d)
theorem movW_K (top hw imm d) : movW top hw imm d &&& 0xFF800000#32 = top ++ (0 : BitVec (2 + 16 + 5)) := by
  rw [show (0xFF800000#32) = BitVec.allOnes 9 ++ (0 : BitVec (2 + 16 + 5)) by decide, movW, BitVec.and_append,
    BitVec.and_allOnes]; simp
theorem movW_hw (top hw imm d) : (movW top hw imm d).extractLsb' 21 2 = hw := by
  rw [movW, BitVec.extractLsb'_append_eq_of_add_le (by decide), BitVec.extractLsb'_append_eq_of_le (by decide),
    BitVec.extractLsb'_append_eq_of_le (by decide)]; simp
theorem movW_imm (top hw imm d) : (movW top hw imm d).extractLsb' 5 16 = imm := by
  rw [movW, BitVec.extractLsb'_append_eq_of_add_le (by decide), BitVec.extractLsb'_append_eq_of_le (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (by decide)]; simp
theorem movW_d (top hw imm d) : (movW top hw imm d).extractLsb' 0 5 = d := by
  rw [movW, BitVec.extractLsb'_append_eq_of_add_le (by decide), BitVec.extractLsb'_append_eq_of_add_le (by decide)]; simp

theorem fromZR {d : BitVec 5} (hd : (d == 31#5) = false) : Arm64.Reg.fromZRBits d = .gpr d := by
  simp [Arm64.Reg.fromZRBits, hd]

theorem dec_movz (hw : BitVec 2) (imm : BitVec 16) (d : BitVec 5) (hd : (d == 31#5) = false) :
    Arm64.decode (movW 0x1A5#9 hw imm d) = some (.moveWide .W64 .MOVZ (.gpr d) imm (hw.toNat * 16)) := by
  have hK := movW_K 0x1A5#9 hw imm d
  decsym hK
  have e1 : (0x1A5#9 ++ (0 : BitVec (2 + 16 + 5))).getLsbD 31 = true := by decide
  have e2 : (BitVec.extractLsb' 29 2 (0x1A5#9 ++ (0 : BitVec (2 + 16 + 5)))).toNat = 2 := by decide
  simp only [e1, e2, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, movW_hw, movW_imm, movW_d, fromZR hd]
  rfl
theorem dec_movk (hw : BitVec 2) (imm : BitVec 16) (d : BitVec 5) (hd : (d == 31#5) = false) :
    Arm64.decode (movW 0x1E5#9 hw imm d) = some (.moveWide .W64 .MOVK (.gpr d) imm (hw.toNat * 16)) := by
  have hK := movW_K 0x1E5#9 hw imm d
  decsym hK
  have e1 : (0x1E5#9 ++ (0 : BitVec (2 + 16 + 5))).getLsbD 31 = true := by decide
  have e2 : (BitVec.extractLsb' 29 2 (0x1E5#9 ++ (0 : BitVec (2 + 16 + 5)))).toNat = 3 := by decide
  simp only [e1, e2, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, movW_hw, movW_imm, movW_d, fromZR hd]
  rfl

/-- `movk` value -/
def mkv (old : BitVec 64) (imm : BitVec 16) (hw : Nat) : BitVec 64 :=
  (old &&& ~~~(0xffff#64 <<< hw)) ||| ((imm.zeroExtend 64) <<< hw)
theorem li4 (c : BitVec 64) :
    mkv (mkv (mkv ((c.extractLsb' 0 16).zeroExtend 64 <<< 0) (c.extractLsb' 16 16) 16) (c.extractLsb' 32 16) 32)
      (c.extractLsb' 48 16) 48 = c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hi' : i < 64 := hi
  have m : ∀ k, (0xffff#64 <<< k).getLsbD i = (decide (k ≤ i) && decide (i < k + 16)) := by
    intro k; rw [BitVec.getLsbD_shiftLeft]
    simp only [show (0xffff#64) = BitVec.ofNat 64 (2 ^ 16 - 1) from rfl, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    by_cases h : k ≤ i <;> simp [h, hi']
    rw [Bool.eq_iff_iff]; simp; omega
  simp only [mkv, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, m, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  by_cases h1 : i < 16 <;> by_cases h2 : i < 32 <;> by_cases h3 : i < 48 <;> simp_all
  all_goals (generalize c[i] = b; cases b <;> simp <;> omega)

/-! ## offsets: sign-extended immediates, times 4 -/
theorem off_fwd {w : Nat} (hw : 1 ≤ w) (hw' : w ≤ 64) {n : Nat} (hn : n < 2 ^ (w - 1)) :
    ((BitVec.ofNat w n).signExtend 64) <<< 2 = BitVec.ofNat 64 (4 * n) := by
  have h2 : 2 ^ (w - 1) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  have h3 : 2 ^ (w - 1) < 2 ^ w := Nat.pow_lt_pow_right (by decide) (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show n < 2 ^ w by omega), Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
  simp only [show ¬ 2 ^ (w - 1) ≤ n by omega, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
    Nat.shiftLeft_eq]
  omega
theorem off_back {w : Nat} (hw : 1 ≤ w) (hw' : w ≤ 62) {n : Nat} (hn : 0 < n) (hn' : n ≤ 2 ^ (w - 1)) :
    ((BitVec.ofNat w (2 ^ w - n)).signExtend 64) <<< 2 = BitVec.ofNat 64 (2 ^ 64 - 4 * n) := by
  have h2 : 2 ^ (w - 1) ≤ 2 ^ 61 := Nat.pow_le_pow_right (by decide) (by omega)
  have h3 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have h4 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 2 ^ w - n < 2 ^ w by omega), Nat.mod_eq_of_lt (show 2 ^ w - n < 2 ^ 64 by omega)]
  simp only [show 2 ^ (w - 1) ≤ 2 ^ w - n by omega, decide_true, ↓reduceIte, Nat.shiftLeft_eq]
  generalize 2 ^ w = P at *; generalize 2 ^ (w - 1) = Q at *
  omega

/-! ## `b` / `bl`: `top6 ++ imm26` -/
theorem bW_K (top : BitVec 6) (imm : BitVec 26) : (top ++ imm) &&& 0xFC000000#32 = top ++ (0 : BitVec 26) := by
  rw [show (0xFC000000#32) = BitVec.allOnes 6 ++ (0 : BitVec 26) by decide, BitVec.and_append, BitVec.and_allOnes]; simp
theorem bW_imm (top : BitVec 6) (imm : BitVec 26) : (top ++ imm).extractLsb' 0 26 = imm := by
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]; simp
theorem dec_bsym (imm : BitVec 26) : Arm64.decode (0x05#6 ++ imm) = some (.b ((imm.signExtend 64) <<< 2)) := by
  have hK := bW_K 0x05#6 imm
  decsym hK
  have e1 : (0x05#6 ++ (0 : BitVec 26)).getLsbD 31 = false := by decide
  simp only [e1, Bool.false_eq_true, ↓reduceIte, bW_imm]
theorem dec_blsym (imm : BitVec 26) : Arm64.decode (0x25#6 ++ imm) = some (.bl ((imm.signExtend 64) <<< 2)) := by
  have hK := bW_K 0x25#6 imm
  decsym hK
  have e1 : (0x25#6 ++ (0 : BitVec 26)).getLsbD 31 = true := by decide
  simp only [e1, ↓reduceIte, bW_imm]

/-! ## `cbz xt` (64-bit): `0xB4 ++ imm19 ++ rt` -/
theorem cbzW_K (imm : BitVec 19) (rt : BitVec 5) : (0xB4#8 ++ imm ++ rt) &&& 0xFF000000#32 = 0xB4#8 ++ (0 : BitVec 19) ++ (0 : BitVec 5) := by
  rw [show (0xFF000000#32) = BitVec.allOnes 8 ++ (0 : BitVec 19) ++ (0 : BitVec 5) by decide, BitVec.and_append,
    BitVec.and_append, BitVec.and_allOnes]; simp
theorem cbzW_imm (imm : BitVec 19) (rt : BitVec 5) : (0xB4#8 ++ imm ++ rt).extractLsb' 5 19 = imm := by
  rw [BitVec.extractLsb'_append_eq_of_le (by decide), BitVec.extractLsb'_append_eq_of_add_le (by decide)]; simp
theorem cbzW_rt (imm : BitVec 19) (rt : BitVec 5) : (0xB4#8 ++ imm ++ rt).extractLsb' 0 5 = rt := by
  rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]; simp
theorem dec_cbzsym (imm : BitVec 19) (rt : BitVec 5) (hr : (rt == 31#5) = false) :
    Arm64.decode (0xB4#8 ++ imm ++ rt) = some (.cbz .W64 false (.gpr rt) ((imm.signExtend 64) <<< 2)) := by
  have hK := cbzW_K imm rt
  decsym hK
  have e1 : (0xB4#8 ++ (0 : BitVec 19) ++ (0 : BitVec 5)).getLsbD 31 = true := by decide
  have e2 : (0xB4#8 ++ (0 : BitVec 19) ++ (0 : BitVec 5)).getLsbD 24 = false := by decide
  simp only [e1, e2, cbzW_imm, cbzW_rt, fromZR hr]
  rfl

/-! ## `b.cond`: `0x54 ++ imm19 ++ 0 ++ cond` (cond literal) -/
theorem bcW_K (imm : BitVec 19) (c : BitVec 4) :
    (0x54#8 ++ imm ++ 0#1 ++ c) &&& 0xFF00001F#32 = 0x54#8 ++ (0 : BitVec 19) ++ 0#1 ++ c := by
  rw [show (0xFF00001F#32) = BitVec.allOnes 8 ++ (0 : BitVec 19) ++ BitVec.allOnes 1 ++ BitVec.allOnes 4 by decide,
    BitVec.and_append, BitVec.and_append, BitVec.and_append, BitVec.and_allOnes, BitVec.and_allOnes, BitVec.and_allOnes]
  simp
theorem bcW_imm (imm : BitVec 19) (c : BitVec 4) : (0x54#8 ++ imm ++ 0#1 ++ c).extractLsb' 5 19 = imm := by
  rw [BitVec.extractLsb'_append_eq_of_le (by decide), BitVec.extractLsb'_append_eq_of_le (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (by decide)]; simp
theorem dec_bcsym (imm : BitVec 19) (c : BitVec 4) (hc : c = 0#4 ∨ c = 1#4 ∨ c = 2#4 ∨ c = 3#4 ∨ c = 10#4 ∨ c = 11#4) :
    Arm64.decode (0x54#8 ++ imm ++ 0#1 ++ c) = some (.bCond (Arm64.CondCode.ofBits c) ((imm.signExtend 64) <<< 2)) := by
  have hK := bcW_K imm c
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · decsym hK
    simp only [bcW_imm]
    rfl

end Proven.Apc
