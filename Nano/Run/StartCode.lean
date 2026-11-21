/- Machine bridge (Opus box E): the code around the defs — the stubs (g34: word 0 = jump to the start code, the
out-of-memory and capacity exits) and the start code (g35 / GenTop.startW: heap and stack set-up, the call of main,
the copy of main's output buffer to a3, the exit registers) — as J templates, and the byte-store lemmas. -/
import Nano.Run.NdTop2
namespace CallProbe

theorem g255 (j : Nat) : (255#64).getLsbD j = decide (j < 8) := by
  rw [BitVec.getLsbD_ofNat, show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.testBit_two_pow_sub_one]
  by_cases h : j < 8 <;> simp [h] <;> omega

theorem byte_get (x : UInt64) (k : Nat) (hk : k < 8) (y : UInt64) :
    ((((x &&& ~~~((255 : UInt64) <<< (8 * k).toUInt64)) ||| ((y &&& 255) <<< (8 * k).toUInt64)) >>> (8 * k).toUInt64) &&& 255)
      = y &&& 255 := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, g255]
  have e : 8 * k % 64 = 8 * k := by omega
  rw [e]
  by_cases h : i < 8
  · simp [h, show 8 * k + i < 64 by omega, show ¬ 8 * k + i < 8 * k by omega]
  · simp [h]

theorem byte_other (x : UInt64) (k k' : Nat) (hk : k < 8) (hk' : k' < 8) (hne : k ≠ k') (y : UInt64) :
    ((((x &&& ~~~((255 : UInt64) <<< (8 * k).toUInt64)) ||| ((y &&& 255) <<< (8 * k).toUInt64)) >>> (8 * k').toUInt64) &&& 255)
      = (x >>> (8 * k').toUInt64) &&& 255 := by
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, g255]
  have e : 8 * k % 64 = 8 * k := by omega
  have e' : 8 * k' % 64 = 8 * k' := by omega
  rw [e, e']
  by_cases h : i < 8
  · by_cases h2 : 8 * k' + i < 8 * k
    · simp [h, h2, show 8 * k' + i < 64 by omega]
    · have h3 : ¬ 8 * k' + i - 8 * k < 8 := by omega
      simp [h, h2, h3, show 8 * k' + i < 64 by omega]
  · simp [h]

/-- a byte store is read back -/
theorem lbm_sbm_same (m : Nat → UInt64) (a : Nat) (v : UInt64) : lbm (sbm m a v) a = v &&& 255 := by
  unfold lbm sbm; simp only [if_true]
  exact byte_get _ (a % 8) (Nat.mod_lt _ (by decide)) v

/-- and leaves every other byte -/
theorem lbm_sbm_other (m : Nat → UInt64) (a a' : Nat) (v : UInt64) (h : a' ≠ a) : lbm (sbm m a v) a' = lbm m a' := by
  unfold lbm sbm
  by_cases hc : a' - a' % 8 = a - a % 8
  · rw [if_pos hc, hc]
    exact byte_other _ (a % 8) (a' % 8) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (by omega) v
  · rw [if_neg hc]

/-- and every other word cell -/
theorem sbm_other (m : Nat → UInt64) (a c : Nat) (v : UInt64) (h : c ≠ a - a % 8) : sbm m a v c = m c := by
  unfold sbm; rw [if_neg h]

end CallProbe

namespace Templates
open CallProbe C GenRef

/-- the start code at word S (main at word w): set-up, call, copy loop, exit -/
def startJ (S w : Nat) : List J :=
  [.addi 30 12 16, .srli 31 2 3, .slli 31 31 3, .bgeu 31 30 4, .addi 10 0 (-1), .addi 11 0 0, .jalr 0 1,
   .sd 1 12 0, .sd 8 12 8, .addi 28 10 0, .addi 29 11 0, .jal 1 ((w : Int) - ((S + 11 : Nat) : Int)),
   .ld 5 31 0, .ld 7 5 0, .bne 7 0 4, .addi 10 0 1, .addi 11 0 0, .jal 0 12,
   .addi 11 7 0, .addi 6 5 16, .addi 14 13 0,
   .beq 7 0 7, .ld 15 6 0, .sb 15 14 0, .addi 6 6 8, .addi 14 14 1, .addi 7 7 (-1), .jal 0 (-6),
   .addi 10 0 0, .ld 1 12 0, .ld 8 12 8, .jalr 0 1]

/-- the stubs (word 0 = the jump to the start code at word S) -/
def stubJ (S : Nat) : List J :=
  [.jal 0 (S : Int), .addi 10 0 (-1), .addi 11 0 0, .ld 1 12 0, .ld 8 12 8, .jalr 0 1,
   .addi 10 0 (-2), .addi 11 0 0, .ld 1 12 0, .ld 8 12 8, .jalr 0 1]

theorem startJ_len (S w : Nat) : (startJ S w).length = 32 := rfl

theorem stH_exact (o : Buf) : stH o = o ++ ((startJ o.length 0).take 11).map encG := by
  have i0 : iu 0 = 0 := by decide
  have i16 : iu 16 = 16 := by decide
  have im : iu (-1) = g_901 := by decide
  have i8 : iu 8 = 8 := by decide
  have i44 : iu (4 * 4) = 16 := by decide
  simp [stH, startJ, encG, bpush, i0, i16, im, i8, i44]

/-- every Gen jump word is a J jal (no range condition at the word level) -/
theorem g13_any (rd a b : UInt64) : g13 rd a b = encG (.jal rd.toNat ((b.toNat : Int) - (a.toNat : Int))) := by
  unfold g13; simp only [encG]
  rw [Fixup.off_eq, iu_ofInt]; simp [Nat.toUInt64]

theorem startW_exact (o : Buf) (w : UInt64) (ho : o.length + 32 < 2 ^ 32) :
    startW o w = o ++ (startJ o.length w.toNat).map encG := by
  have i0 : iu 0 = 0 := by decide
  have i16 : iu 16 = 16 := by decide
  have im : iu (-1) = g_901 := by decide
  have i8 : iu 8 = 8 := by decide
  have i44 : iu (4 * 4) = 16 := by decide
  have i47 : iu (4 * 7) = 28 := by decide
  have i1 : iu 1 = 1 := by decide
  unfold startW stT
  rw [stH_exact]
  simp only [bpush, bsize, g13_any]
  have i28 : iu 28 = 28 := by decide
  have e27 : (UInt64.ofNat o.length + 27).toNat = o.length + 27 := by
    rw [UInt64.toNat_add]; simp; omega
  have e21 : (UInt64.ofNat o.length + 27 - 6).toNat = o.length + 21 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, e27]; simp), e27]; simp
  simp [startJ, encG, i0, i16, im, i8, i1, i28, Nat.toUInt64, e21]
  refine ⟨?_, ?_, ?_⟩ <;> congr 2 <;> omega

theorem g34_len : (g34 bnew).length = 11 := by simp [g34, bpush, bnew]

theorem stubs_exact (r : Buf) (hr : r.length + 11 < 2 ^ 32) :
    bset (g34 bnew ++ r) 0 (g13 0 0 (bsize (g34 bnew ++ r))) = (stubJ (11 + r.length)).map encG ++ r := by
  have im : iu (-1) = g_901 := by decide
  have im2 : iu (-2) = g_902 := by decide
  have i0 : iu 0 = 0 := by decide
  have i8 : iu 8 = 8 := by decide
  rw [g13_any]
  simp [g34, bpush, bnew, bset, bsize, stubJ, encG, im, im2, i0, i8, Nat.toUInt64]
  congr 2; omega

end Templates
