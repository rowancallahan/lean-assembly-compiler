/- J `addi` on DeepMind's machine. Premise beyond `validJ`: no wrap, `0 ≤ x[rs] + imm < 2^64` (J's `ea` clamps with
`Int.toNat`, A64 wraps; `JLay.SafeX` has the same premise). -/
import Blocks.Block
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Proven.Apc.Blocks
open CallProbe Proven.Arm ArmBlock

theorem pads3 {j : J} {w0 : Nat} (h : blockJ j = [w0, PAD, PAD, PAD]) : PadsFrom j 1 := by
  intro k h1 h2; rw [bw_of h]
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl <;> rfl
theorem pads4 {j : J} (h : blockJ j = [PAD, PAD, PAD, PAD]) : PadsFrom j 0 := by
  intro k h1 h2; rw [bw_of h]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem toBV_ofNat (n : Nat) : (UInt64.ofNat n).toBitVec = BitVec.ofNat 64 n := rfl

theorem blk_addi {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {rd rs : Nat} {imm : Int}
    (hj : C[pc]? = some (.addi rd rs imm)) (hv : validJ C.length pc (.addi rd rs imm))
    (hnw : 0 ≤ ((s.x rs).toNat : Int) + imm ∧ ((s.x rs).toNat : Int) + imm < 2 ^ 64) (hR : RelD C D K (pc, s) t) :
    Reach t (RelD C D K (pc + 1, wr s rd (UInt64.ofNat (ea (s.x rs) imm)))) := by
  obtain ⟨hrs, hrd, hi1, hi2⟩ := hv
  have hm := hR.mid hj
  by_cases h0 : rd = 0
  · subst h0
    have hb : blockJ (.addi 0 rs imm) = [PAD, PAD, PAD, PAD] := by simp [blockJ, body, pad4]
    refine (pads 4 0 rfl hm (pads4 hb)).mono fun t' ⟨m', a', p', q'⟩ => ?_
    simp only [wr, ite_true]
    exact relD_next hR m' (a' ▸ hR.regs) p' (q' ▸ hR.mem) rfl hR.zero rfl
  have hl := live_of_wr hrd h0
  have hd31 := hl.1
  have fin : ∀ {t' : Arm64.State} {v : BitVec 64}, Mid C s.b pc (.addi rd rs imm) 4 t' →
      abs t' = (abs t).setX (pi rd) v → v = (UInt64.ofNat (ea (s.x rs) imm)).toBitVec → t'.sp = t.sp → t'.mem = t.mem →
      RelD C D K (pc + 1, wr s rd (UInt64.ofNat (ea (s.x rs) imm))) t' := by
    intro t' v m' a' e p' q'
    refine relD_next hR m' (a' ▸ e ▸ regs_wr hR.regs hl _) p' (q' ▸ ?_) ?_ ?_ ?_
    all_goals have hz : s.x 0 = 0 := hR.zero
    all_goals simp [wr, h0, upd, hz, hR.mem, Ne.symm h0]
  by_cases hs0 : rs = 0
  · subst hs0
    have hz : s.x 0 = 0 := hR.zero
    have hpos : 0 ≤ imm := by have := hnw.1; rw [hz] at this; simpa using this
    have hb : blockJ (.addi rd 0 imm) = [movz (pi rd) imm.toNat, PAD, PAD, PAD] := by
      simp [blockJ, body, pad4, h0, show ¬ imm < 0 by omega]
    refine (one_pads (A := (abs t).setX (pi rd) (BitVec.ofNat 64 imm.toNat)) hm (fun hA => ?_) (pads3 hb)).mono
      fun t' ⟨m', a', p', q'⟩ => fin m' a' ?_ p' q'
    · rw [bw_of hb] at hA; simp only [List.getD_cons_zero, movz] at hA
      have := dm_movz (by mask32) (by fldt) hA
      rw [show ((wd (0xD2800000 + imm.toNat * 2 ^ 5 + pi rd)).extractLsb' 0 5).toNat = pi rd by fldt,
        show ((wd (0xD2800000 + imm.toNat * 2 ^ 5 + pi rd)).extractLsb' 21 2).toNat = 0 by fldt,
        show ((wd (0xD2800000 + imm.toNat * 2 ^ 5 + pi rd)).extractLsb' 5 16).setWidth 64 = BitVec.ofNat 64 imm.toNat by immt]
        at this
      simpa using this
    · simp [ea, hz]; rfl
  have hsl := live_of_rd hrs hs0
  have hs31 := hsl.1
  have hx : (abs t).x (pi rs) = (s.x rs).toBitVec := hR.regs.1 rs hsl
  have hxl := (s.x rs).toNat_lt
  by_cases hneg : imm < 0
  · have hb : blockJ (.addi rd rs imm) = [subi (pi rd) (pi rs) imm.natAbs, PAD, PAD, PAD] := by
      simp [blockJ, body, pad4, h0, hs0, hneg]
    refine (one_pads (A := (abs t).setX (pi rd) ((s.x rs).toBitVec - BitVec.ofNat 64 imm.natAbs)) hm (fun hA => ?_)
      (pads3 hb)).mono fun t' ⟨m', a', p', q'⟩ => fin m' a' ?_ p' q'
    · rw [bw_of hb] at hA; simp only [List.getD_cons_zero, subi] at hA
      have := dm_subi (by mask32) (by fldt) (by fldt) hA
      rw [show ((wd (0xD1000000 + imm.natAbs * 2 ^ 10 + pi rs * 2 ^ 5 + pi rd)).extractLsb' 0 5).toNat = pi rd by fldt,
        show ((wd (0xD1000000 + imm.natAbs * 2 ^ 10 + pi rs * 2 ^ 5 + pi rd)).extractLsb' 5 5).toNat = pi rs by fldt,
        show ((wd (0xD1000000 + imm.natAbs * 2 ^ 10 + pi rs * 2 ^ 5 + pi rd)).extractLsb' 10 12).setWidth 64 =
          BitVec.ofNat 64 imm.natAbs by immt, hx] at this
      exact this
    · apply BitVec.eq_of_toNat_eq; simp [ea, BitVec.toNat_sub]; omega
  · have hb : blockJ (.addi rd rs imm) = [ArmBlock.addi (pi rd) (pi rs) imm.toNat, PAD, PAD, PAD] := by
      simp [blockJ, body, pad4, h0, hs0, hneg]
    refine (one_pads (A := (abs t).setX (pi rd) ((s.x rs).toBitVec + BitVec.ofNat 64 imm.toNat)) hm (fun hA => ?_)
      (pads3 hb)).mono fun t' ⟨m', a', p', q'⟩ => fin m' a' ?_ p' q'
    · rw [bw_of hb] at hA; simp only [List.getD_cons_zero, ArmBlock.addi] at hA
      have := dm_addi (by mask32) (by fldt) (by fldt) hA
      rw [show ((wd (0x91000000 + imm.toNat * 2 ^ 10 + pi rs * 2 ^ 5 + pi rd)).extractLsb' 0 5).toNat = pi rd by fldt,
        show ((wd (0x91000000 + imm.toNat * 2 ^ 10 + pi rs * 2 ^ 5 + pi rd)).extractLsb' 5 5).toNat = pi rs by fldt,
        show ((wd (0x91000000 + imm.toNat * 2 ^ 10 + pi rs * 2 ^ 5 + pi rd)).extractLsb' 10 12).setWidth 64 =
          BitVec.ofNat 64 imm.toNat by immt, hx] at this
      exact this
    · apply BitVec.eq_of_toNat_eq; simp [ea, BitVec.toNat_add]; omega

end Proven.Apc.Blocks
