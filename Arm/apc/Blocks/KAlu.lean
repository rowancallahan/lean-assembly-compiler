/- J `alu op rd a b` (op 1..8: add sub mul and or sll srl xor) on DeepMind's machine. Block: `[movz x17, #0]` (when an
operand is x0, or op = mul) then the 3-register word (`madd d, a, b, x17` for mul), then PADs. -/
import Blocks.KAddi
import Blocks.Reg
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Proven.Apc.Blocks
open CallProbe Proven.Arm ArmBlock

theorem rr_f {c d n m : Nat} (hc : c < 2 ^ 32) (h0 : c % 32 = 0) (h1 : c / 32 % 32 = 0) (h2 : c / 65536 % 32 = 0)
    (hd : d < 32) (hn : n < 32) (hm : m < 32) :
    (fd (wd (c + m * 2 ^ 16 + n * 2 ^ 5 + d))).toNat = d ∧ (fn (wd (c + m * 2 ^ 16 + n * 2 ^ 5 + d))).toNat = n ∧
    (fm (wd (c + m * 2 ^ 16 + n * 2 ^ 5 + d))).toNat = m := by
  refine ⟨by fldt, by fldt, by fldt⟩

/-- the ALU word, from any state whose operand registers hold J's operands (and x17 = 0 for mul) -/
theorem alu_word {op d n m : Nat} {x y : UInt64} {t : Arm64.State} (hop : 1 ≤ op ∧ op ≤ 8) (hd : d < 31) (hn : n < 31)
    (hm : m < 31) (hx : (abs t).x n = x.toBitVec) (hy : (abs t).x m = y.toBitVec) (h17 : op = 3 → (abs t).x 17 = 0)
    (hA : At t (wd (rr (aluC op) d n m))) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = (abs t).setX d (aluf op x y).toBitVec ∧ Post t t' (t.pc + 4) t.mem := by
  rcases (show op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 ∨ op = 6 ∨ op = 7 ∨ op = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [aluC] at hA
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0x8B000000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega)
    simp only [rr] at hA ed en em
    have := dm_addR (by mask32) (by omega) (by omega) (by omega) hA
    rw [ed, en, em, hx, hy] at this; simpa [aluf] using this
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0xCB000000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega)
    simp only [rr] at hA ed en em
    have := dm_subR (by mask32) (by omega) (by omega) (by omega) hA
    rw [ed, en, em, hx, hy] at this; simpa [aluf] using this
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0x9B004400) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega)
    simp only [rr] at hA ed en em
    have ea : (fa (wd (0x9B004400 + m * 2 ^ 16 + n * 2 ^ 5 + d))).toNat = 17 := by fldt
    have := dm_madd (by mask32) (by omega) (by omega) (by omega) (by omega) hA
    rw [ed, en, em, ea, hx, hy, h17 rfl] at this; simpa [aluf] using this
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0x8A000000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega)
    simp only [rr] at hA ed en em
    have := dm_andR (by mask32) (by omega) (by omega) (by omega) hA
    rw [ed, en, em, hx, hy] at this; simpa [aluf] using this
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0xAA000000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega)
    simp only [rr] at hA ed en em
    have := dm_orrR (by mask32) (by omega) (by omega) (by omega) hA
    rw [ed, en, em, hx, hy] at this; simpa [aluf] using this
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0x9AC02000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega)
    simp only [rr] at hA ed en em
    have := dm_lslv (by mask32) (by omega) (by omega) (by omega) hA
    rw [ed, en, em, hx, hy] at this; simpa [aluf] using this
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0x9AC02400) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega)
    simp only [rr] at hA ed en em
    have := dm_lsrv (by mask32) (by omega) (by omega) (by omega) hA
    rw [ed, en, em, hx, hy] at this; simpa [aluf] using this
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0xCA000000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega)
    simp only [rr] at hA ed en em
    have := dm_eorR (by mask32) (by omega) (by omega) (by omega) hA
    rw [ed, en, em, hx, hy] at this; simpa [aluf] using this

theorem pads2 {j : J} {w0 w1 : Nat} (h : blockJ j = [w0, w1, PAD, PAD]) : PadsFrom j 2 := by
  intro k h1 h2; rw [bw_of h]
  rcases (show k = 2 ∨ k = 3 by omega) with rfl | rfl <;> rfl

theorem setX_ne (a : AState) {d i : Nat} (h : i ≠ d) (v : BitVec 64) : (a.setX d v).x i = a.x i := by
  unfold AState.setX; split <;> simp [h]
theorem setX_eq (a : AState) {d : Nat} (h : d ≠ 31) (v : BitVec 64) : (a.setX d v).x d = v := by
  unfold AState.setX; simp [h]

/-- an operand after `movz x17, #0`: x0 reads x17 -/
theorem opv {a : AState} {s : St} {K} (h : RegsOK a s K) (hz : s.x 0 = 0) {r : Nat} (hr : rdOK r) :
    (a.setX 17 0).x (opR r) = (s.x r).toBitVec := by
  unfold opR; split
  · subst r; rw [setX_eq _ (by decide), hz]; rfl
  · rename_i h0; have hl := live_of_rd hr h0
    rw [setX_ne _ (pi_rng hl).2.1, h.1 r hl]

theorem opR_lt {r : Nat} (hr : rdOK r) : opR r < 31 := by
  unfold opR; split
  · decide
  · rename_i h0; exact (live_of_rd hr h0).1

theorem blk_alu {C : List J} {D K} {pc : Nat} {s : St} {t : Arm64.State} {op rd a b : Nat}
    (hj : C[pc]? = some (.alu op rd a b)) (hv : validJ C.length pc (.alu op rd a b)) (hR : RelD C D K (pc, s) t) :
    Reach t (RelD C D K (pc + 1, wr s rd (aluf op (s.x a) (s.x b)))) := by
  obtain ⟨hop1, hop2, hra, hrb, hrd⟩ := hv
  have hm := hR.mid hj
  have hz : s.x 0 = 0 := hR.zero
  by_cases h0 : rd = 0
  · subst h0
    have hb : blockJ (.alu op 0 a b) = [PAD, PAD, PAD, PAD] := by simp [blockJ, body, pad4]
    refine (pads 4 0 rfl hm (pads4 hb)).mono fun t' ⟨m', a', p', q'⟩ => ?_
    simp only [wr, ite_true]
    exact relD_next hR m' (a' ▸ hR.regs) p' (q' ▸ hR.mem) rfl hR.zero rfl
  have hl := live_of_wr hrd h0
  have fin : ∀ {t' : Arm64.State} {A : AState}, Mid C s.b pc (.alu op rd a b) 4 t' → RegsOK A s K →
      abs t' = A.setX (pi rd) (aluf op (s.x a) (s.x b)).toBitVec → t'.sp = t.sp → t'.mem = t.mem →
      RelD C D K (pc + 1, wr s rd (aluf op (s.x a) (s.x b))) t' := by
    intro t' A m' hA a' p' q'
    refine relD_next hR m' (a' ▸ regs_wr hA hl _) p' (q' ▸ ?_) ?_ ?_ ?_
    all_goals simp [wr, h0, upd, hz, hR.mem, Ne.symm h0]
  have hal := opR_lt hra; have hbl := opR_lt hrb
  by_cases hZ : a = 0 ∨ b = 0 ∨ op = 3
  · have hb : blockJ (.alu op rd a b) = [movz 17 0, rr (aluC op) (pi rd) (opR a) (opR b), PAD, PAD] := by
      simp [blockJ, body, pad4, h0, zpre, hZ]
    have hA0 := hm.at (by omega); rw [bw_of hb] at hA0; simp only [List.getD_cons_zero, movz] at hA0
    have h1 := dm_movz (by decide) (by decide) hA0
    rw [show ((wd (0xD2800000 + 0 * 2 ^ 5 + 17)).extractLsb' 0 5).toNat = 17 by decide,
      show ((wd (0xD2800000 + 0 * 2 ^ 5 + 17)).extractLsb' 21 2).toNat = 0 by decide,
      show ((wd (0xD2800000 + 0 * 2 ^ 5 + 17)).extractLsb' 5 16).setWidth 64 = 0 by decide] at h1
    obtain ⟨t1, s1, m1, a1, p1, q1⟩ := seq1 hm (by omega) h1
    replace a1 : abs t1 = (abs t).setX 17 0 := by rw [a1]; rfl
    refine Reach.cons s1 ((word_pads (A := ((abs t).setX 17 0).setX (pi rd) (aluf op (s.x a) (s.x b)).toBitVec) m1
      (by omega) (fun hA => ?_) (pads2 hb)).mono fun t' ⟨m', a', p', q'⟩ => fin m' (regs_scr hR.regs (.inr rfl) 0)
        a' (p'.trans p1) (q'.trans q1))
    rw [bw_of hb] at hA; simp only [List.getD_cons_succ, List.getD_cons_zero] at hA
    have := alu_word ⟨hop1, hop2⟩ hl.1 hal hbl ((congrArg (fun z : AState => z.x (opR a)) a1).trans (opv hR.regs hz hra))
      ((congrArg (fun z : AState => z.x (opR b)) a1).trans (opv hR.regs hz hrb))
      (fun _ => by rw [a1, setX_eq _ (by decide)]) hA
    rwa [a1] at this
  · have hb : blockJ (.alu op rd a b) = [rr (aluC op) (pi rd) (pi a) (pi b), PAD, PAD, PAD] := by
      simp at hZ; simp [blockJ, body, pad4, h0, zpre, hZ, opR]
    simp at hZ
    have hla := live_of_rd hra hZ.1; have hlb := live_of_rd hrb hZ.2.1
    refine (word_pads (A := (abs t).setX (pi rd) (aluf op (s.x a) (s.x b)).toBitVec) hm (by omega) (fun hA => ?_)
      (pads3 hb)).mono fun t' ⟨m', a', p', q'⟩ => fin m' hR.regs a' p' q'
    rw [bw_of hb] at hA; simp only [List.getD_cons_zero] at hA
    exact alu_word ⟨hop1, hop2⟩ hl.1 hla.1 hlb.1 (hR.regs.1 a hla) (hR.regs.1 b hlb) (fun h => absurd h hZ.2.2) hA

end Proven.Apc.Blocks
