/- The `A64Sem` fields on `armDM`, one per instruction form, from the `dm_*` lemmas. Premises as `A64Sem`'s plus the
DeepMind permissions: `XAt` (the 4 bytes at the pc are executable) and, for loads/stores, the accessed bytes
readable/writable (DeepMind enforces W^X; see NOTES). -/
import Blocks.ArmDM
import Blocks.KAlu
import Blocks.KBr
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Proven.Apc.Blocks
open Proven.Top Proven.Arm

theorem regv (t : Arm64.State) {r : Nat} (hr : r < 31) : (obsDM t).register r = UInt64.ofBitVec ((abs t).x r) := by
  simp [obsDM, hr]

theorem goes_set {t : Arm64.State} {d : Nat} {V : BitVec 64} {U : UInt64} (hd : d < 31)
    (h : ∃ t', Arm64.Step Pg t t' ∧ abs t' = (abs t).setX d V ∧ Post t t' (t.pc + 4) t.mem) (hU : UInt64.ofBitVec V = U) :
    JT.Goes armDM t (JT.setReg (obsDM t) d U) := by
  obtain ⟨t', s1, a1, P1⟩ := h
  exact goes1 ⟨t', s1, P1.run, by rw [obs_setX hd a1 P1.pc P1.mem P1.sp, hU]⟩

abbrev O (t : Arm64.State) := armDM.observe t

theorem F_movk (t : Arm64.State) (d i h : Nat) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : XAt t)
    (hd : d < 31) (hi : i < 2 ^ 16) (hh : h < 4)
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.movk d i h)) :
    JT.Goes armDM t (JT.setReg (O t) d (JT.movkV ((O t).register d) i h)) := by
  have hA := fetch hc hp hw hx; simp only [ArmEnc.movk] at hA
  have := dm_movk (by mask32) (by fldt) hA
  rw [show ((wd (0xF2800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)).extractLsb' 0 5).toNat = d by fldt,
    show ((wd (0xF2800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)).extractLsb' 21 2).toNat = h by fldt,
    show ((wd (0xF2800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)).extractLsb' 5 16).setWidth 64 = BitVec.ofNat 64 i by immt]
    at this
  refine goes_set hd this ?_
  show _ = JT.movkV ((obsDM t).register d) i h
  rw [regv t hd]; apply UInt64.toBitVec_inj.mp
  simp [JT.movkV, UInt64.toBitVec_shiftLeft, Nat.mul_comm, BitVec.and_comm, show h * 16 % 64 = h * 16 by omega]; rfl

theorem F_addi (t : Arm64.State) (d n i : Nat) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : XAt t)
    (hd : d < 31) (hn : n < 31) (hi : i < 4096)
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.addi d n i)) :
    JT.Goes armDM t (JT.setReg (O t) d ((O t).register n + UInt64.ofNat i)) := by
  have hA := fetch hc hp hw hx; simp only [ArmEnc.addi] at hA
  have := dm_addi (by mask32) (by fldt) (by fldt) hA
  rw [show ((wd (0x91000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 0 5).toNat = d by fldt,
    show ((wd (0x91000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 5 5).toNat = n by fldt,
    show ((wd (0x91000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 10 12).setWidth 64 = BitVec.ofNat 64 i by immt] at this
  refine goes_set hd this ?_
  show _ = (obsDM t).register n + _
  rw [regv t hn]; rfl

theorem F_subi (t : Arm64.State) (d n i : Nat) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : XAt t)
    (hd : d < 31) (hn : n < 31) (hi : i < 4096)
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.subi d n i)) :
    JT.Goes armDM t (JT.setReg (O t) d ((O t).register n - UInt64.ofNat i)) := by
  have hA := fetch hc hp hw hx; simp only [ArmEnc.subi] at hA
  have := dm_subi (by mask32) (by fldt) (by fldt) hA
  rw [show ((wd (0xD1000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 0 5).toNat = d by fldt,
    show ((wd (0xD1000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 5 5).toNat = n by fldt,
    show ((wd (0xD1000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 10 12).setWidth 64 = BitVec.ofNat 64 i by immt] at this
  refine goes_set hd this ?_
  show _ = (obsDM t).register n - _
  rw [regv t hn]; rfl

theorem F_alu (t : Arm64.State) (op d n m : Nat) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : XAt t)
    (h1 : 1 ≤ op) (h2 : op ≤ 8) (hd : d < 31) (hn : n < 31) (hm : m < 31)
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.rr (ArmEnc.aluC op) d n m)) :
    JT.Goes armDM t (JT.setReg (O t) d (JT.aluV op ((O t).register n) ((O t).register m) ((O t).register 17))) := by
  have hA := fetch hc hp hw hx
  show JT.Goes armDM t (JT.setReg (obsDM t) d (JT.aluV op ((obsDM t).register n) ((obsDM t).register m)
    ((obsDM t).register 17)))
  rw [regv t hn, regv t hm, regv t (by decide : 17 < 31)]
  rcases (show op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 ∨ op = 6 ∨ op = 7 ∨ op = 8 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [ArmEnc.aluC] at hA
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0x8B000000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega)
    simp only [ArmEnc.rr, ArmBlock.rr] at hA ed en em
    have := dm_addR (by mask32) (by omega) (by omega) (by omega) hA
    rw [ed, en, em] at this
    refine goes_set hd this ?_
    apply UInt64.toBitVec_inj.mp; simp [JT.aluV, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight]
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0xCB000000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega)
    simp only [ArmEnc.rr, ArmBlock.rr] at hA ed en em
    have := dm_subR (by mask32) (by omega) (by omega) (by omega) hA
    rw [ed, en, em] at this
    refine goes_set hd this ?_
    apply UInt64.toBitVec_inj.mp; simp [JT.aluV, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight]
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0x9B004400) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega)
    simp only [ArmEnc.rr, ArmBlock.rr] at hA ed en em
    have ea : (fa (wd (0x9B004400 + m * 2 ^ 16 + n * 2 ^ 5 + d))).toNat = 17 := by fldt
    have := dm_madd (by mask32) (by omega) (by omega) (by omega) (by omega) hA
    rw [ed, en, em, ea] at this
    refine goes_set hd this ?_
    apply UInt64.toBitVec_inj.mp; simp [JT.aluV, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight]
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0x8A000000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega)
    simp only [ArmEnc.rr, ArmBlock.rr] at hA ed en em
    have := dm_andR (by mask32) (by omega) (by omega) (by omega) hA
    rw [ed, en, em] at this
    refine goes_set hd this ?_
    apply UInt64.toBitVec_inj.mp; simp [JT.aluV, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight]
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0xAA000000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega)
    simp only [ArmEnc.rr, ArmBlock.rr] at hA ed en em
    have := dm_orrR (by mask32) (by omega) (by omega) (by omega) hA
    rw [ed, en, em] at this
    refine goes_set hd this ?_
    apply UInt64.toBitVec_inj.mp; simp [JT.aluV, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight]
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0x9AC02000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega)
    simp only [ArmEnc.rr, ArmBlock.rr] at hA ed en em
    have := dm_lslv (by mask32) (by omega) (by omega) (by omega) hA
    rw [ed, en, em] at this
    refine goes_set hd this ?_
    apply UInt64.toBitVec_inj.mp; simp [JT.aluV, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight]
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0x9AC02400) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega)
    simp only [ArmEnc.rr, ArmBlock.rr] at hA ed en em
    have := dm_lsrv (by mask32) (by omega) (by omega) (by omega) hA
    rw [ed, en, em] at this
    refine goes_set hd this ?_
    apply UInt64.toBitVec_inj.mp; simp [JT.aluV, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight]
  · obtain ⟨ed, en, em⟩ := rr_f (c := 0xCA000000) (d := d) (n := n) (m := m) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) (by omega)
    simp only [ArmEnc.rr, ArmBlock.rr] at hA ed en em
    have := dm_eorR (by mask32) (by omega) (by omega) (by omega) hA
    rw [ed, en, em] at this
    refine goes_set hd this ?_
    apply UInt64.toBitVec_inj.mp; simp [JT.aluV, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight]

theorem ofInt_toNat (f : Int) : (UInt64.ofInt f).toNat = (f % 2 ^ 64).toNat := by
  unfold UInt64.ofInt
  rw [UInt64.toNat_ofNat']
  have h0 := Int.emod_nonneg f (show (2 ^ 64 : Int) ≠ 0 by decide)
  have h1 := Int.emod_lt_of_pos f (show (0 : Int) < 2 ^ 64 by decide)
  omega

/-- the branch offset field, as `A64Sem` writes it -/
theorem offW (w : Nat) (hw1 : 2 ≤ w) (hw2 : w ≤ 26) (f : Int) (hm : ArmEnc.mo f w = if 0 ≤ f then f.toNat else 2 ^ w - f.natAbs)
    (h1 : -2 ^ (w - 1) ≤ f) (h2 : f < 2 ^ (w - 1)) :
    (BitVec.ofNat w (ArmEnc.mo f w)).signExtend 64 <<< 2 = (4 * UInt64.ofInt f).toBitVec := by
  have p1 : (2 : Int) ^ (w - 1) = ((2 ^ (w - 1) : Nat) : Int) := by push_cast; rfl
  have p2 : 2 ^ (w - 1) ≤ 2 ^ 25 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [hm]; split
  · rename_i h0
    rw [off_fwd (w := w) (by omega) (by omega) (show f.toNat < 2 ^ (w - 1) by omega)]
    apply BitVec.eq_of_toNat_eq; simp [UInt64.toNat_mul, ofInt_toNat]; omega
  · rename_i h0
    have hp : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    rw [off_back (w := w) (by omega) (by omega) (show 0 < f.natAbs by omega) (show f.natAbs ≤ 2 ^ (w - 1) by omega)]
    apply BitVec.eq_of_toNat_eq; simp [UInt64.toNat_mul, ofInt_toNat]; omega

theorem off19 (f : Int) (h1 : -2 ^ 18 ≤ f) (h2 : f < 2 ^ 18) :
    (BitVec.ofNat 19 (ArmEnc.mo f 19)).signExtend 64 <<< 2 = (4 * UInt64.ofInt f).toBitVec :=
  offW 19 (by decide) (by decide) f (by unfold ArmEnc.mo; split <;> simp only [Nat.reducePow] <;> omega) h1 h2
theorem off26 (f : Int) (h1 : -2 ^ 25 ≤ f) (h2 : f < 2 ^ 25) :
    (BitVec.ofNat 26 (ArmEnc.mo f 26)).signExtend 64 <<< 2 = (4 * UInt64.ofInt f).toBitVec :=
  offW 26 (by decide) (by decide) f (by unfold ArmEnc.mo; split <;> simp only [Nat.reducePow] <;> omega) h1 h2

/-- observation after a step that writes `x[d] := v` (flags free) and moves the pc to `p` -/
theorem obs_gen {t t' : Arm64.State} {d : Nat} {v p : BitVec 64} (hd : d < 31)
    (ha : (abs t').x = ((abs t).setX d v).x) (hpc : t'.pc = p) (hm : t'.mem = t.mem) (hsp : t'.sp = t.sp) :
    obsDM t' = ⟨UInt64.ofBitVec p, fun r => if r = d then UInt64.ofBitVec v else (obsDM t).register r,
      (obsDM t).memory⟩ := by
  simp only [obsDM, ha, hpc, hm, hsp]
  congr 1
  funext r
  by_cases e : r = d
  · subst e; simp [hd, AState.setX, show r ≠ 31 by omega]
  · simp only [e, ite_false]; split
    · rename_i hr; simp [AState.setX, e, show d ≠ 31 by omega]
    · rfl

/-- a fetch at a later state with the same memory, at `pc + 4·j` -/
theorem fetch' {t t1 : Arm64.State} {w : Nat} (hc : t1.status = .Running) (hm : t1.mem = t.mem)
    (hp : JT.PcOK armDM (obsDM t1)) (hw : JT.WordAt (obsDM t) (obsDM t1).programCounter.toNat w)
    (hx : ∀ k < 4, t.mem.canExec (ad (t1.pc.toNat + k)) 1 = true) : At t1 (wd w) :=
  fetch hc hp (by simpa [JT.WordAt, obsDM, hm] using hw) (by rw [hm]; exact hx)

theorem jc_condV (c : Nat) (hc : c < 4) (x y : UInt64) : jc c x y = JT.condV c x y := by
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem F_cmpbr (t : Arm64.State) (c n m : Nat) (f : Int) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t))
    (hx : ∀ k < 8, t.mem.canExec (ad (t.pc.toNat + k)) 1 = true) (hc4 : c < 4) (hn : n < 31) (hm : m < 31)
    (hf1 : -2 ^ 18 ≤ f) (hf2 : f < 2 ^ 18) (h8 : (O t).programCounter.toNat + 8 ≤ armDM.ramEnd)
    (hw0 : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.subsR n m))
    (hw1 : JT.WordAt (O t) ((O t).programCounter.toNat + 4) (ArmEnc.bc c f)) :
    JT.Goes armDM t ⟨if JT.condV c ((O t).register n) ((O t).register m)
        then (O t).programCounter + 4 + 4 * UInt64.ofInt f else (O t).programCounter + 8,
      fun r => if r = 16 then (O t).register n - (O t).register m else (O t).register r, (O t).memory⟩ := by
  have hA := fetch hc hp hw0 (fun k hk => hx k (by omega)); simp only [ArmEnc.subsR] at hA
  obtain ⟨ed, en, em⟩ := rr_f (c := 0xEB000000) (d := 16) (n := n) (m := m) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)
  have h0 := dm_subsR (w := wd (0xEB000000 + m * 2 ^ 16 + n * 2 ^ 5 + 16)) (by mask32) (by omega) (by omega)
    (by omega) hA
  rw [ed, en, em] at h0
  obtain ⟨t1, s1, a1, P1⟩ := h0
  obtain ⟨p4, plo, phi⟩ : t.pc.toNat % 4 = 0 ∧ 2 ^ 31 ≤ t.pc.toNat ∧ t.pc.toNat + 4 ≤ 3 * 2 ^ 30 := by
    have := hp; simp only [JT.PcOK, O, armDM, pc_obs] at this; exact this
  have h8' : t.pc.toNat + 8 ≤ 3 * 2 ^ 30 := by
    have := h8; simp only [O, armDM, pc_obs] at this; exact this
  have pc1 : t1.pc.toNat = t.pc.toNat + 4 := by rw [P1.pc]; simp; omega
  have hp1 : JT.PcOK armDM (obsDM t1) := by
    simp only [JT.PcOK, armDM, pc_obs, pc1]; omega
  have hw1' : JT.WordAt (obsDM t) (obsDM t1).programCounter.toNat (ArmEnc.bc c f) := by
    rw [pc_obs, pc1]; have := hw1; simp only [O, armDM, pc_obs] at this; exact this
  have hA1 := fetch' P1.run P1.mem hp1 hw1' (fun k hk => by rw [pc1, Nat.add_assoc]; exact hx (4 + k) (by omega))
  simp only [ArmEnc.bc] at hA1
  have hmo : ArmEnc.mo f 19 < 2 ^ 19 := mo_lt f 19
  obtain ⟨t2, s2, a2, P2⟩ := dm_bc (by mask32) hA1
  rw [show (wd (0x54000000 + ArmEnc.mo f 19 * 2 ^ 5 + c)).extractLsb' 0 4 = BitVec.ofNat 4 c by
      apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega,
    show (wd (0x54000000 + ArmEnc.mo f 19 * 2 ^ 5 + c)).extractLsb' 5 19 = BitVec.ofNat 19 (ArmEnc.mo f 19) by
      apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega, off19 f hf1 hf2, a1,
    show (abs t).x n = (UInt64.ofBitVec ((abs t).x n)).toBitVec from rfl,
    show (abs t).x m = (UInt64.ofBitVec ((abs t).x m)).toBitVec from rfl, cond_sub _ c hc4, jc_condV c hc4] at P2
  have r2 : (abs t2).x = ((abs t).setX 16 ((abs t).x n - (abs t).x m)).x := by rw [a2, a1]; rfl
  refine ⟨t2, runs_trans (runs_one s1 P1.run) (runs_one s2 P2.run), P2.run, ?_⟩
  show obsDM t2 = _
  rw [obs_gen (by decide) r2 P2.pc (P2.mem.trans P1.mem) (P2.sp.trans P1.sp)]
  have en' : (O t).register n = UInt64.ofBitVec ((abs t).x n) := regv t hn
  have em' : (O t).register m = UInt64.ofBitVec ((abs t).x m) := regv t hm
  rw [en', em']
  congr 1
  · by_cases hcv : JT.condV c (UInt64.ofBitVec ((abs t).x n)) (UInt64.ofBitVec ((abs t).x m)) = true
    · simp only [hcv, ite_true]; apply UInt64.toBitVec_inj.mp; simp [P1.pc, O, armDM, obsDM, BitVec.add_assoc]
    · simp only [hcv, ite_false, Bool.false_eq_true]; apply UInt64.toBitVec_inj.mp
      simp [P1.pc, O, armDM, obsDM, BitVec.add_assoc]

theorem F_cbz (t : Arm64.State) (r : Nat) (f : Int) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : XAt t)
    (hr : r < 31) (hf1 : -2 ^ 18 ≤ f) (hf2 : f < 2 ^ 18)
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.cbz r f)) :
    JT.Goes armDM t (JT.jumpTo (O t) (if (O t).register r = 0
      then (O t).programCounter + 4 * UInt64.ofInt f else (O t).programCounter + 4)) := by
  have hA := fetch hc hp hw hx; simp only [ArmEnc.cbz] at hA
  have hmo : ArmEnc.mo f 19 < 2 ^ 19 := mo_lt f 19
  obtain ⟨t1, s1, a1, P1⟩ := dm_cbz (by mask32) (by fldt) hA
  rw [show (wd (0xB4000000 + ArmEnc.mo f 19 * 2 ^ 5 + r)).extractLsb' 5 19 = BitVec.ofNat 19 (ArmEnc.mo f 19) by
      apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega,
    show ((wd (0xB4000000 + ArmEnc.mo f 19 * 2 ^ 5 + r)).extractLsb' 0 5).toNat = r by fldt, off19 f hf1 hf2] at P1
  refine goes1 ⟨t1, s1, P1.run, ?_⟩
  rw [obs_jump a1 P1.pc P1.mem P1.sp]
  have er : (O t).register r = UInt64.ofBitVec ((abs t).x r) := regv t hr
  rw [er]
  by_cases hz : (abs t).x r = 0
  · have : UInt64.ofBitVec ((abs t).x r) = 0 := by rw [hz]; rfl
    simp only [hz, ite_true, this]; rfl
  · have : ¬ UInt64.ofBitVec ((abs t).x r) = 0 := fun h => hz (by rw [← UInt64.toBitVec_ofBitVec ((abs t).x r), h]; rfl)
    simp only [hz, ite_false, this]; rfl

theorem F_b (t : Arm64.State) (f : Int) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : XAt t)
    (hf1 : -2 ^ 25 ≤ f) (hf2 : f < 2 ^ 25) (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.bB f)) :
    JT.Goes armDM t (JT.jumpTo (O t) ((O t).programCounter + 4 * UInt64.ofInt f)) := by
  have hA := fetch hc hp hw hx; simp only [ArmEnc.bB] at hA
  have hmo : ArmEnc.mo f 26 < 2 ^ 26 := mo_lt f 26
  obtain ⟨t1, s1, a1, P1⟩ := dm_b (by mask32) hA
  rw [show (wd (0x14000000 + ArmEnc.mo f 26)).extractLsb' 0 26 = BitVec.ofNat 26 (ArmEnc.mo f 26) by
    apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega, off26 f hf1 hf2] at P1
  exact goes1 ⟨t1, s1, P1.run, by rw [obs_jump a1 P1.pc P1.mem P1.sp]; rfl⟩

theorem F_bl (t : Arm64.State) (f : Int) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : XAt t)
    (hf1 : -2 ^ 25 ≤ f) (hf2 : f < 2 ^ 25) (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.blB f)) :
    JT.Goes armDM t ⟨(O t).programCounter + 4 * UInt64.ofInt f,
      fun r => if r = 30 then (O t).programCounter + 4 else (O t).register r, (O t).memory⟩ := by
  have hA := fetch hc hp hw hx; simp only [ArmEnc.blB] at hA
  have hmo : ArmEnc.mo f 26 < 2 ^ 26 := mo_lt f 26
  obtain ⟨t1, s1, a1, P1⟩ := dm_bl (by mask32) hA
  rw [show (wd (0x94000000 + ArmEnc.mo f 26)).extractLsb' 0 26 = BitVec.ofNat 26 (ArmEnc.mo f 26) by
    apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega, off26 f hf1 hf2] at P1
  exact goes1 ⟨t1, s1, P1.run, by rw [obs_gen (d := 30) (by decide) (by rw [a1]) P1.pc P1.mem P1.sp]; rfl⟩

theorem F_br (t : Arm64.State) (n : Nat) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : XAt t)
    (hn : n < 31) (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.brR n)) :
    JT.Goes armDM t (JT.jumpTo (O t) ((O t).register n)) := by
  have hA := fetch hc hp hw hx; simp only [ArmEnc.brR] at hA
  obtain ⟨t1, s1, a1, P1⟩ := dm_br (by mask32) (by fldt) hA
  rw [show ((wd (0xD61F0000 + n * 2 ^ 5)).extractLsb' 5 5).toNat = n by fldt] at P1
  exact goes1 ⟨t1, s1, P1.run, by rw [obs_jump a1 P1.pc P1.mem P1.sp, show (O t).register n = _ from regv t hn]; rfl⟩

end Proven.Apc.Blocks
