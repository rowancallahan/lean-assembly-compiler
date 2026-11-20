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
    JT.GoesK armDM XD WD t (JT.setReg (obsDM t) d U) := by
  obtain ⟨t', s1, a1, P1⟩ := h
  exact goes1 ⟨t', s1, P1.run, by rw [obs_setX hd a1 P1.pc P1.mem P1.sp, hU], P1.mem⟩

abbrev O (t : Arm64.State) := armDM.observe t

theorem F_movk (t : Arm64.State) (d i h : Nat) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : JT.FetchX armDM XD t 4)
    (hd : d < 31) (hi : i < 2 ^ 16) (hh : h < 4)
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.movk d i h)) :
    JT.GoesK armDM XD WD t (JT.setReg (O t) d (JT.movkV ((O t).register d) i h)) := by
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.movk] at hA
  have := dm_movk (by mask32) (by fldt) hA
  rw [show ((wd (0xF2800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)).extractLsb' 0 5).toNat = d by fldt,
    show ((wd (0xF2800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)).extractLsb' 21 2).toNat = h by fldt,
    show ((wd (0xF2800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)).extractLsb' 5 16).setWidth 64 = BitVec.ofNat 64 i by immt]
    at this
  refine goes_set hd this ?_
  show _ = JT.movkV ((obsDM t).register d) i h
  rw [regv t hd]; apply UInt64.toBitVec_inj.mp
  simp [JT.movkV, UInt64.toBitVec_shiftLeft, Nat.mul_comm, BitVec.and_comm, show h * 16 % 64 = h * 16 by omega]; rfl

theorem F_addi (t : Arm64.State) (d n i : Nat) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : JT.FetchX armDM XD t 4)
    (hd : d < 31) (hn : n < 31) (hi : i < 4096)
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.addi d n i)) :
    JT.GoesK armDM XD WD t (JT.setReg (O t) d ((O t).register n + UInt64.ofNat i)) := by
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.addi] at hA
  have := dm_addi (by mask32) (by fldt) (by fldt) hA
  rw [show ((wd (0x91000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 0 5).toNat = d by fldt,
    show ((wd (0x91000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 5 5).toNat = n by fldt,
    show ((wd (0x91000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 10 12).setWidth 64 = BitVec.ofNat 64 i by immt] at this
  refine goes_set hd this ?_
  show _ = (obsDM t).register n + _
  rw [regv t hn]; rfl

theorem F_subi (t : Arm64.State) (d n i : Nat) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : JT.FetchX armDM XD t 4)
    (hd : d < 31) (hn : n < 31) (hi : i < 4096)
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.subi d n i)) :
    JT.GoesK armDM XD WD t (JT.setReg (O t) d ((O t).register n - UInt64.ofNat i)) := by
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.subi] at hA
  have := dm_subi (by mask32) (by fldt) (by fldt) hA
  rw [show ((wd (0xD1000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 0 5).toNat = d by fldt,
    show ((wd (0xD1000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 5 5).toNat = n by fldt,
    show ((wd (0xD1000000 + i * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 10 12).setWidth 64 = BitVec.ofNat 64 i by immt] at this
  refine goes_set hd this ?_
  show _ = (obsDM t).register n - _
  rw [regv t hn]; rfl

theorem F_alu (t : Arm64.State) (op d n m : Nat) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : JT.FetchX armDM XD t 4)
    (h1 : 1 ≤ op) (h2 : op ≤ 8) (hd : d < 31) (hn : n < 31) (hm : m < 31)
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.rr (ArmEnc.aluC op) d n m)) :
    JT.GoesK armDM XD WD t (JT.setReg (O t) d (JT.aluV op ((O t).register n) ((O t).register m) ((O t).register 17))) := by
  have hA := fetch hc hp hw (xat hx)
  show JT.GoesK armDM XD WD t (JT.setReg (obsDM t) d (JT.aluV op ((obsDM t).register n) ((obsDM t).register m)
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
    (hx : JT.FetchX armDM XD t 8) (hc4 : c < 4) (hn : n < 31) (hm : m < 31)
    (hf1 : -2 ^ 18 ≤ f) (hf2 : f < 2 ^ 18) (h8 : (O t).programCounter.toNat + 8 ≤ armDM.ramEnd)
    (hw0 : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.subsR n m))
    (hw1 : JT.WordAt (O t) ((O t).programCounter.toNat + 4) (ArmEnc.bc c f)) :
    JT.GoesK armDM XD WD t ⟨if JT.condV c ((O t).register n) ((O t).register m)
        then (O t).programCounter + 4 + 4 * UInt64.ofInt f else (O t).programCounter + 8,
      fun r => if r = 16 then (O t).register n - (O t).register m else (O t).register r, (O t).memory⟩ := by
  have hx := xat hx
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
  refine ⟨t2, runs_trans (runs_one s1 P1.run) (runs_one s2 P2.run), P2.run, ?_, keep_of_mem (P2.mem.trans P1.mem)⟩
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

theorem F_cbz (t : Arm64.State) (r : Nat) (f : Int) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : JT.FetchX armDM XD t 4)
    (hr : r < 31) (hf1 : -2 ^ 18 ≤ f) (hf2 : f < 2 ^ 18)
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.cbz r f)) :
    JT.GoesK armDM XD WD t (JT.jumpTo (O t) (if (O t).register r = 0
      then (O t).programCounter + 4 * UInt64.ofInt f else (O t).programCounter + 4)) := by
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.cbz] at hA
  have hmo : ArmEnc.mo f 19 < 2 ^ 19 := mo_lt f 19
  obtain ⟨t1, s1, a1, P1⟩ := dm_cbz (by mask32) (by fldt) hA
  rw [show (wd (0xB4000000 + ArmEnc.mo f 19 * 2 ^ 5 + r)).extractLsb' 5 19 = BitVec.ofNat 19 (ArmEnc.mo f 19) by
      apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega,
    show ((wd (0xB4000000 + ArmEnc.mo f 19 * 2 ^ 5 + r)).extractLsb' 0 5).toNat = r by fldt, off19 f hf1 hf2] at P1
  refine goes1 ⟨t1, s1, P1.run, ?_, P1.mem⟩
  rw [obs_jump a1 P1.pc P1.mem P1.sp]
  have er : (O t).register r = UInt64.ofBitVec ((abs t).x r) := regv t hr
  rw [er]
  by_cases hz : (abs t).x r = 0
  · have : UInt64.ofBitVec ((abs t).x r) = 0 := by rw [hz]; rfl
    simp only [hz, ite_true, this]; rfl
  · have : ¬ UInt64.ofBitVec ((abs t).x r) = 0 := fun h => hz (by rw [← UInt64.toBitVec_ofBitVec ((abs t).x r), h]; rfl)
    simp only [hz, ite_false, this]; rfl

theorem F_b (t : Arm64.State) (f : Int) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : JT.FetchX armDM XD t 4)
    (hf1 : -2 ^ 25 ≤ f) (hf2 : f < 2 ^ 25) (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.bB f)) :
    JT.GoesK armDM XD WD t (JT.jumpTo (O t) ((O t).programCounter + 4 * UInt64.ofInt f)) := by
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.bB] at hA
  have hmo : ArmEnc.mo f 26 < 2 ^ 26 := mo_lt f 26
  obtain ⟨t1, s1, a1, P1⟩ := dm_b (by mask32) hA
  rw [show (wd (0x14000000 + ArmEnc.mo f 26)).extractLsb' 0 26 = BitVec.ofNat 26 (ArmEnc.mo f 26) by
    apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega, off26 f hf1 hf2] at P1
  exact goes1 ⟨t1, s1, P1.run, by rw [obs_jump a1 P1.pc P1.mem P1.sp]; rfl, P1.mem⟩

theorem F_bl (t : Arm64.State) (f : Int) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : JT.FetchX armDM XD t 4)
    (hf1 : -2 ^ 25 ≤ f) (hf2 : f < 2 ^ 25) (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.blB f)) :
    JT.GoesK armDM XD WD t ⟨(O t).programCounter + 4 * UInt64.ofInt f,
      fun r => if r = 30 then (O t).programCounter + 4 else (O t).register r, (O t).memory⟩ := by
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.blB] at hA
  have hmo : ArmEnc.mo f 26 < 2 ^ 26 := mo_lt f 26
  obtain ⟨t1, s1, a1, P1⟩ := dm_bl (by mask32) hA
  rw [show (wd (0x94000000 + ArmEnc.mo f 26)).extractLsb' 0 26 = BitVec.ofNat 26 (ArmEnc.mo f 26) by
    apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega, off26 f hf1 hf2] at P1
  exact goes1 ⟨t1, s1, P1.run, by rw [obs_gen (d := 30) (by decide) (by rw [a1]) P1.pc P1.mem P1.sp]; rfl, P1.mem⟩

theorem F_br (t : Arm64.State) (n : Nat) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : JT.FetchX armDM XD t 4)
    (hn : n < 31) (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.brR n)) :
    JT.GoesK armDM XD WD t (JT.jumpTo (O t) ((O t).register n)) := by
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.brR] at hA
  obtain ⟨t1, s1, a1, P1⟩ := dm_br (by mask32) (by fldt) hA
  rw [show ((wd (0xD61F0000 + n * 2 ^ 5)).extractLsb' 5 5).toNat = n by fldt] at P1
  exact goes1 ⟨t1, s1, P1.run, by rw [obs_jump a1 P1.pc P1.mem P1.sp, show (O t).register n = _ from regv t hn]; rfl, P1.mem⟩

/-! ## loads and stores -/
theorem mapped_of_read {m : Arm64.Memory} {a : BitVec 64} (h : m.canRead a 1 = true) : (m.perm a).isSome = true := by
  simp only [Arm64.Memory.canRead, Arm64.Memory.allPerm, Bool.and_true, Bool.and_eq_true] at h
  have := h.1; revert this; cases m.perm a <;> simp

theorem cbyte_bv (v : UInt64) (k : Nat) (hk : k < 8) : (JT.cbyte v k).toBitVec = v.toBitVec.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [JT.cbyte, UInt64.toBitVec_shiftRight, BitVec.getLsbD_extractLsb', show 8 * k % 64 = 8 * k by omega, hi]

theorem perm_w64 (m : Arm64.Memory) (e v : BitVec 64) (a : BitVec 64) : (m.write64 e v).perm a = m.perm a := by
  rw [write64_eq8]; simp only [perm_w8]

theorem canExec_w64 (m : Arm64.Memory) (e v x : BitVec 64) : (m.write64 e v).canExec x 1 = m.canExec x 1 := by
  rw [write64_eq8]; simp only [Arm64.Memory.canExec, allPerm_w8]

/-- the effective address `x[n] + f` of an unsigned-offset word (scale `2^k`, `f = imm·2^k`) -/
theorem ea_of {t : Arm64.State} {c d n f k : Nat} (hc : c < 2 ^ 32) (hc0 : c % 2 ^ 22 = 0) (hn : n < 31) (hd : d < 32)
    (hf : f % 2 ^ k = 0) (hk : f / 2 ^ k < 4096) (hl : ((abs t).x n).toNat + f < 2 ^ 64) :
    Blocks.ea t (wd (c + f / 2 ^ k * 2 ^ 10 + n * 2 ^ 5 + d)) k = ad (((abs t).x n).toNat + f) := by
  unfold Blocks.ea
  rw [show ((wd (c + f / 2 ^ k * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 5 5).toNat = n by fldt]
  apply BitVec.eq_of_toNat_eq
  have h1 : ((wd (c + f / 2 ^ k * 2 ^ 10 + n * 2 ^ 5 + d)).extractLsb' 10 12).toNat = f / 2 ^ k := by fldt
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, h1, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have : f / 2 ^ k * 2 ^ k = f := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hf)
  rw [Nat.mod_eq_of_lt (show f / 2 ^ k < 2 ^ 64 by omega), this]
  omega

theorem regN (t : Arm64.State) {n : Nat} (hn : n < 31) : ((O t).register n).toNat = ((abs t).x n).toNat := by
  rw [show (O t).register n = _ from regv t hn]; rfl

theorem F_ldr (t : Arm64.State) (r n f : Nat) (v : UInt64) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t))
    (hx : JT.FetchX armDM XD t 4) (hr : r < 31) (hn : n < 31) (hf8 : f % 8 = 0) (hf : f < 32768)
    (hl : ((O t).register n).toNat + f < 2 ^ 64) (hal : (((O t).register n).toNat + f) % 8 = 0)
    (hlo : armDM.ramStart ≤ ((O t).register n).toNat + f) (hhi : ((O t).register n).toNat + f + 8 ≤ armDM.ramEnd)
    (hW : ∀ k < 8, WD t (((O t).register n).toNat + f + k))
    (hv : ∀ k < 8, (O t).memory (UInt64.ofNat (((O t).register n).toNat + f + k)) = some (JT.cbyte v k))
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.ldr r n f)) :
    JT.GoesK armDM XD WD t (JT.setReg (O t) r v) := by
  rw [regN t hn] at hl hal hlo hhi hW hv
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.ldr] at hA
  have ee := ea_of (t := t) (c := 0xF9400000) (d := r) (n := n) (f := f) (k := 3) (by decide) (by decide) hn (by omega)
    (by simpa using hf8) (by simp; omega) hl
  simp only [show (2 : Nat) ^ 3 = 8 from rfl] at ee
  have hb : ∀ k < 8, t.mem.read8 (ad (((abs t).x n).toNat + f) + BitVec.ofNat 64 k) = v.toBitVec.extractLsb' (8 * k) 8 :=
    fun k hk => by rw [ad_addk _ _ (by omega), byte_obs (by omega) (hv k hk), cbyte_bv _ _ hk]
  have hrd : t.mem.canRead (ad (((abs t).x n).toNat + f)) 8 = true :=
    canRead_of _ 8 _ fun k hk => by rw [ad_addk _ _ (by omega)]; exact (hW k hk).1
  have hval : t.mem.read64 (ad (((abs t).x n).toNat + f)) = v.toBitVec := by
    unfold Arm64.Memory.read64
    simp only [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, hb 0 (by omega), hb 1 (by omega), hb 2 (by omega),
      hb 3 (by omega), hb 4 (by omega), hb 5 (by omega), hb 6 (by omega), hb 7 (by omega)]
    exact bytes8 _
  have := dm_ldr (by mask32) (by fldt) (by fldt) (by rw [ee]; exact hrd) hA
  rw [ee, hval, show ((wd (0xF9400000 + f / 8 * 2 ^ 10 + n * 2 ^ 5 + r)).extractLsb' 0 5).toNat = r by fldt] at this
  exact goes_set hr this rfl

theorem F_ldrb (t : Arm64.State) (r n f : Nat) (b : UInt8) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t))
    (hx : JT.FetchX armDM XD t 4) (hr : r < 31) (hn : n < 31) (hf : f < 4096)
    (hl : ((O t).register n).toNat + f < 2 ^ 64)
    (hlo : armDM.ramStart ≤ ((O t).register n).toNat + f) (hhi : ((O t).register n).toNat + f < armDM.ramEnd)
    (hW : WD t (((O t).register n).toNat + f))
    (hv : (O t).memory (UInt64.ofNat (((O t).register n).toNat + f)) = some b)
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.ldrb r n f)) :
    JT.GoesK armDM XD WD t (JT.setReg (O t) r b.toUInt64) := by
  rw [regN t hn] at hl hlo hhi hW hv
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.ldrb] at hA
  have ee := ea_of (t := t) (c := 0x39400000) (d := r) (n := n) (f := f) (k := 0) (by decide) (by decide) hn (by omega)
    (by simp; omega) (by simp; omega) hl
  simp only [show (2 : Nat) ^ 0 = 1 from rfl, Nat.div_one] at ee
  have := dm_ldrb (by mask32) (by fldt) (by fldt) (by rw [ee]; exact hW.1) hA
  rw [ee, byte_obs (by omega) hv,
    show ((wd (0x39400000 + f * 2 ^ 10 + n * 2 ^ 5 + r)).extractLsb' 0 5).toNat = r by fldt] at this
  exact goes_set hr this (by apply UInt64.toBitVec_inj.mp; simp)

theorem keep_w64 {t t' : Arm64.State} {e v : BitVec 64} (h : t'.mem = t.mem.write64 e v) :
    JT.Keep (M := armDM) XD WD t t' :=
  ⟨fun a ha => by unfold XD at ha ⊢; rw [h, canExec_w64]; exact ha,
   fun a ha => by unfold WD at ha ⊢; rw [h, canWrite_w64]; exact ⟨canRead_w64 _ _ _ _ ha.1, ha.2⟩⟩

theorem keep_w8 {t t' : Arm64.State} {e : BitVec 64} {v : BitVec 8} (h : t'.mem = t.mem.write8 e v) :
    JT.Keep (M := armDM) XD WD t t' :=
  ⟨fun a ha => by unfold XD at ha ⊢; rw [h, canExec_w8]; exact ha,
   fun a ha => by unfold WD at ha ⊢; rw [h, canWrite_w8]; exact ⟨canRead_w8 _ _ _ _ ha.1, ha.2⟩⟩

theorem uad (u : UInt64) : u.toBitVec = ad u.toNat := by apply BitVec.eq_of_toNat_eq; simp

theorem F_str (t : Arm64.State) (r n f : Nat) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t))
    (hx : JT.FetchX armDM XD t 4) (hr : r < 31) (hn : n < 31) (hf8 : f % 8 = 0) (hf : f < 32768)
    (hl : ((O t).register n).toNat + f < 2 ^ 64) (hal : (((O t).register n).toNat + f) % 8 = 0)
    (hlo : armDM.ramStart ≤ ((O t).register n).toNat + f) (hhi : ((O t).register n).toNat + f + 8 ≤ armDM.ramEnd)
    (hW : ∀ k < 8, WD t (((O t).register n).toNat + f + k))
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.str r n f)) :
    JT.GoesK armDM XD WD t (JT.store8 (O t) (((O t).register n).toNat + f) ((O t).register r)) := by
  rw [regN t hn] at hl hal hlo hhi hW ⊢
  rw [show (O t).register r = UInt64.ofBitVec ((abs t).x r) from regv t hr]
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.str] at hA
  have ee := ea_of (t := t) (c := 0xF9000000) (d := r) (n := n) (f := f) (k := 3) (by decide) (by decide) hn (by omega)
    (by simpa using hf8) (by simp; omega) hl
  simp only [show (2 : Nat) ^ 3 = 8 from rfl] at ee
  generalize he : ((abs t).x n).toNat + f = e at *
  have hwr : t.mem.canWrite (ad e) 8 = true :=
    canWrite_of _ 8 _ fun k hk => by rw [ad_addk _ _ (by omega)]; exact (hW k hk).2
  have := dm_str (by mask32) (by fldt) (by fldt) (by rw [ee]; exact hwr) hA
  rw [ee, show ((wd (0xF9000000 + f / 8 * 2 ^ 10 + n * 2 ^ 5 + r)).extractLsb' 0 5).toNat = r by fldt] at this
  obtain ⟨t1, s1, a1, P1⟩ := this
  refine ⟨t1, runs_one s1 P1.run, P1.run, ?_, keep_w64 P1.mem⟩
  simp only [O, armDM, obsDM, JT.store8, a1, P1.pc, P1.mem, P1.sp]
  congr 1
  funext u
  rw [uad u, perm_w64]
  by_cases hu : e ≤ u.toNat ∧ u.toNat < e + 8
  · have hk : ad u.toNat = ad e + BitVec.ofNat 64 (u.toNat - e) := by rw [ad_addk _ _ (by omega)]; congr 1; omega
    rw [if_pos hu, hk, read8_w64 _ _ _ _ (by omega), ← hk,
      show (t.mem.perm (ad u.toNat)).isSome = true from mapped_of_read (by
        have := (hW (u.toNat - e) (by omega)).1; rwa [show e + (u.toNat - e) = u.toNat by omega] at this)]
    simp only [ite_true]; congr 1
    apply UInt8.toBitVec_inj.mp; rw [cbyte_bv _ _ (by omega)]
  · rw [if_neg hu, read8_w64_ne _ _ _ _ fun k hk => by
      rw [ad_addk _ _ (by omega)]; exact ad_ne u.toNat_lt (by omega) (by omega)]

theorem F_strb (t : Arm64.State) (r n f : Nat) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t))
    (hx : JT.FetchX armDM XD t 4) (hr : r < 31) (hn : n < 31) (hf : f < 4096)
    (hl : ((O t).register n).toNat + f < 2 ^ 64)
    (hlo : armDM.ramStart ≤ ((O t).register n).toNat + f) (hhi : ((O t).register n).toNat + f < armDM.ramEnd)
    (hW : WD t (((O t).register n).toNat + f))
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.strb r n f)) :
    JT.GoesK armDM XD WD t (JT.store1 (O t) (((O t).register n).toNat + f) ((O t).register r)) := by
  rw [regN t hn] at hl hlo hhi hW ⊢
  rw [show (O t).register r = UInt64.ofBitVec ((abs t).x r) from regv t hr]
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.strb] at hA
  have ee := ea_of (t := t) (c := 0x39000000) (d := r) (n := n) (f := f) (k := 0) (by decide) (by decide) hn (by omega)
    (by simp; omega) (by simp; omega) hl
  simp only [show (2 : Nat) ^ 0 = 1 from rfl, Nat.div_one] at ee
  generalize he : ((abs t).x n).toNat + f = e at *
  have := dm_strb (by mask32) (by fldt) (by fldt) (by rw [ee]; exact hW.2) hA
  rw [ee, show ((wd (0x39000000 + f * 2 ^ 10 + n * 2 ^ 5 + r)).extractLsb' 0 5).toNat = r by fldt] at this
  obtain ⟨t1, s1, a1, P1⟩ := this
  refine ⟨t1, runs_one s1 P1.run, P1.run, ?_, keep_w8 P1.mem⟩
  simp only [O, armDM, obsDM, JT.store1, a1, P1.pc, P1.mem, P1.sp]
  congr 1
  funext u
  rw [uad u, perm_w8, read_w8]
  by_cases hu : u.toNat = e
  · rw [if_pos hu, hu, if_pos rfl, show (t.mem.perm (ad e)).isSome = true from mapped_of_read hW.1]
    simp only [ite_true]; rfl
  · rw [if_neg hu, if_neg (ad_ne u.toNat_lt (by omega) hu)]

end Proven.Apc.Blocks
