/- **`A64SemN armDM XD WD`**: the seven instruction forms only the native generator `C/GenArm.lean` emits, on
DeepMind's model: `movn`, `cbnz`, `ldur`, `stur`, `ldp`, `ldrb` (register offset), `add` (register, lsl #3).
Per form: `dec_*` (the decoder), `dm_*` (one `Arm64.Step`, in the shape of the other `dm_*` lemmas), `F_*` (the
`A64SemN` field).  `a64DMN` extends `a64DM`. -/
import Nano.Run.A64SemN
import Blocks.A64Inst
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Proven.Apc.Blocks
open Proven.Top Proven.Arm

variable {w : BitVec 32} {t : Arm64.State}

/-! ## movn -/
theorem dec_movnW (hK : w &&& 0xFF800000#32 = 0x92800000#32) (hd : (w.extractLsb' 0 5).toNat < 31) :
    Arm64.decode w = some (.moveWide .W64 .MOVN (.gpr (w.extractLsb' 0 5)) (w.extractLsb' 5 16)
      ((w.extractLsb' 21 2).toNat * 16)) := by
  decsym hK
  simp only [fromZR (ne31 hd)]
  rfl

/-- **`movn xd, #imm16, lsl #16hw`** -/
theorem dm_movn (hK : w &&& 0xFF800000#32 = 0x92800000#32) (hd : (w.extractLsb' 0 5).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧
      abs t' = (abs t).setX (w.extractLsb' 0 5).toNat
        (~~~((w.extractLsb' 5 16).setWidth 64 <<< ((w.extractLsb' 21 2).toNat * 16))) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine ⟨_, step_of (dec_movnW hK hd) h, ?_, ?_⟩
  · show abs ((t.writeReg64 (.gpr _) _).advancePC) = _
    rw [abs_adv, abs_wr t hd]
  · exact ⟨h.run, rfl, rfl, rfl⟩

theorem F_movn (t : Arm64.State) (d i h : Nat) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : JT.FetchX armDM XD t 4)
    (hd : d < 31) (hi : i < 2 ^ 16) (hh : h < 4)
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.movn d i h)) :
    JT.GoesK armDM XD WD t (JT.setReg (O t) d (JT.movnV i h)) := by
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.movn] at hA
  have := dm_movn (by mask32) (by fldt) hA
  rw [show ((wd (0x92800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)).extractLsb' 0 5).toNat = d by fldt,
    show ((wd (0x92800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)).extractLsb' 21 2).toNat = h by fldt,
    show ((wd (0x92800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)).extractLsb' 5 16).setWidth 64 = BitVec.ofNat 64 i by immt]
    at this
  refine goes_set hd this ?_
  apply UInt64.toBitVec_inj.mp
  simp [JT.movnV, UInt64.toBitVec_shiftLeft, Nat.mul_comm, show h * 16 % 64 = h * 16 by omega]; rfl

theorem F_movzH (t : Arm64.State) (d i h : Nat) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : JT.FetchX armDM XD t 4)
    (hd : d < 31) (hi : i < 2 ^ 16) (hh : h < 4)
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.movzH d i h)) :
    JT.GoesK armDM XD WD t (JT.setReg (O t) d ((UInt64.ofNat i) <<< (16 * h).toUInt64)) := by
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.movzH] at hA
  have := dm_movz (by mask32) (by fldt) hA
  rw [show ((wd (0xD2800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)).extractLsb' 0 5).toNat = d by fldt,
    show ((wd (0xD2800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)).extractLsb' 21 2).toNat = h by fldt,
    show ((wd (0xD2800000 + h * 2 ^ 21 + i * 2 ^ 5 + d)).extractLsb' 5 16).setWidth 64 = BitVec.ofNat 64 i by immt]
    at this
  refine goes_set hd this ?_
  apply UInt64.toBitVec_inj.mp
  simp [UInt64.toBitVec_shiftLeft, Nat.mul_comm, show h * 16 % 64 = h * 16 by omega]; rfl

/-! ## cbnz -/
theorem dec_cbnzW (hK : w &&& 0xFF000000#32 = 0xB5000000#32) (ht : (w.extractLsb' 0 5).toNat < 31) :
    Arm64.decode w = some (.cbz .W64 true (.gpr (w.extractLsb' 0 5)) (((w.extractLsb' 5 19).signExtend 64) <<< 2)) := by
  decsym hK
  simp only [fromZR' ht]
  rfl

/-- **`cbnz xt, imm19`** -/
theorem dm_cbnz (hK : w &&& 0xFF000000#32 = 0xB5000000#32) (ht : (w.extractLsb' 0 5).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = abs t ∧
      Post t t' (if (abs t).x (w.extractLsb' 0 5).toNat = 0 then t.pc + 4
        else t.pc + ((w.extractLsb' 5 19).signExtend 64) <<< 2) t.mem := by
  refine ⟨_, step_of (dec_cbnzW hK ht) h, ?_⟩
  have e : Pg.evalInst (.cbz .W64 true (.gpr (w.extractLsb' 0 5)) (((w.extractLsb' 5 19).signExtend 64) <<< 2)) t =
      if (abs t).x (w.extractLsb' 0 5).toNat = 0 then t.advancePC
      else t.setPC (t.pc + ((w.extractLsb' 5 19).signExtend 64) <<< 2) := by
    simp only [Pg, Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.readReg, rd_gpr t ht]
    by_cases hz : (abs t).x (w.extractLsb' 0 5).toNat = 0 <;> simp [hz]
  rw [e]; split
  · exact ⟨abs_adv _, h.run, rfl, rfl, rfl⟩
  · exact ⟨abs_setPC _ _, h.run, rfl, rfl, rfl⟩

theorem F_cbnz (t : Arm64.State) (r : Nat) (f : Int) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : JT.FetchX armDM XD t 4)
    (hr : r < 31) (hf1 : -2 ^ 18 ≤ f) (hf2 : f < 2 ^ 18)
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.cbnz r f)) :
    JT.GoesK armDM XD WD t (JT.jumpTo (O t) (if (O t).register r = 0
      then (O t).programCounter + 4 else (O t).programCounter + 4 * UInt64.ofInt f)) := by
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.cbnz] at hA
  have hmo : ArmEnc.mo f 19 < 2 ^ 19 := mo_lt f 19
  obtain ⟨t1, s1, a1, P1⟩ := dm_cbnz (by mask32) (by fldt) hA
  rw [show (wd (0xB5000000 + ArmEnc.mo f 19 * 2 ^ 5 + r)).extractLsb' 5 19 = BitVec.ofNat 19 (ArmEnc.mo f 19) by
      apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega,
    show ((wd (0xB5000000 + ArmEnc.mo f 19 * 2 ^ 5 + r)).extractLsb' 0 5).toNat = r by fldt, off19 f hf1 hf2] at P1
  refine goes1 ⟨t1, s1, P1.run, ?_, P1.mem⟩
  rw [obs_jump a1 P1.pc P1.mem P1.sp]
  have er : (O t).register r = UInt64.ofBitVec ((abs t).x r) := regv t hr
  rw [er]
  by_cases hz : (abs t).x r = 0
  · have : UInt64.ofBitVec ((abs t).x r) = 0 := by rw [hz]; rfl
    simp only [hz, ite_true, this]; rfl
  · have : ¬ UInt64.ofBitVec ((abs t).x r) = 0 := fun h => hz (by rw [← UInt64.toBitVec_ofBitVec ((abs t).x r), h]; rfl)
    simp only [hz, ite_false, this]; rfl

/-! ## add (register, lsl #3) -/
theorem dec_addL3 (hK : w &&& 0xFFE0FC00#32 = 0x8B000C00#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) :
    Arm64.decode w = some (.addSubShift .W64 .ADD (.gpr (fd w)) (.gpr (fn w)) (.gpr (fm w)) .LSL 3) := by
  decsym hK
  simp only [fromZR' hd, fromZR' hn, fromZR' hm]
  rfl

/-- **`add xd, xn, xm, lsl #3`** -/
theorem dm_addL3 (hK : w &&& 0xFFE0FC00#32 = 0x8B000C00#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧
      abs t' = (abs t).setX (fd w).toNat ((abs t).x (fn w).toNat + (abs t).x (fm w).toNat <<< 3) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine wr1 hd (dec_addL3 hK hd hn hm) h ?_
  have := rd_gpr t hn; have := rd_gpr t hm
  evs

theorem F_addLsl3 (t : Arm64.State) (d n m : Nat) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t)) (hx : JT.FetchX armDM XD t 4)
    (hd : d < 31) (hn : n < 31) (hm : m < 31)
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.addLsl3 d n m)) :
    JT.GoesK armDM XD WD t (JT.setReg (O t) d ((O t).register n + ((O t).register m <<< 3))) := by
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.addLsl3] at hA
  show JT.GoesK armDM XD WD t (JT.setReg (obsDM t) d ((obsDM t).register n + ((obsDM t).register m <<< 3)))
  rw [regv t hn, regv t hm]
  have := dm_addL3 (by mask32) (by fldt) (by fldt) (by fldt) hA
  rw [show (fd (wd (0x8B000C00 + m * 2 ^ 16 + n * 2 ^ 5 + d))).toNat = d by fldt,
    show (fn (wd (0x8B000C00 + m * 2 ^ 16 + n * 2 ^ 5 + d))).toNat = n by fldt,
    show (fm (wd (0x8B000C00 + m * 2 ^ 16 + n * 2 ^ 5 + d))).toNat = m by fldt] at this
  refine goes_set hd this ?_
  apply UInt64.toBitVec_inj.mp; simp [UInt64.toBitVec_shiftLeft]

/-! ## ldur / stur -/
/-- the effective address of the unscaled forms -/
abbrev eau (t : Arm64.State) (w : BitVec 32) : BitVec 64 :=
  (abs t).x (w.extractLsb' 5 5).toNat + (w.extractLsb' 12 9).signExtend 64

theorem dec_ldurW (hK : w &&& 0xFFE00C00#32 = 0xF8400000#32) (ht : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) :
    Arm64.decode w = some (.ldr .W64 .X64 false (.gpr (w.extractLsb' 0 5))
      (.UnscaledOffset (.gpr (w.extractLsb' 5 5)) ((w.extractLsb' 12 9).signExtend 64))) := by
  decsym hK
  simp only [fromZR' ht, fromSP hn]
  rfl

/-- **`ldur xt, [xn, #simm9]`** -/
theorem dm_ldur (hK : w &&& 0xFFE00C00#32 = 0xF8400000#32) (ht : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) (hr : t.mem.canRead (eau t w) 8 = true) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = (abs t).setX (w.extractLsb' 0 5).toNat (t.mem.read64 (eau t w)) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine ⟨_, step_of (dec_ldurW hK ht hn) h, ?_⟩
  have e := rd_n t hn
  have hr' : t.mem.canRead (t.regs.regs (w.extractLsb' 5 5) + (w.extractLsb' 12 9).signExtend 64) 8 = true := by
    rw [eau, ← e] at hr; exact hr
  have ev : Pg.evalInst (.ldr .W64 .X64 false (.gpr (w.extractLsb' 0 5))
      (.UnscaledOffset (.gpr (w.extractLsb' 5 5)) ((w.extractLsb' 12 9).signExtend 64))) t =
      (t.writeReg64 (.gpr (w.extractLsb' 0 5)) (t.mem.read64 (eau t w))).advancePC := by
    have := ne31 ht; have := ne31 hn; rw [eau, ← e]; memsimp
  rw [ev, abs_adv, abs_wr t ht]; exact ⟨rfl, h.run, rfl, rfl, rfl⟩

theorem dec_sturW (hK : w &&& 0xFFE00C00#32 = 0xF8000000#32) (ht : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) :
    Arm64.decode w = some (.str .X64 (.gpr (w.extractLsb' 0 5))
      (.UnscaledOffset (.gpr (w.extractLsb' 5 5)) ((w.extractLsb' 12 9).signExtend 64))) := by
  decsym hK
  simp only [fromZR' ht, fromSP hn]
  rfl

/-- **`stur xt, [xn, #simm9]`** -/
theorem dm_stur (hK : w &&& 0xFFE00C00#32 = 0xF8000000#32) (ht : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) (hw : t.mem.canWrite (eau t w) 8 = true) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = abs t ∧
      Post t t' (t.pc + 4) (t.mem.write64 (eau t w) ((abs t).x (w.extractLsb' 0 5).toNat)) := by
  refine ⟨_, step_of (dec_sturW hK ht hn) h, ?_⟩
  have e := rd_n t hn; have e2 := rd_n t ht
  have hw' : t.mem.canWrite (t.regs.regs (w.extractLsb' 5 5) + (w.extractLsb' 12 9).signExtend 64) 8 = true := by
    rw [eau, ← e] at hw; exact hw
  have ev : Pg.evalInst (.str .X64 (.gpr (w.extractLsb' 0 5))
      (.UnscaledOffset (.gpr (w.extractLsb' 5 5)) ((w.extractLsb' 12 9).signExtend 64))) t =
      { t with mem := t.mem.write64 (eau t w) ((abs t).x (w.extractLsb' 0 5).toNat), pc := t.pc + 4 } := by
    have := ne31 ht; have := ne31 hn; rw [eau, ← e, ← e2]; memsimp
  rw [ev]; exact ⟨rfl, h.run, rfl, rfl, rfl⟩

/-- the 9-bit signed offset field -/
theorem mo9 (f : Int) (h1 : -256 ≤ f) (h2 : f < 256) : ArmEnc.mo f 9 = if 0 ≤ f then f.toNat else 512 - f.natAbs := by
  unfold ArmEnc.mo; split <;> simp only [Nat.reducePow] <;> omega

/-- the effective address `x[n] + f` of an unscaled word -/
theorem eau_of {t : Arm64.State} {c d n a : Nat} {f : Int} (hc : c < 2 ^ 32) (hc0 : c % 2 ^ 21 = 0) (hn : n < 31)
    (hd : d < 32) (h1 : -256 ≤ f) (h2 : f < 256) (ha : (a : Int) = ((abs t).x n).toNat + f) (hl : a < 2 ^ 64) :
    eau t (wd (c + ArmEnc.mo f 9 * 2 ^ 12 + n * 2 ^ 5 + d)) = ad a := by
  have hm : ArmEnc.mo f 9 < 2 ^ 9 := mo_lt f 9
  unfold eau
  rw [show ((wd (c + ArmEnc.mo f 9 * 2 ^ 12 + n * 2 ^ 5 + d)).extractLsb' 5 5).toNat = n by fldt,
    show (wd (c + ArmEnc.mo f 9 * 2 ^ 12 + n * 2 ^ 5 + d)).extractLsb' 12 9 = BitVec.ofNat 9 (ArmEnc.mo f 9) by
      apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega]
  have hx := ((abs t).x n).isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [mo9 f h1 h2] at hm ⊢
  by_cases h0 : 0 ≤ f
  · simp only [h0, ite_true] at hm ⊢
    simp only [show ¬ 2 ^ (9 - 1) ≤ f.toNat % 2 ^ 9 by omega, decide_false, Bool.false_eq_true, ↓reduceIte]
    omega
  · simp only [h0, ite_false] at hm ⊢
    simp only [show 2 ^ (9 - 1) ≤ (512 - f.natAbs) % 2 ^ 9 by omega, decide_true, ↓reduceIte]
    omega

theorem F_ldur (t : Arm64.State) (r n a : Nat) (f : Int) (v : UInt64) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t))
    (hx : JT.FetchX armDM XD t 4) (hr : r < 31) (hn : n < 31) (hf1 : -256 ≤ f) (hf2 : f < 256)
    (ha : (a : Int) = ((O t).register n).toNat + f) (hal : a % 8 = 0)
    (hlo : armDM.ramStart ≤ a) (hhi : a + 8 ≤ armDM.ramEnd)
    (hW : ∀ k < 8, WD t (a + k))
    (hv : ∀ k < 8, (O t).memory (UInt64.ofNat (a + k)) = some (JT.cbyte v k))
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.ldur r n f)) :
    JT.GoesK armDM XD WD t (JT.setReg (O t) r v) := by
  rw [regN t hn] at ha
  have hl : a + 8 < 2 ^ 64 := by simp [armDM] at hhi; omega
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.ldur] at hA
  have ee := eau_of (t := t) (c := 0xF8400000) (d := r) (n := n) (a := a) (f := f) (by decide) (by decide) hn (by omega)
    hf1 hf2 ha (by omega)
  have hb : ∀ k < 8, t.mem.read8 (ad a + BitVec.ofNat 64 k) = v.toBitVec.extractLsb' (8 * k) 8 :=
    fun k hk => by rw [ad_addk _ _ (by omega), byte_obs (by omega) (hv k hk), cbyte_bv _ _ hk]
  have hrd : t.mem.canRead (ad a) 8 = true :=
    canRead_of _ 8 _ fun k hk => by rw [ad_addk _ _ (by omega)]; exact (hW k hk).1
  have hval : t.mem.read64 (ad a) = v.toBitVec := by
    unfold Arm64.Memory.read64
    simp only [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, hb 0 (by omega), hb 1 (by omega), hb 2 (by omega),
      hb 3 (by omega), hb 4 (by omega), hb 5 (by omega), hb 6 (by omega), hb 7 (by omega)]
    exact bytes8 _
  have hmo : ArmEnc.mo f 9 < 2 ^ 9 := mo_lt f 9
  have := dm_ldur (by mask32) (by fldt) (by fldt) (by rw [ee]; exact hrd) hA
  rw [ee, hval, show ((wd (0xF8400000 + ArmEnc.mo f 9 * 2 ^ 12 + n * 2 ^ 5 + r)).extractLsb' 0 5).toNat = r by fldt] at this
  exact goes_set hr this rfl

theorem F_stur (t : Arm64.State) (r n e : Nat) (f : Int) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t))
    (hx : JT.FetchX armDM XD t 4) (hr : r < 31) (hn : n < 31) (hf1 : -256 ≤ f) (hf2 : f < 256)
    (ha : (e : Int) = ((O t).register n).toNat + f) (hal : e % 8 = 0)
    (hlo : armDM.ramStart ≤ e) (hhi : e + 8 ≤ armDM.ramEnd)
    (hW : ∀ k < 8, WD t (e + k))
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.stur r n f)) :
    JT.GoesK armDM XD WD t (JT.store8 (O t) e ((O t).register r)) := by
  rw [regN t hn] at ha
  rw [show (O t).register r = UInt64.ofBitVec ((abs t).x r) from regv t hr]
  have hl : e + 8 < 2 ^ 64 := by simp [armDM] at hhi; omega
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.stur] at hA
  have ee := eau_of (t := t) (c := 0xF8000000) (d := r) (n := n) (a := e) (f := f) (by decide) (by decide) hn (by omega)
    hf1 hf2 ha (by omega)
  have hwr : t.mem.canWrite (ad e) 8 = true :=
    canWrite_of _ 8 _ fun k hk => by rw [ad_addk _ _ (by omega)]; exact (hW k hk).2
  have hmo : ArmEnc.mo f 9 < 2 ^ 9 := mo_lt f 9
  have := dm_stur (by mask32) (by fldt) (by fldt) (by rw [ee]; exact hwr) hA
  rw [ee, show ((wd (0xF8000000 + ArmEnc.mo f 9 * 2 ^ 12 + n * 2 ^ 5 + r)).extractLsb' 0 5).toNat = r by fldt] at this
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

/-! ## ldrb (register offset) -/
theorem dec_ldrbRW (hK : w &&& 0xFFE0FC00#32 = 0x38606800#32) (ht : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) (hm : (w.extractLsb' 16 5).toNat < 31) :
    Arm64.decode w = some (.ldr .W32 .B8 false (.gpr (w.extractLsb' 0 5))
      (.RegOffset (.gpr (w.extractLsb' 5 5)) (.gpr (w.extractLsb' 16 5)) .UXTX 0)) := by
  decsym hK
  simp only [fromZR' ht, fromSP hn, fromZR' hm]
  rfl

/-- **`ldrb wt, [xn, xm]`** -/
theorem dm_ldrbR (hK : w &&& 0xFFE0FC00#32 = 0x38606800#32) (ht : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) (hm : (w.extractLsb' 16 5).toNat < 31)
    (hr : t.mem.canRead ((abs t).x (w.extractLsb' 5 5).toNat + (abs t).x (w.extractLsb' 16 5).toNat) 1 = true)
    (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = (abs t).setX (w.extractLsb' 0 5).toNat
        ((t.mem.read8 ((abs t).x (w.extractLsb' 5 5).toNat + (abs t).x (w.extractLsb' 16 5).toNat)).setWidth 64) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine ⟨_, step_of (dec_ldrbRW hK ht hn hm) h, ?_⟩
  have e := rd_n t hn; have e2 := rd_n t hm
  rw [← e, ← e2] at hr ⊢
  have hr' : t.mem.canRead (t.regs.regs (w.extractLsb' 5 5) + t.regs.regs (w.extractLsb' 16 5)) 1 = true := hr
  have ev : Pg.evalInst (.ldr .W32 .B8 false (.gpr (w.extractLsb' 0 5))
      (.RegOffset (.gpr (w.extractLsb' 5 5)) (.gpr (w.extractLsb' 16 5)) .UXTX 0)) t =
      (t.writeReg64 (.gpr (w.extractLsb' 0 5))
        ((t.mem.read8 (t.regs.read (w.extractLsb' 5 5) + t.regs.read (w.extractLsb' 16 5))).setWidth 64)).advancePC := by
    have := ne31 ht; have := ne31 hn; have := ne31 hm
    have hx : ∀ v : BitVec 64, Arm64.extendVal .W64 v .UXTX 0 = v := fun v => by simp [Arm64.extendVal]
    memsimp
  rw [ev, abs_adv, abs_wr t ht]; exact ⟨rfl, h.run, rfl, rfl, rfl⟩

theorem F_ldrbR (t : Arm64.State) (r n m : Nat) (b : UInt8) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t))
    (hx : JT.FetchX armDM XD t 4) (hr : r < 31) (hn : n < 31) (hm : m < 31)
    (hlo : armDM.ramStart ≤ ((O t).register n + (O t).register m).toNat)
    (hhi : ((O t).register n + (O t).register m).toNat < armDM.ramEnd)
    (hW : WD t (((O t).register n + (O t).register m).toNat))
    (hv : (O t).memory (UInt64.ofNat (((O t).register n + (O t).register m).toNat)) = some b)
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.ldrbR r n m)) :
    JT.GoesK armDM XD WD t (JT.setReg (O t) r b.toUInt64) := by
  rw [show (O t).register n = UInt64.ofBitVec ((abs t).x n) from regv t hn,
    show (O t).register m = UInt64.ofBitVec ((abs t).x m) from regv t hm,
    show (UInt64.ofBitVec ((abs t).x n) + UInt64.ofBitVec ((abs t).x m)).toNat = ((abs t).x n + (abs t).x m).toNat from rfl]
    at hlo hhi hW hv
  have hl : ((abs t).x n + (abs t).x m).toNat < 2 ^ 64 := ((abs t).x n + (abs t).x m).isLt
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.ldrbR] at hA
  have ee : (abs t).x n + (abs t).x m = ad ((abs t).x n + (abs t).x m).toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  have := dm_ldrbR (by mask32) (by fldt) (by fldt) (by fldt) (by
    rw [show ((wd (0x38606800 + m * 2 ^ 16 + n * 2 ^ 5 + r)).extractLsb' 5 5).toNat = n by fldt,
      show ((wd (0x38606800 + m * 2 ^ 16 + n * 2 ^ 5 + r)).extractLsb' 16 5).toNat = m by fldt, ee]; exact hW.1) hA
  rw [show ((wd (0x38606800 + m * 2 ^ 16 + n * 2 ^ 5 + r)).extractLsb' 5 5).toNat = n by fldt,
    show ((wd (0x38606800 + m * 2 ^ 16 + n * 2 ^ 5 + r)).extractLsb' 16 5).toNat = m by fldt, ee, byte_obs (by omega) hv,
    show ((wd (0x38606800 + m * 2 ^ 16 + n * 2 ^ 5 + r)).extractLsb' 0 5).toNat = r by fldt] at this
  exact goes_set hr this (by apply UInt64.toBitVec_inj.mp; simp)

/-! ## ldp -/
theorem dec_ldpW (hK : w &&& 0xFFFF8000#32 = 0xA9400000#32) (ht : (w.extractLsb' 0 5).toNat < 31)
    (hu : (w.extractLsb' 10 5).toNat < 31) (hn : (w.extractLsb' 5 5).toNat < 31)
    (hne : (w.extractLsb' 0 5 == w.extractLsb' 10 5) = false) :
    Arm64.decode w = some (.ldp .W64 false (.gpr (w.extractLsb' 0 5)) (.gpr (w.extractLsb' 10 5))
      (.Offset (.gpr (w.extractLsb' 5 5)) 0#64)) := by
  decsym hK
  simp only [fromZR' ht, fromZR' hu, fromSP hn, hne]
  rfl

/-- **`ldp xt, xu, [xn]`** (`t ≠ u`) -/
theorem dm_ldp (hK : w &&& 0xFFFF8000#32 = 0xA9400000#32) (ht : (w.extractLsb' 0 5).toNat < 31)
    (hu : (w.extractLsb' 10 5).toNat < 31) (hn : (w.extractLsb' 5 5).toNat < 31)
    (hne : (w.extractLsb' 0 5 == w.extractLsb' 10 5) = false)
    (hr1 : t.mem.canRead ((abs t).x (w.extractLsb' 5 5).toNat) 8 = true)
    (hr2 : t.mem.canRead ((abs t).x (w.extractLsb' 5 5).toNat + 8#64) 8 = true) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧
      abs t' = (((abs t).setX (w.extractLsb' 0 5).toNat (t.mem.read64 ((abs t).x (w.extractLsb' 5 5).toNat))).setX
        (w.extractLsb' 10 5).toNat (t.mem.read64 ((abs t).x (w.extractLsb' 5 5).toNat + 8#64))) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine ⟨_, step_of (dec_ldpW hK ht hu hn hne) h, ?_⟩
  have e := rd_n t hn
  rw [← e] at hr1 hr2 ⊢
  have hr1' : t.mem.canRead (t.regs.regs (w.extractLsb' 5 5)) 8 = true := hr1
  have hr2' : t.mem.canRead (t.regs.regs (w.extractLsb' 5 5) + 8#64) 8 = true := hr2
  have ev : Pg.evalInst (.ldp .W64 false (.gpr (w.extractLsb' 0 5)) (.gpr (w.extractLsb' 10 5))
      (.Offset (.gpr (w.extractLsb' 5 5)) 0#64)) t =
      ((t.writeReg64 (.gpr (w.extractLsb' 0 5)) (t.mem.read64 (t.regs.read (w.extractLsb' 5 5)))).writeReg64
        (.gpr (w.extractLsb' 10 5)) (t.mem.read64 (t.regs.read (w.extractLsb' 5 5) + 8#64))).advancePC := by
    have := ne31 ht; have := ne31 hn; have := ne31 hu; memsimp
  rw [ev, abs_adv, abs_wr _ hu, abs_wr t ht]; exact ⟨rfl, h.run, rfl, rfl, rfl⟩

theorem obs_setX2 {t t' : Arm64.State} {d e : Nat} {v u : BitVec 64} (hd : d < 31) (he : e < 31)
    (ha : abs t' = ((abs t).setX d v).setX e u) (hpc : t'.pc = t.pc + 4) (hm : t'.mem = t.mem) (hsp : t'.sp = t.sp) :
    obsDM t' = JT.setReg2 (obsDM t) d e (UInt64.ofBitVec v) (UInt64.ofBitVec u) := by
  simp only [obsDM, JT.setReg2, ha, hpc, hm, hsp]
  congr 1
  funext r
  by_cases e1 : r = e
  · subst e1; simp [he, AState.setX, show r ≠ 31 by omega]
  · by_cases e2 : r = d
    · subst e2; simp [hd, e1, AState.setX, show r ≠ 31 by omega, show e ≠ 31 by omega]
    · simp only [e1, e2, ite_false]; split
      · simp [AState.setX, e1, e2, show d ≠ 31 by omega, show e ≠ 31 by omega]
      · rfl

/-- `read64` of eight observed bytes -/
theorem read64_obs {t : Arm64.State} {a : Nat} {v : UInt64} (hl : a + 8 < 2 ^ 64)
    (hv : ∀ k < 8, (obsDM t).memory (UInt64.ofNat (a + k)) = some (JT.cbyte v k)) : t.mem.read64 (ad a) = v.toBitVec := by
  have hb : ∀ k < 8, t.mem.read8 (ad a + BitVec.ofNat 64 k) = v.toBitVec.extractLsb' (8 * k) 8 :=
    fun k hk => by rw [ad_addk _ _ (by omega), byte_obs (by omega) (hv k hk), cbyte_bv _ _ hk]
  unfold Arm64.Memory.read64
  simp only [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, hb 0 (by omega), hb 1 (by omega), hb 2 (by omega),
    hb 3 (by omega), hb 4 (by omega), hb 5 (by omega), hb 6 (by omega), hb 7 (by omega)]
  exact bytes8 _

theorem F_ldp (t : Arm64.State) (r u n : Nat) (v1 v2 : UInt64) (hc : armDM.configured t) (hp : JT.PcOK armDM (O t))
    (hx : JT.FetchX armDM XD t 4) (hr : r < 31) (hu : u < 31) (hn : n < 31) (hne : r ≠ u)
    (hal : ((O t).register n).toNat % 8 = 0)
    (hlo : armDM.ramStart ≤ ((O t).register n).toNat) (hhi : ((O t).register n).toNat + 16 ≤ armDM.ramEnd)
    (hW : ∀ k < 16, WD t (((O t).register n).toNat + k))
    (hv1 : ∀ k < 8, (O t).memory (UInt64.ofNat (((O t).register n).toNat + k)) = some (JT.cbyte v1 k))
    (hv2 : ∀ k < 8, (O t).memory (UInt64.ofNat (((O t).register n).toNat + 8 + k)) = some (JT.cbyte v2 k))
    (hw : JT.WordAt (O t) (O t).programCounter.toNat (ArmEnc.ldp r u n)) :
    JT.GoesK armDM XD WD t (JT.setReg2 (O t) r u v1 v2) := by
  rw [regN t hn] at hal hlo hhi hW hv1 hv2
  generalize he : ((abs t).x n).toNat = e at *
  have hl : e + 16 < 2 ^ 64 := by simp [armDM] at hhi; omega
  have hA := fetch hc hp hw (xat hx); simp only [ArmEnc.ldp] at hA
  have e0 : (abs t).x n = ad e := by apply BitVec.eq_of_toNat_eq; simp [← he]
  have e8 : ad e + 8#64 = ad (e + 8) := ad_addk e 8 (by omega)
  have fr : ((wd (0xA9400000 + u * 2 ^ 10 + n * 2 ^ 5 + r)).extractLsb' 0 5).toNat = r := by fldt
  have fu : ((wd (0xA9400000 + u * 2 ^ 10 + n * 2 ^ 5 + r)).extractLsb' 10 5).toNat = u := by fldt
  have fn' : ((wd (0xA9400000 + u * 2 ^ 10 + n * 2 ^ 5 + r)).extractLsb' 5 5).toNat = n := by fldt
  have hrd1 : t.mem.canRead (ad e) 8 = true :=
    canRead_of _ 8 _ fun k hk => by rw [ad_addk _ _ (by omega)]; exact (hW k (by omega)).1
  have hrd2 : t.mem.canRead (ad (e + 8)) 8 = true :=
    canRead_of _ 8 _ fun k hk => by rw [ad_addk _ _ (by omega), show e + 8 + k = e + (8 + k) by omega]; exact (hW (8 + k) (by omega)).1
  have := dm_ldp (t := t) (by mask32) (by rw [fr]; exact hr) (by rw [fu]; exact hu) (by rw [fn']; exact hn)
    (by apply Bool.eq_false_iff.mpr; intro h; rw [beq_iff_eq] at h; have := congrArg BitVec.toNat h; omega)
    (by rw [fn', e0]; exact hrd1) (by rw [fn', e0, e8]; exact hrd2) hA
  rw [fr, fu, fn', e0, e8, read64_obs (by omega) hv1, read64_obs (by omega) hv2] at this
  obtain ⟨t1, s1, a1, P1⟩ := this
  exact goes1 ⟨t1, s1, P1.run, by rw [obs_setX2 hr hu a1 P1.pc P1.mem P1.sp]; rfl, P1.mem⟩

/-- **the native generator's A64 interface on DeepMind's model** -/
theorem a64DMN : JT.A64SemN armDM XD WD where
  toA64Sem := a64DM
  movn s d i h hc hp hx hd hi hh hw := F_movn s d i h hc hp hx hd hi hh hw
  movzH s d i h hc hp hx hd hi hh hw := F_movzH s d i h hc hp hx hd hi hh hw
  cbnz s r f hc hp hx hr hf1 hf2 hw := F_cbnz s r f hc hp hx hr hf1 hf2 hw
  ldur s r n a f v hc hp hx hr hn hf1 hf2 ha hal hlo hhi hW hv hw := F_ldur s r n a f v hc hp hx hr hn hf1 hf2 ha hal hlo hhi hW hv hw
  stur s r n a f hc hp hx hr hn hf1 hf2 ha hal hlo hhi hW hw := F_stur s r n a f hc hp hx hr hn hf1 hf2 ha hal hlo hhi hW hw
  ldp s r u n v1 v2 hc hp hx hr hu hn hne hal hlo hhi hW hv1 hv2 hw := F_ldp s r u n v1 v2 hc hp hx hr hu hn hne hal hlo hhi hW hv1 hv2 hw
  ldrbR s r n m b hc hp hx hr hn hm hlo hhi hW hv hw := F_ldrbR s r n m b hc hp hx hr hn hm hlo hhi hW hv hw
  addLsl3 s d n m hc hp hx hd hn hm hw := F_addLsl3 s d n m hc hp hx hd hn hm hw

end Proven.Apc.Blocks
