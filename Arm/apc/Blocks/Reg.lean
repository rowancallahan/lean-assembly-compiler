/- Register-register forms on DeepMind's step: `add`/`sub`/`subs` (shifted register, shift 0), `and`/`orr`/`eor`
(shifted register, shift 0), `lslv`/`lsrv`, `madd`. Fields `d = w[4:0]`, `n = w[9:5]`, `m = w[20:16]`
(`a = w[14:10]` for `madd`), all `< 31`. The effects are those of the small machine `armStep` (`Apc/Small.lean`). -/
import Blocks.Base
import Apc.Flags
set_option linter.unusedSimpArgs false
namespace Proven.Apc.Blocks
open Proven.Arm

variable {w : BitVec 32} {t : Arm64.State}

/-- the fields -/
abbrev fd (w : BitVec 32) : BitVec 5 := w.extractLsb' 0 5
abbrev fn (w : BitVec 32) : BitVec 5 := w.extractLsb' 5 5
abbrev fm (w : BitVec 32) : BitVec 5 := w.extractLsb' 16 5
abbrev fa (w : BitVec 32) : BitVec 5 := w.extractLsb' 10 5

macro "evs" : tactic => `(tactic|
  simp [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.readReg, Arm64.State.writeReg,
    Arm64.evalAddSub, Arm64.evalLogical, Arm64.AddWithCarry64, Arm64.shiftVal, Arm64.shift64,
    add_res, sub_res, *])

/-- one step that writes register `d` -/
theorem wr1 {i : Arm64.Instr} {d : BitVec 5} {v : BitVec 64} (hd31 : d.toNat < 31) (hd : Arm64.decode w = some i)
    (h : At t w) (he : Pg.evalInst i t = (t.writeReg64 (.gpr d) v).advancePC) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = (abs t).setX d.toNat v ∧ Post t t' (t.pc + 4) t.mem := by
  refine ⟨_, step_of hd h, ?_, ?_⟩
  · rw [he, abs_adv, abs_wr t hd31]
  · rw [he]; exact ⟨h.run, rfl, rfl, rfl⟩

theorem dec_addR (hK : w &&& 0xFFE0FC00#32 = 0x8B000000#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) :
    Arm64.decode w = some (.addSubShift .W64 .ADD (.gpr (fd w)) (.gpr (fn w)) (.gpr (fm w)) .LSL 0) := by
  decsym hK
  simp only [fromZR' hd, fromZR' hn, fromZR' hm]
  rfl

/-- **`add xd, xn, xm`** -/
theorem dm_addR (hK : w &&& 0xFFE0FC00#32 = 0x8B000000#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = (abs t).setX (fd w).toNat ((abs t).x (fn w).toNat + (abs t).x (fm w).toNat) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine wr1 hd (dec_addR hK hd hn hm) h ?_
  have := rd_gpr t hn; have := rd_gpr t hm
  evs

theorem dec_subR (hK : w &&& 0xFFE0FC00#32 = 0xCB000000#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) :
    Arm64.decode w = some (.addSubShift .W64 .SUB (.gpr (fd w)) (.gpr (fn w)) (.gpr (fm w)) .LSL 0) := by
  decsym hK
  simp only [fromZR' hd, fromZR' hn, fromZR' hm]
  rfl

/-- **`sub xd, xn, xm`** -/
theorem dm_subR (hK : w &&& 0xFFE0FC00#32 = 0xCB000000#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = (abs t).setX (fd w).toNat ((abs t).x (fn w).toNat - (abs t).x (fm w).toNat) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine wr1 hd (dec_subR hK hd hn hm) h ?_
  have := rd_gpr t hn; have := rd_gpr t hm
  evs

theorem dec_andR (hK : w &&& 0xFFE0FC00#32 = 0x8A000000#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) :
    Arm64.decode w = some (.logicalShift .W64 .AND (.gpr (fd w)) (.gpr (fn w)) (.gpr (fm w)) .LSL 0) := by
  decsym hK
  simp only [fromZR' hd, fromZR' hn, fromZR' hm]
  rfl

/-- **`and xd, xn, xm`** -/
theorem dm_andR (hK : w &&& 0xFFE0FC00#32 = 0x8A000000#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = (abs t).setX (fd w).toNat ((abs t).x (fn w).toNat &&& (abs t).x (fm w).toNat) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine wr1 hd (dec_andR hK hd hn hm) h ?_
  have := rd_gpr t hn; have := rd_gpr t hm
  evs

theorem dec_orrR (hK : w &&& 0xFFE0FC00#32 = 0xAA000000#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) :
    Arm64.decode w = some (.logicalShift .W64 .ORR (.gpr (fd w)) (.gpr (fn w)) (.gpr (fm w)) .LSL 0) := by
  decsym hK
  simp only [fromZR' hd, fromZR' hn, fromZR' hm]
  rfl

/-- **`orr xd, xn, xm`** -/
theorem dm_orrR (hK : w &&& 0xFFE0FC00#32 = 0xAA000000#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = (abs t).setX (fd w).toNat ((abs t).x (fn w).toNat ||| (abs t).x (fm w).toNat) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine wr1 hd (dec_orrR hK hd hn hm) h ?_
  have := rd_gpr t hn; have := rd_gpr t hm
  evs

theorem dec_eorR (hK : w &&& 0xFFE0FC00#32 = 0xCA000000#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) :
    Arm64.decode w = some (.logicalShift .W64 .EOR (.gpr (fd w)) (.gpr (fn w)) (.gpr (fm w)) .LSL 0) := by
  decsym hK
  simp only [fromZR' hd, fromZR' hn, fromZR' hm]
  rfl

/-- **`eor xd, xn, xm`** -/
theorem dm_eorR (hK : w &&& 0xFFE0FC00#32 = 0xCA000000#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = (abs t).setX (fd w).toNat ((abs t).x (fn w).toNat ^^^ (abs t).x (fm w).toNat) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine wr1 hd (dec_eorR hK hd hn hm) h ?_
  have := rd_gpr t hn; have := rd_gpr t hm
  evs

theorem dec_lslv (hK : w &&& 0xFFE0FC00#32 = 0x9AC02000#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) :
    Arm64.decode w = some (.dataProc2 .W64 .LSLV (.gpr (fd w)) (.gpr (fn w)) (.gpr (fm w))) := by
  decsym hK
  simp only [fromZR' hd, fromZR' hn, fromZR' hm]
  rfl

/-- **`lslv xd, xn, xm`** (amount `xm mod 64`) -/
theorem dm_lslv (hK : w &&& 0xFFE0FC00#32 = 0x9AC02000#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧
      abs t' = (abs t).setX (fd w).toNat ((abs t).x (fn w).toNat <<< (((abs t).x (fm w).toNat).toNat % 64)) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine wr1 hd (dec_lslv hK hd hn hm) h ?_
  have := rd_gpr t hn; have := rd_gpr t hm
  evs

theorem dec_lsrv (hK : w &&& 0xFFE0FC00#32 = 0x9AC02400#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) :
    Arm64.decode w = some (.dataProc2 .W64 .LSRV (.gpr (fd w)) (.gpr (fn w)) (.gpr (fm w))) := by
  decsym hK
  simp only [fromZR' hd, fromZR' hn, fromZR' hm]
  rfl

/-- **`lsrv xd, xn, xm`** (amount `xm mod 64`) -/
theorem dm_lsrv (hK : w &&& 0xFFE0FC00#32 = 0x9AC02400#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧
      abs t' = (abs t).setX (fd w).toNat ((abs t).x (fn w).toNat >>> (((abs t).x (fm w).toNat).toNat % 64)) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine wr1 hd (dec_lsrv hK hd hn hm) h ?_
  have := rd_gpr t hn; have := rd_gpr t hm
  evs

theorem dec_madd (hK : w &&& 0xFFE08000#32 = 0x9B000000#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) (ha : (fa w).toNat < 31) :
    Arm64.decode w = some (.dataProc3 .W64 .MADD (.gpr (fd w)) (.gpr (fn w)) (.gpr (fm w)) (.gpr (fa w))) := by
  decsym hK
  simp only [fromZR' hd, fromZR' hn, fromZR' hm, fromZR' ha]
  rfl

/-- **`madd xd, xn, xm, xa`**: `xd := xa + xn * xm` -/
theorem dm_madd (hK : w &&& 0xFFE08000#32 = 0x9B000000#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) (ha : (fa w).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧
      abs t' = (abs t).setX (fd w).toNat ((abs t).x (fa w).toNat + (abs t).x (fn w).toNat * (abs t).x (fm w).toNat) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine wr1 hd (dec_madd hK hd hn hm ha) h ?_
  have := rd_gpr t hn; have := rd_gpr t hm; have := rd_gpr t ha
  evs

theorem signExt_not (y : BitVec 64) : BitVec.signExtend 65 (~~~y) = ~~~BitVec.signExtend 65 y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_signExtend, BitVec.getLsbD_not, BitVec.msb_not]
  by_cases h : i < 64 <;> simp [h, hi]

theorem dec_subsR (hK : w &&& 0xFFE0FC00#32 = 0xEB000000#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) :
    Arm64.decode w = some (.addSubShift .W64 .SUBS (.gpr (fd w)) (.gpr (fn w)) (.gpr (fm w)) .LSL 0) := by
  decsym hK
  simp only [fromZR' hd, fromZR' hn, fromZR' hm]
  rfl

/-- **`subs xd, xn, xm`**: `xd := xn - xm`, NZCV of the subtraction (`AState.setSub`, as `armStep`) -/
theorem dm_subsR (hK : w &&& 0xFFE0FC00#32 = 0xEB000000#32) (hd : (fd w).toNat < 31) (hn : (fn w).toNat < 31)
    (hm : (fm w).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧
      abs t' = ((abs t).setSub ((abs t).x (fn w).toNat) ((abs t).x (fm w).toNat)).setX (fd w).toNat
        ((abs t).x (fn w).toNat - (abs t).x (fm w).toNat) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine ⟨_, step_of (dec_subsR hK hd hn hm) h, ?_, ⟨h.run, rfl, rfl, rfl⟩⟩
  have e1 := rd_gpr t hn; have e2 := rd_gpr t hm
  generalize (abs t).x (fn w).toNat = x at e1; generalize (abs t).x (fm w).toNat = y at e2
  simp only [Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.execInst, Arm64.execAddSubShift, Arm64.State.readReg,
    Arm64.State.writeReg, e1, e2, Arm64.shiftVal, Arm64.shift64, Arm64.evalAddSub, Arm64.AddWithCarry64, Arm64.State.setPState,
    Arm64.State.advancePC, sub_res, sub_c, sub_vflag, BitVec.shiftLeft_zero, ↓reduceIte, Nat.zero_mod]
  have ew := abs_wr t hd (x - y)
  simp only [abs, Arm64.State.writeReg64, AState.mk.injEq] at ew ⊢
  simp only [AState.setX, AState.setSub, show (fd w).toNat ≠ 31 by omega, ite_false] at ew ⊢
  rw [AState.mk.injEq]
  refine ⟨congrArg AState.x ew, rfl, beq_dec _ _, rfl, ?_⟩
  rw [signExt_not, sub_vflag, BitVec.toInt_sub]
  simp

end Proven.Apc.Blocks
