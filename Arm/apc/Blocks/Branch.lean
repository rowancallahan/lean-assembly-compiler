/- Branch forms on DeepMind's step: `b`, `bl`, `b.cond` (any condition), `cbz`, `br`. Analogues of Sail's `full_b`,
`full_bl`, `full_bc`, `full_cbz` (`Arm/proofs/Arm/BrFull.lean`) and the AL6 draft (`br`). Offsets are DeepMind's
`signExtend imm <<< 2` (= Sail's `sign_extend (imm ++ 00)`, `BridgeBr.sx2`); the condition is the small machine's
`AState.cond` (= Sail's `condP`, `BridgeBr.cond_agree` + `cond_abs` here). -/
import Blocks.Base
set_option linter.unusedSimpArgs false
namespace Proven.Apc.Blocks
open Proven.Arm

variable {w : BitVec 32} {t : Arm64.State}

theorem dec_bW (hK : w &&& 0xFC000000#32 = 0x14000000#32) :
    Arm64.decode w = some (.b (((w.extractLsb' 0 26).signExtend 64) <<< 2)) := by
  decsym hK
  rfl

/-- **`b imm26`** -/
theorem dm_b (hK : w &&& 0xFC000000#32 = 0x14000000#32) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = abs t ∧
      Post t t' (t.pc + ((w.extractLsb' 0 26).signExtend 64) <<< 2) t.mem :=
  ⟨_, step_of (dec_bW hK) h, rfl, ⟨h.run, rfl, rfl, rfl⟩⟩

theorem dec_blW (hK : w &&& 0xFC000000#32 = 0x94000000#32) :
    Arm64.decode w = some (.bl (((w.extractLsb' 0 26).signExtend 64) <<< 2)) := by
  decsym hK
  rfl

/-- **`bl imm26`**: `x30 := PC + 4` -/
theorem dm_bl (hK : w &&& 0xFC000000#32 = 0x94000000#32) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = (abs t).setX 30 (t.pc + 4) ∧
      Post t t' (t.pc + ((w.extractLsb' 0 26).signExtend 64) <<< 2) t.mem := by
  refine ⟨_, step_of (dec_blW hK) h, ?_, ⟨h.run, rfl, rfl, rfl⟩⟩
  show abs ((t.writeReg64 (.gpr 30#5) _).setPC _) = _
  rw [abs_setPC, abs_wr t (d := 30#5) (by decide)]; rfl

theorem dec_cbzW (hK : w &&& 0xFF000000#32 = 0xB4000000#32) (ht : (w.extractLsb' 0 5).toNat < 31) :
    Arm64.decode w = some (.cbz .W64 false (.gpr (w.extractLsb' 0 5)) (((w.extractLsb' 5 19).signExtend 64) <<< 2)) := by
  decsym hK
  simp only [fromZR' ht]
  rfl

/-- **`cbz xt, imm19`** -/
theorem dm_cbz (hK : w &&& 0xFF000000#32 = 0xB4000000#32) (ht : (w.extractLsb' 0 5).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = abs t ∧
      Post t t' (if (abs t).x (w.extractLsb' 0 5).toNat = 0 then t.pc + ((w.extractLsb' 5 19).signExtend 64) <<< 2
        else t.pc + 4) t.mem := by
  refine ⟨_, step_of (dec_cbzW hK ht) h, ?_⟩
  have e : Pg.evalInst (.cbz .W64 false (.gpr (w.extractLsb' 0 5)) (((w.extractLsb' 5 19).signExtend 64) <<< 2)) t =
      if (abs t).x (w.extractLsb' 0 5).toNat = 0 then t.setPC (t.pc + ((w.extractLsb' 5 19).signExtend 64) <<< 2)
      else t.advancePC := by
    simp only [Pg, Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.readReg, rd_gpr t ht]
    by_cases hz : (abs t).x (w.extractLsb' 0 5).toNat = 0 <;> simp [hz]
  rw [e]; split
  · exact ⟨abs_setPC _ _, h.run, rfl, rfl, rfl⟩
  · exact ⟨abs_adv _, h.run, rfl, rfl, rfl⟩

theorem bv4 : ∀ c : BitVec 4, c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨
    c = 10 ∨ c = 11 ∨ c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 := by decide

/-- DeepMind's condition = the small machine's, all 16 codes -/
theorem cond_abs (c : BitVec 4) (t : Arm64.State) :
    Arm64.ConditionHolds (Arm64.CondCode.ofBits c) t.pstate = (abs t).cond c := by
  simp only [abs, AState.cond]; obtain ⟨n, z, cc, v⟩ := t.pstate
  rcases bv4 c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  cases n <;> cases z <;> cases cc <;> cases v <;> decide

theorem dec_bcW (hK : w &&& 0xFF000010#32 = 0x54000000#32) :
    Arm64.decode w = some (.bCond (Arm64.CondCode.ofBits (w.extractLsb' 0 4)) (((w.extractLsb' 5 19).signExtend 64) <<< 2)) := by
  decsym hK

/-- **`b.cond imm19`** (any condition) -/
theorem dm_bc (hK : w &&& 0xFF000010#32 = 0x54000000#32) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = abs t ∧
      Post t t' (if (abs t).cond (w.extractLsb' 0 4) then t.pc + ((w.extractLsb' 5 19).signExtend 64) <<< 2
        else t.pc + 4) t.mem := by
  refine ⟨_, step_of (dec_bcW hK) h, ?_⟩
  have e : Pg.evalInst (.bCond (Arm64.CondCode.ofBits (w.extractLsb' 0 4)) (((w.extractLsb' 5 19).signExtend 64) <<< 2)) t =
      if (abs t).cond (w.extractLsb' 0 4) then t.setPC (t.pc + ((w.extractLsb' 5 19).signExtend 64) <<< 2)
      else t.advancePC := by
    simp only [Pg, Arm64.Program.evalInst, Arm64.execInstWithSvc, cond_abs]
  rw [e]; split
  · exact ⟨abs_setPC _ _, h.run, rfl, rfl, rfl⟩
  · exact ⟨abs_adv _, h.run, rfl, rfl, rfl⟩

theorem dec_brW (hK : w &&& 0xFFFFFC1F#32 = 0xD61F0000#32) (hn : (w.extractLsb' 5 5).toNat < 31) :
    Arm64.decode w = some (.br (.gpr (w.extractLsb' 5 5))) := by
  decsym hK
  simp only [fromZR' hn]
  rfl

/-- **`br xn`** -/
theorem dm_br (hK : w &&& 0xFFFFFC1F#32 = 0xD61F0000#32) (hn : (w.extractLsb' 5 5).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = abs t ∧ Post t t' ((abs t).x (w.extractLsb' 5 5).toNat) t.mem := by
  refine ⟨_, step_of (dec_brW hK hn) h, rfl, ⟨h.run, ?_, rfl, rfl⟩⟩
  simp [Pg, Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.setPC, rd_gpr t hn]

end Proven.Apc.Blocks
