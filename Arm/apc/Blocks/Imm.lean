/- `movz`, `movk`, `add`/`sub` immediate (64-bit, shift 0) on DeepMind's step: the analogues of Sail's
`full_movz`, `full_movk`, `full_addi`, `full_subi` (`Arm/proofs/Arm/BrFull.lean`). -/
import Blocks.Base
set_option linter.unusedSimpArgs false
namespace Proven.Apc.Blocks
open Proven.Arm

variable {w : BitVec 32} {t : Arm64.State}

theorem dec_movzW (hK : w &&& 0xFF800000#32 = 0xD2800000#32) (hd : (w.extractLsb' 0 5).toNat < 31) :
    Arm64.decode w = some (.moveWide .W64 .MOVZ (.gpr (w.extractLsb' 0 5)) (w.extractLsb' 5 16)
      ((w.extractLsb' 21 2).toNat * 16)) := by
  decsym hK
  simp only [fromZR (ne31 hd)]
  rfl

/-- **`movz xd, #imm16, lsl #16hw`** -/
theorem dm_movz (hK : w &&& 0xFF800000#32 = 0xD2800000#32) (hd : (w.extractLsb' 0 5).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧
      abs t' = (abs t).setX (w.extractLsb' 0 5).toNat
        ((w.extractLsb' 5 16).setWidth 64 <<< ((w.extractLsb' 21 2).toNat * 16)) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine ⟨_, step_of (dec_movzW hK hd) h, ?_, ?_⟩
  · show abs ((t.writeReg64 (.gpr _) _).advancePC) = _
    rw [abs_adv, abs_wr t hd]
  · exact ⟨h.run, rfl, rfl, rfl⟩

theorem dec_movkW (hK : w &&& 0xFF800000#32 = 0xF2800000#32) (hd : (w.extractLsb' 0 5).toNat < 31) :
    Arm64.decode w = some (.moveWide .W64 .MOVK (.gpr (w.extractLsb' 0 5)) (w.extractLsb' 5 16)
      ((w.extractLsb' 21 2).toNat * 16)) := by
  decsym hK
  simp only [fromZR (ne31 hd)]
  rfl

/-- **`movk xd, #imm16, lsl #16hw`** -/
theorem dm_movk (hK : w &&& 0xFF800000#32 = 0xF2800000#32) (hd : (w.extractLsb' 0 5).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧
      abs t' = (abs t).setX (w.extractLsb' 0 5).toNat
        (~~~(0xFFFF#64 <<< ((w.extractLsb' 21 2).toNat * 16)) &&& (abs t).x (w.extractLsb' 0 5).toNat |||
          (w.extractLsb' 5 16).setWidth 64 <<< ((w.extractLsb' 21 2).toNat * 16)) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine ⟨_, step_of (dec_movkW hK hd) h, ?_, ⟨h.run, rfl, rfl, rfl⟩⟩
  show abs ((t.writeReg64 (.gpr _) _).advancePC) = _
  rw [abs_adv, abs_wr t hd]; congr 1
  simp only [Arm64.State.readReg, rd_gpr t hd]
  rw [BitVec.and_comm]

theorem add_res12 (x : BitVec 64) (y : BitVec 12) :
    BitVec.setWidth 64 (BitVec.setWidth 65 y + BitVec.setWidth 65 x) = x + BitVec.setWidth 64 y := by
  bv_omega

theorem dec_addiW (hK : w &&& 0xFFC00000#32 = 0x91000000#32) (hd : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) : Arm64.decode w = some (.addSubImm .W64 .ADD (.gpr (w.extractLsb' 0 5))
      (.gpr (w.extractLsb' 5 5)) (w.extractLsb' 10 12) false) := by
  decsym hK
  simp only [fromSP hd, fromSP hn]
  rfl

/-- **`add xd, xn, #imm12`** (`d n < 31`) -/
theorem dm_addi (hK : w &&& 0xFFC00000#32 = 0x91000000#32) (hd : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧
      abs t' = (abs t).setX (w.extractLsb' 0 5).toNat ((abs t).x (w.extractLsb' 5 5).toNat + (w.extractLsb' 10 12).setWidth 64) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine ⟨_, step_of (dec_addiW hK hd hn) h, ?_, ⟨h.run, rfl, rfl, rfl⟩⟩
  show abs ((t.writeReg64 (.gpr _) _).advancePC) = _
  rw [abs_adv, abs_wr t hd]; congr 1
  simp [Arm64.State.readReg, rd_gpr t hn, Arm64.evalAddSub, Arm64.AddWithCarry64, add_res12]

theorem dec_subiW (hK : w &&& 0xFFC00000#32 = 0xD1000000#32) (hd : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) : Arm64.decode w = some (.addSubImm .W64 .SUB (.gpr (w.extractLsb' 0 5))
      (.gpr (w.extractLsb' 5 5)) (w.extractLsb' 10 12) false) := by
  decsym hK
  simp only [fromSP hd, fromSP hn]
  rfl

/-- **`sub xd, xn, #imm12`** (`d n < 31`) -/
theorem dm_subi (hK : w &&& 0xFFC00000#32 = 0xD1000000#32) (hd : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧
      abs t' = (abs t).setX (w.extractLsb' 0 5).toNat ((abs t).x (w.extractLsb' 5 5).toNat - (w.extractLsb' 10 12).setWidth 64) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine ⟨_, step_of (dec_subiW hK hd hn) h, ?_, ⟨h.run, rfl, rfl, rfl⟩⟩
  show abs ((t.writeReg64 (.gpr _) _).advancePC) = _
  rw [abs_adv, abs_wr t hd]; congr 1
  simp [Arm64.State.readReg, rd_gpr t hn, Arm64.evalAddSub, Arm64.AddWithCarry64, sub_res]

end Proven.Apc.Blocks
