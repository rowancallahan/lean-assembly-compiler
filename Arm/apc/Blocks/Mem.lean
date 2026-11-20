/- Load/store forms on DeepMind's step: `ldr`/`str xt, [xn, #8·imm12]` (the `[x16]` form is `imm12 = 0`),
`ldrb`/`strb wt, [xn, #imm12]`. Analogues of Sail's `full_ldr`, `full_str`, `full_ldrb`, `full_strb`
(`Arm/proofs/Arm/Mem.lean`). DeepMind's premise is a permission (`canRead`/`canWrite`), Sail's an address
`< 2^29` (+ 8-alignment for 8 bytes) and the bytes present (`MemD`/`get?`); `BridgeMem.MemRel` connects them. -/
import Blocks.Base
set_option linter.unusedSimpArgs false
namespace Proven.Apc.Blocks
open Proven.Arm

variable {w : BitVec 32} {t : Arm64.State}

/-- the effective address of the unsigned-offset forms, scale `2^k` -/
abbrev ea (t : Arm64.State) (w : BitVec 32) (k : Nat) : BitVec 64 :=
  (abs t).x (w.extractLsb' 5 5).toNat + (w.extractLsb' 10 12).setWidth 64 <<< k

theorem rd_n (t : Arm64.State) {n : BitVec 5} (hn : n.toNat < 31) : t.regs.read n = (abs t).x n.toNat := by
  simp [abs, hn]

macro "memsimp" : tactic => `(tactic|
  simp [Pg, Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.checkAddrSPAligned, Arm64.evalAddrMode,
    Arm64.State.readReg64, Arm64.State.writeReg, Arm64.State.writeReg64, Arm64.State.setMem, Arm64.State.advancePC,
    Arm64.Memory.readSized, Arm64.Memory.writeSized, Arm64.RegFile.read, Arm64.MemWidth.bytes,
    Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg, *])

theorem dec_ldrW (hK : w &&& 0xFFC00000#32 = 0xF9400000#32) (ht : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) :
    Arm64.decode w = some (.ldr .W64 .X64 false (.gpr (w.extractLsb' 0 5))
      (.Offset (.gpr (w.extractLsb' 5 5)) ((w.extractLsb' 10 12).setWidth 64 <<< 3))) := by
  decsym hK
  simp only [fromZR' ht, fromSP hn]
  rfl

/-- **`ldr xt, [xn, #8·imm12]`** -/
theorem dm_ldr (hK : w &&& 0xFFC00000#32 = 0xF9400000#32) (ht : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) (hr : t.mem.canRead (ea t w 3) 8 = true) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = (abs t).setX (w.extractLsb' 0 5).toNat (t.mem.read64 (ea t w 3)) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine ⟨_, step_of (dec_ldrW hK ht hn) h, ?_⟩
  have e := rd_n t hn
  have hr' : t.mem.canRead (t.regs.regs (w.extractLsb' 5 5) + (w.extractLsb' 10 12).setWidth 64 <<< 3) 8 = true := by
    rw [ea, ← e] at hr; exact hr
  have ev : Pg.evalInst (.ldr .W64 .X64 false (.gpr (w.extractLsb' 0 5))
      (.Offset (.gpr (w.extractLsb' 5 5)) ((w.extractLsb' 10 12).setWidth 64 <<< 3))) t =
      (t.writeReg64 (.gpr (w.extractLsb' 0 5)) (t.mem.read64 (ea t w 3))).advancePC := by
    have := ne31 ht; have := ne31 hn; rw [ea, ← e]; memsimp
  rw [ev, abs_adv, abs_wr t ht]; exact ⟨rfl, h.run, rfl, rfl, rfl⟩

theorem dec_strW (hK : w &&& 0xFFC00000#32 = 0xF9000000#32) (ht : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) :
    Arm64.decode w = some (.str .X64 (.gpr (w.extractLsb' 0 5))
      (.Offset (.gpr (w.extractLsb' 5 5)) ((w.extractLsb' 10 12).setWidth 64 <<< 3))) := by
  decsym hK
  simp only [fromZR' ht, fromSP hn]
  rfl

/-- **`str xt, [xn, #8·imm12]`** -/
theorem dm_str (hK : w &&& 0xFFC00000#32 = 0xF9000000#32) (ht : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) (hw : t.mem.canWrite (ea t w 3) 8 = true) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = abs t ∧
      Post t t' (t.pc + 4) (t.mem.write64 (ea t w 3) ((abs t).x (w.extractLsb' 0 5).toNat)) := by
  refine ⟨_, step_of (dec_strW hK ht hn) h, ?_⟩
  have e := rd_n t hn; have e2 := rd_n t ht
  have hw' : t.mem.canWrite (t.regs.regs (w.extractLsb' 5 5) + (w.extractLsb' 10 12).setWidth 64 <<< 3) 8 = true := by
    rw [ea, ← e] at hw; exact hw
  have ev : Pg.evalInst (.str .X64 (.gpr (w.extractLsb' 0 5))
      (.Offset (.gpr (w.extractLsb' 5 5)) ((w.extractLsb' 10 12).setWidth 64 <<< 3))) t =
      { t with mem := t.mem.write64 (ea t w 3) ((abs t).x (w.extractLsb' 0 5).toNat), pc := t.pc + 4 } := by
    have := ne31 ht; have := ne31 hn; rw [ea, ← e, ← e2]; memsimp
  rw [ev]; exact ⟨rfl, h.run, rfl, rfl, rfl⟩

theorem dec_ldrbW (hK : w &&& 0xFFC00000#32 = 0x39400000#32) (ht : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) :
    Arm64.decode w = some (.ldr .W32 .B8 false (.gpr (w.extractLsb' 0 5))
      (.Offset (.gpr (w.extractLsb' 5 5)) ((w.extractLsb' 10 12).setWidth 64 <<< 0))) := by
  decsym hK
  simp only [fromZR' ht, fromSP hn]
  rfl

/-- **`ldrb wt, [xn, #imm12]`** -/
theorem dm_ldrb (hK : w &&& 0xFFC00000#32 = 0x39400000#32) (ht : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) (hr : t.mem.canRead (ea t w 0) 1 = true) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = (abs t).setX (w.extractLsb' 0 5).toNat ((t.mem.read8 (ea t w 0)).setWidth 64) ∧
      Post t t' (t.pc + 4) t.mem := by
  refine ⟨_, step_of (dec_ldrbW hK ht hn) h, ?_⟩
  have e := rd_n t hn
  have hr' : t.mem.canRead (t.regs.regs (w.extractLsb' 5 5) + (w.extractLsb' 10 12).setWidth 64) 1 = true := by
    rw [ea, ← e, BitVec.shiftLeft_zero] at hr; exact hr
  have ev : Pg.evalInst (.ldr .W32 .B8 false (.gpr (w.extractLsb' 0 5))
      (.Offset (.gpr (w.extractLsb' 5 5)) ((w.extractLsb' 10 12).setWidth 64 <<< 0))) t =
      (t.writeReg64 (.gpr (w.extractLsb' 0 5)) ((t.mem.read8 (ea t w 0)).setWidth 64)).advancePC := by
    have := ne31 ht; have := ne31 hn; rw [ea, ← e]; memsimp
  rw [ev, abs_adv, abs_wr t ht]; exact ⟨rfl, h.run, rfl, rfl, rfl⟩

theorem dec_strbW (hK : w &&& 0xFFC00000#32 = 0x39000000#32) (ht : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) :
    Arm64.decode w = some (.str .B8 (.gpr (w.extractLsb' 0 5))
      (.Offset (.gpr (w.extractLsb' 5 5)) ((w.extractLsb' 10 12).setWidth 64 <<< 0))) := by
  decsym hK
  simp only [fromZR' ht, fromSP hn]
  rfl

/-- **`strb wt, [xn, #imm12]`** -/
theorem dm_strb (hK : w &&& 0xFFC00000#32 = 0x39000000#32) (ht : (w.extractLsb' 0 5).toNat < 31)
    (hn : (w.extractLsb' 5 5).toNat < 31) (hw : t.mem.canWrite (ea t w 0) 1 = true) (h : At t w) :
    ∃ t', Arm64.Step Pg t t' ∧ abs t' = abs t ∧
      Post t t' (t.pc + 4) (t.mem.write8 (ea t w 0) (((abs t).x (w.extractLsb' 0 5).toNat).setWidth 8)) := by
  refine ⟨_, step_of (dec_strbW hK ht hn) h, ?_⟩
  have e := rd_n t hn; have e2 := rd_n t ht
  have hw' : t.mem.canWrite (t.regs.regs (w.extractLsb' 5 5) + (w.extractLsb' 10 12).setWidth 64) 1 = true := by
    rw [ea, ← e, BitVec.shiftLeft_zero] at hw; exact hw
  have ev : Pg.evalInst (.str .B8 (.gpr (w.extractLsb' 0 5))
      (.Offset (.gpr (w.extractLsb' 5 5)) ((w.extractLsb' 10 12).setWidth 64 <<< 0))) t =
      { t with mem := t.mem.write8 (ea t w 0) (((abs t).x (w.extractLsb' 0 5).toNat).setWidth 8), pc := t.pc + 4 } := by
    have := ne31 ht; have := ne31 hn; rw [ea, ← e, ← e2]; memsimp
  rw [ev]; exact ⟨rfl, h.run, rfl, rfl, rfl⟩

end Proven.Apc.Blocks
