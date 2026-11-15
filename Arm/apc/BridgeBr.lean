/- The bridge beyond the 216 expression words: one Sail full step (`stepModel`, under `ArmFull`) and one step of
DeepMind's `Arm64.Step` from related states end in related states, for `b`, `bl`, `cbz`, `b.cond`, `ret`, `movz`,
`movk`, `add`/`sub` immediate, with symbolic fields (the encodings `Apc/*.lean` emits).
Composition of `Arm/proofs/Arm/BrFull.lean` (Sail) and `Apc/Sym.lean` + `Arm64.evalInst` (DeepMind). -/
import Arm.BrFull
import Br.Agree
import Br.Sym
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.all false
namespace ArmProof
open Proven.Apc

/-- related states: Sail `s` (full-step configuration) and DeepMind `t` agree on x0..x30, NZCV and the PC -/
structure Rel (s : St) (t : Arm64.State) : Prop where
  full : ArmFull s
  abs : Abs s (Proven.Apc.abs t)
  pc : s.regs.get? ._PC = some t.pc
  run : t.status = .Running

/-- both machines hold the word `w` at the PC (4-aligned, below `2^29`; executable on DeepMind's side) -/
structure WordAt (s : St) (t : Arm64.State) (w : BitVec 32) : Prop where
  lt : t.pc.toNat < 2 ^ 29
  al : t.pc.toNat % 4 = 0
  sail : MemWord s.mem t.pc.toNat w
  exec : t.mem.canExec t.pc 4 = true
  rd : t.mem.read32 t.pc = w

/-- the conclusion of every bridge lemma: one step each, related again, memories unchanged -/
def Bridged (s : St) (t : Arm64.State) : Prop :=
  ∃ s' t', stepModel s = .ok () s' ∧ Arm64.Step Pg t t' ∧ Rel s' t' ∧ s'.mem = s.mem ∧ t'.mem = t.mem

theorem bridge_of {w : BitVec 32} {i : Arm64.Instr} (hd : Arm64.decode w = some i) {s : St} {t : Arm64.State}
    (hR : Rel s t) (hW : WordAt s t w)
    (hS : ∃ s', stepModel s = .ok () s' ∧ Abs s' (Proven.Apc.abs (Pg.evalInst i t)) ∧ ArmFull s' ∧
      s'.regs.get? ._PC = some (Pg.evalInst i t).pc ∧ s'.mem = s.mem)
    (hM : (Pg.evalInst i t).mem = t.mem) (hst : (Pg.evalInst i t).status = t.status) : Bridged s t := by
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := hS
  refine ⟨s', _, h1, .exec hR.run ?_, ⟨h3, h2, h4, hst.trans hR.run⟩, h5, hM⟩
  have he : Pg.externAt? t.pc = none := rfl
  unfold Arm64.Program.fetchMem; rw [he]; simp [hW.al, hW.exec, hW.rd, hd]

theorem abs_setPC (t : Arm64.State) (x : BitVec 64) : Proven.Apc.abs (t.setPC x) = Proven.Apc.abs t := rfl
theorem abs_adv (t : Arm64.State) : Proven.Apc.abs t.advancePC = Proven.Apc.abs t := rfl
theorem abs_wr (t : Arm64.State) {d : BitVec 5} (hd : d.toNat < 31) (v : BitVec 64) :
    Proven.Apc.abs (t.writeReg64 (.gpr d) v) = (Proven.Apc.abs t).setX d.toNat v := by
  have hd' : (d == 31#5) = false := by
    apply Bool.eq_false_iff.mpr; intro e; rw [beq_iff_eq] at e; subst e; simp at hd
  simp only [Proven.Apc.abs, Arm64.State.writeReg64, hd', AState.setX, show d.toNat ≠ 31 by omega, if_false]
  congr 1; funext i
  by_cases hi : i < 31
  · by_cases e : i = d.toNat
    · subst e; simp [Arm64.RegFile.write, Arm64.RegFile.read, hi]
    · have : BitVec.ofNat 5 i ≠ d := fun h => e (by rw [← h]; simp; omega)
      simp [Arm64.RegFile.write, Arm64.RegFile.read, hi, e, this]
  · simp [hi]; omega
theorem abs_x (t : Arm64.State) {d : BitVec 5} (hd : d.toNat < 31) :
    (Proven.Apc.abs t).x d.toNat = t.regs.read d := by simp [Proven.Apc.abs, hd]

/-- Sail's offset `sign_extend (imm ++ 00)` is DeepMind's `signExtend imm <<< 2` -/
theorem sx2 {n : Nat} (x : BitVec n) (h : n + 2 ≤ 64) : sign_extend (x +++ 0#2) 64 = (x.signExtend 64) <<< 2 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_signExtend, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_append, BitVec.msb_append]
  by_cases h1 : i < 2
  · simp [h1]; intros; omega
  · simp [h1, hi]
    have h3 : i - 2 < 64 := by omega
    simp only [h3, decide_true, Bool.true_and]
    by_cases h2 : i < n + 2
    · simp [h2, show i - 2 < n by omega]
    · simp only [h2, show ¬ i - 2 < n by omega, if_false]
      by_cases hn : n = 0
      · subst hn; simp [BitVec.msb, BitVec.getMsbD]
      · simp [hn]

theorem ne31 {r : BitVec 5} (h : r.toNat < 31) : (r == 31#5) = false := by
  apply Bool.eq_false_iff.mpr; intro e; rw [beq_iff_eq] at e; subst e; simp at h

theorem sl_ext {w : BitVec 32} (a b : Nat) : Sail.BitVec.slice w a b = w.extractLsb' a b := rfl

/-! ## `b`, `bl` -/
theorem br_b (imm : BitVec 26) {s : St} {t : Arm64.State} (hR : Rel s t) (hW : WordAt s t (0x05#6 ++ imm)) :
    Bridged s t := by
  have hK : (0x05#6 ++ imm : BitVec 32) &&& 0xFC000000#32 = 0x14000000#32 := by rw [bW_K]; decide
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_b hR.full hR.abs hR.pc hW.lt hW.al hW.sail hK
  refine bridge_of (Proven.Apc.dec_bsym imm) hR hW ⟨s', h1, h2, h3, ?_, h5⟩ rfl rfl
  rw [h4, sl_ext, bW_imm, sx2 imm (by decide)]; rfl

theorem br_bl (imm : BitVec 26) {s : St} {t : Arm64.State} (hR : Rel s t) (hW : WordAt s t (0x25#6 ++ imm)) :
    Bridged s t := by
  have hK : (0x25#6 ++ imm : BitVec 32) &&& 0xFC000000#32 = 0x94000000#32 := by rw [bW_K]; decide
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_bl hR.full hR.abs hR.pc hW.lt hW.al hW.sail hK
  refine bridge_of (Proven.Apc.dec_blsym imm) hR hW ⟨s', h1, ?_, h3, ?_, h5⟩ rfl rfl
  · show Abs s' (Proven.Apc.abs ((t.writeReg64 (.gpr 30#5) (t.pc + 4#64)).setPC _))
    rw [abs_setPC, abs_wr t (by decide)]; exact h2
  · rw [h4, sl_ext, bW_imm, sx2 imm (by decide)]; rfl

/-! ## `cbz`, `b.cond` -/
theorem br_cbz (imm : BitVec 19) (rt : BitVec 5) (hr : rt.toNat < 31) {s : St} {t : Arm64.State} (hR : Rel s t)
    (hW : WordAt s t (0xB4#8 ++ imm ++ rt)) : Bridged s t := by
  have hK : (0xB4#8 ++ imm ++ rt : BitVec 32) &&& 0xFF000000#32 = 0xB4000000#32 := by rw [cbzW_K]; decide
  have e0 : Sail.BitVec.slice (0xB4#8 ++ imm ++ rt) 0 5 = rt := by rw [sl_ext, cbzW_rt]
  have e5 : Sail.BitVec.slice (0xB4#8 ++ imm ++ rt) 5 19 = imm := by rw [sl_ext, cbzW_imm]
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_cbz hR.full hR.abs hR.pc hW.lt hW.al hW.sail hK (by rw [e0]; exact hr)
  refine bridge_of (Proven.Apc.dec_cbzsym imm rt (ne31 hr)) hR hW ⟨s', h1, ?_, h3, ?_, h5⟩ ?_ ?_
  all_goals simp only [Pg, Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.State.readReg, Arm64.State.readReg64,
    ne31 hr, Bool.false_eq_true, if_false]
  all_goals split
  all_goals first | rfl | exact h2 | skip
  · rename_i hc; rw [h4, e0, abs_x t hr, if_pos (by simpa using hc), e5, sx2 imm (by decide)]; rfl
  · rename_i hc; rw [h4, e0, abs_x t hr, if_neg (by simpa using hc)]; rfl

theorem cond_agree (c : BitVec 4) (p : ProcState) (ps : Arm64.PState) (hN : p.N = .ofBool ps.n)
    (hZ : p.Z = .ofBool ps.z) (hC : p.C = .ofBool ps.c) (hV : p.V = .ofBool ps.v) :
    condP c p = Arm64.ConditionHolds (Arm64.CondCode.ofBits c) ps := by
  obtain ⟨n, z, cc, v⟩ := ps
  unfold condP; rw [hN, hZ, hC, hV]
  rcases bv4 c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  cases n <;> cases z <;> cases cc <;> cases v <;> decide

theorem br_bc (imm : BitVec 19) (c : BitVec 4)
    (hc : c = 0#4 ∨ c = 1#4 ∨ c = 2#4 ∨ c = 3#4 ∨ c = 10#4 ∨ c = 11#4) {s : St} {t : Arm64.State} (hR : Rel s t)
    (hW : WordAt s t (0x54#8 ++ imm ++ 0#1 ++ c)) : Bridged s t := by
  have hK : (0x54#8 ++ imm ++ 0#1 ++ c : BitVec 32) &&& 0xFF000010#32 = 0x54000000#32 := by
    rw [show (0xFF000010#32) = 0xFF00001F#32 &&& 0xFF000010#32 by decide, ← BitVec.and_assoc, bcW_K]; rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have e0 : Sail.BitVec.slice (0x54#8 ++ imm ++ 0#1 ++ c) 0 4 = c := by
    rw [sl_ext, BitVec.extractLsb'_append_eq_of_add_le (by decide)]; simp
  have e5 : Sail.BitVec.slice (0x54#8 ++ imm ++ 0#1 ++ c) 5 19 = imm := by rw [sl_ext, bcW_imm]
  obtain ⟨p, hp, hN, hZ, hC, hV⟩ := hR.abs.p
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_bc hR.full hR.abs hR.pc hW.lt hW.al hW.sail hK hp
  have hca := cond_agree c p t.pstate hN hZ hC hV
  rw [e0, hca, e5, sx2 imm (by decide)] at h4
  refine bridge_of (Proven.Apc.dec_bcsym imm c hc) hR hW ⟨s', h1, ?_, h3, ?_, h5⟩ ?_ ?_
  all_goals simp only [Pg, Arm64.Program.evalInst, Arm64.execInstWithSvc]
  all_goals split
  all_goals first | rfl | exact h2 | skip
  · rename_i hc; rw [h4, if_pos hc]; rfl
  · rename_i hc; rw [h4, if_neg hc]; rfl

/-! ## `ret` -/
theorem dec_ret' : Arm64.decode 0xD65F03C0#32 = some (.ret (.gpr 30#5)) := by decide

theorem br_ret {s : St} {t : Arm64.State} (hR : Rel s t) (hW : WordAt s t 0xD65F03C0#32) : Bridged s t := by
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_ret hR.full hR.abs hR.pc hW.lt hW.al hW.sail
  refine bridge_of dec_ret' hR hW ⟨s', h1, h2, h3, ?_, h5⟩ rfl rfl
  rw [h4, show (30 : Nat) = (30#5 : BitVec 5).toNat from rfl, abs_x t (by decide)]; rfl

/-! ## `movz`, `movk` -/
theorem br_movz (hw : BitVec 2) (imm : BitVec 16) (d : BitVec 5) (hd : d.toNat < 31) {s : St} {t : Arm64.State}
    (hR : Rel s t) (hW : WordAt s t (movW 0x1A5#9 hw imm d)) : Bridged s t := by
  have hK : (movW 0x1A5#9 hw imm d : BitVec 32) &&& 0xFF800000#32 = 0xD2800000#32 := by rw [movW_K]; decide
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_movz hR.full hR.abs hR.pc hW.lt hW.al hW.sail hK (by rw [sl_ext, movW_d]; exact hd)
  rw [sl_ext, sl_ext, sl_ext, movW_d, movW_imm, movW_hw] at h2
  refine bridge_of (Proven.Apc.dec_movz hw imm d (ne31 hd)) hR hW ⟨s', h1, ?_, h3, h4, h5⟩ rfl rfl
  show Abs s' (Proven.Apc.abs ((t.writeReg64 (.gpr d) _).advancePC))
  rw [abs_adv, abs_wr t hd]; exact h2

theorem br_movk (hw : BitVec 2) (imm : BitVec 16) (d : BitVec 5) (hd : d.toNat < 31) {s : St} {t : Arm64.State}
    (hR : Rel s t) (hW : WordAt s t (movW 0x1E5#9 hw imm d)) : Bridged s t := by
  have hK : (movW 0x1E5#9 hw imm d : BitVec 32) &&& 0xFF800000#32 = 0xF2800000#32 := by rw [movW_K]; decide
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_movk hR.full hR.abs hR.pc hW.lt hW.al hW.sail hK (by rw [sl_ext, movW_d]; exact hd)
  rw [sl_ext, sl_ext, sl_ext, movW_d, movW_imm, movW_hw, abs_x t hd] at h2
  refine bridge_of (Proven.Apc.dec_movk hw imm d (ne31 hd)) hR hW ⟨s', h1, ?_, h3, h4, h5⟩ rfl rfl
  show Abs s' (Proven.Apc.abs ((t.writeReg64 (.gpr d) _).advancePC))
  rw [abs_adv, abs_wr t hd]
  simp only [Arm64.State.readReg, Arm64.State.readReg64, ne31 hd, Bool.false_eq_true, if_false]
  rw [BitVec.and_comm]; exact h2

/-! ## `add`/`sub` immediate (64-bit, no shift): `top ++ imm12 ++ rn ++ rd` -/
def aiW (top : BitVec 10) (imm : BitVec 12) (n d : BitVec 5) : BitVec 32 := top ++ imm ++ n ++ d
theorem aiW_K (top imm n d) : aiW top imm n d &&& 0xFFC00000#32 = top ++ (0 : BitVec 12) ++ (0 : BitVec 5) ++ (0 : BitVec 5) := by
  rw [show (0xFFC00000#32) = BitVec.allOnes 10 ++ (0 : BitVec 12) ++ (0 : BitVec 5) ++ (0 : BitVec 5) by decide, aiW,
    BitVec.and_append, BitVec.and_append, BitVec.and_append, BitVec.and_allOnes]; simp
theorem aiW_d (top imm n d) : (aiW top imm n d).extractLsb' 0 5 = d := by
  rw [aiW, BitVec.extractLsb'_append_eq_of_add_le (by decide)]; simp
theorem aiW_n (top imm n d) : (aiW top imm n d).extractLsb' 5 5 = n := by
  rw [aiW, BitVec.extractLsb'_append_eq_of_le (by decide), BitVec.extractLsb'_append_eq_of_add_le (by decide)]; simp
theorem aiW_imm (top imm n d) : (aiW top imm n d).extractLsb' 10 12 = imm := by
  rw [aiW, BitVec.extractLsb'_append_eq_of_le (by decide), BitVec.extractLsb'_append_eq_of_le (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (by decide)]; simp

theorem fromSP {d : BitVec 5} (hd : (d == 31#5) = false) : Arm64.Reg.fromSPBits d = .gpr d := by
  simp [Arm64.Reg.fromSPBits, hd]

theorem dec_addi (imm : BitVec 12) (n d : BitVec 5) (hn : (n == 31#5) = false) (hd : (d == 31#5) = false) :
    Arm64.decode (aiW 0x244#10 imm n d) = some (.addSubImm .W64 .ADD (.gpr d) (.gpr n) imm false) := by
  have hK := aiW_K 0x244#10 imm n d
  decsym hK
  have e1 : (0x244#10 ++ (0 : BitVec 12) ++ (0 : BitVec 5) ++ (0 : BitVec 5)).getLsbD 31 = true := by decide
  have e2 : (0x244#10 ++ (0 : BitVec 12) ++ (0 : BitVec 5) ++ (0 : BitVec 5)).getLsbD 30 = false := by decide
  have e3 : (0x244#10 ++ (0 : BitVec 12) ++ (0 : BitVec 5) ++ (0 : BitVec 5)).getLsbD 29 = false := by decide
  have e4 : (0x244#10 ++ (0 : BitVec 12) ++ (0 : BitVec 5) ++ (0 : BitVec 5)).getLsbD 22 = false := by decide
  simp only [e1, e2, e3, e4, aiW_d, aiW_n, aiW_imm, fromSP hd, fromSP hn]
  rfl

theorem dec_subi (imm : BitVec 12) (n d : BitVec 5) (hn : (n == 31#5) = false) (hd : (d == 31#5) = false) :
    Arm64.decode (aiW 0x344#10 imm n d) = some (.addSubImm .W64 .SUB (.gpr d) (.gpr n) imm false) := by
  have hK := aiW_K 0x344#10 imm n d
  decsym hK
  have e1 : (0x344#10 ++ (0 : BitVec 12) ++ (0 : BitVec 5) ++ (0 : BitVec 5)).getLsbD 31 = true := by decide
  have e2 : (0x344#10 ++ (0 : BitVec 12) ++ (0 : BitVec 5) ++ (0 : BitVec 5)).getLsbD 30 = true := by decide
  have e3 : (0x344#10 ++ (0 : BitVec 12) ++ (0 : BitVec 5) ++ (0 : BitVec 5)).getLsbD 29 = false := by decide
  have e4 : (0x344#10 ++ (0 : BitVec 12) ++ (0 : BitVec 5) ++ (0 : BitVec 5)).getLsbD 22 = false := by decide
  simp only [e1, e2, e3, e4, aiW_d, aiW_n, aiW_imm, fromSP hd, fromSP hn]
  rfl

theorem add_res12 (x : BitVec 64) (y : BitVec 12) :
    BitVec.setWidth 64 (BitVec.setWidth 65 y + BitVec.setWidth 65 x) = x + BitVec.setWidth 64 y := by
  bv_omega

theorem br_addi (imm : BitVec 12) (n d : BitVec 5) (hn : n.toNat < 31) (hd : d.toNat < 31) {s : St} {t : Arm64.State}
    (hR : Rel s t) (hW : WordAt s t (aiW 0x244#10 imm n d)) : Bridged s t := by
  have hK : (aiW 0x244#10 imm n d : BitVec 32) &&& 0xFFC00000#32 = 0x91000000#32 := by rw [aiW_K]; decide
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_addi hR.full hR.abs hR.pc hW.lt hW.al hW.sail hK
    (by rw [sl_ext, aiW_d]; exact hd) (by rw [sl_ext, aiW_n]; exact hn)
  rw [sl_ext, sl_ext, sl_ext, aiW_d, aiW_n, aiW_imm, abs_x t hn] at h2
  refine bridge_of (dec_addi imm n d (ne31 hn) (ne31 hd)) hR hW ⟨s', h1, ?_, h3, h4, h5⟩ rfl rfl
  show Abs s' (Proven.Apc.abs ((t.writeReg64 (.gpr d) _).advancePC))
  rw [abs_adv, abs_wr t hd]
  simpa [Arm64.State.readReg, Arm64.State.readReg64, ne31 hn, Arm64.evalAddSub, Arm64.AddWithCarry64, add_res12] using h2

theorem br_subi (imm : BitVec 12) (n d : BitVec 5) (hn : n.toNat < 31) (hd : d.toNat < 31) {s : St} {t : Arm64.State}
    (hR : Rel s t) (hW : WordAt s t (aiW 0x344#10 imm n d)) : Bridged s t := by
  have hK : (aiW 0x344#10 imm n d : BitVec 32) &&& 0xFFC00000#32 = 0xD1000000#32 := by rw [aiW_K]; decide
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_subi hR.full hR.abs hR.pc hW.lt hW.al hW.sail hK
    (by rw [sl_ext, aiW_d]; exact hd) (by rw [sl_ext, aiW_n]; exact hn)
  rw [sl_ext, sl_ext, sl_ext, aiW_d, aiW_n, aiW_imm, abs_x t hn] at h2
  refine bridge_of (dec_subi imm n d (ne31 hn) (ne31 hd)) hR hW ⟨s', h1, ?_, h3, h4, h5⟩ rfl rfl
  show Abs s' (Proven.Apc.abs ((t.writeReg64 (.gpr d) _).advancePC))
  rw [abs_adv, abs_wr t hd]
  simpa [Arm64.State.readReg, Arm64.State.readReg64, ne31 hn, Arm64.evalAddSub, Arm64.AddWithCarry64, sub_res] using h2

end ArmProof
