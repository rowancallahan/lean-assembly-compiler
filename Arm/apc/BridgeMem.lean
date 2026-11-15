/- The bridge for byte loads/stores: a relation between the two memories (byte-addressed, for every DeepMind byte
that is readable or writable), `ldrb`/`strb` bridged, the run-level simulation with memory, and `sort_apc`
(insertion sort, `ldrb`/`strb` + loops) end to end on the Sail model. -/
import Br.BridgeRun
import Arm.Mem
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.all false
namespace ArmProof
open Proven Proven.Apc Proven.Mach

/-- **the memory relation**: every DeepMind byte that is readable or writable lies below `2^29` and is held by the
Sail memory at the same (byte) address -/
def MemRel (s : St) (t : Arm64.State) : Prop :=
  ∀ a : BitVec 64, (t.mem.canRead a 1 = true ∨ t.mem.canWrite a 1 = true) →
    a.toNat < 2 ^ 29 ∧ s.mem.get? a.toNat = some (t.mem.read8 a)

/-! ## DeepMind decode of `ldrb`/`strb wt, [xn, #imm12]` (templates `aiW 0x0E5/0x0E4 imm n t`) -/
theorem dec_ldrb' (imm : BitVec 12) (n d : BitVec 5) (hn : (n == 31#5) = false) (hd : (d == 31#5) = false) :
    Arm64.decode (aiW 0x0E5#10 imm n d) = some (.ldr .W32 .B8 false (.gpr d) (.Offset (.gpr n) (imm.zeroExtend 64 <<< 0))) := by
  have hK := aiW_K 0x0E5#10 imm n d
  decsym hK
  simp only [aiW_d, aiW_n, aiW_imm, Proven.Apc.fromZR hd, fromSP hn]
  rfl
theorem dec_strb' (imm : BitVec 12) (n d : BitVec 5) (hn : (n == 31#5) = false) (hd : (d == 31#5) = false) :
    Arm64.decode (aiW 0x0E4#10 imm n d) = some (.str .B8 (.gpr d) (.Offset (.gpr n) (imm.zeroExtend 64 <<< 0))) := by
  have hK := aiW_K 0x0E4#10 imm n d
  decsym hK
  simp only [aiW_d, aiW_n, aiW_imm, Proven.Apc.fromZR hd, fromSP hn]
  rfl

theorem t_ldrb {w : BitVec 32} (hK : w &&& 0xFFC00000#32 = 0x39400000#32) :
    w = aiW 0x0E5#10 (w.extractLsb' 10 12) (w.extractLsb' 5 5) (w.extractLsb' 0 5) := by
  have h := split4 (a := 10) (b := 12) (c := 5) (d := 5) w
  rwa [kf hK (i := 22) (n := 10) (v := 0x0E5#10) (by decide) (by decide)] at h
theorem t_strb {w : BitVec 32} (hK : w &&& 0xFFC00000#32 = 0x39000000#32) :
    w = aiW 0x0E4#10 (w.extractLsb' 10 12) (w.extractLsb' 5 5) (w.extractLsb' 0 5) := by
  have h := split4 (a := 10) (b := 12) (c := 5) (d := 5) w
  rwa [kf hK (i := 22) (n := 10) (v := 0x0E4#10) (by decide) (by decide)] at h

theorem sh0 (x : BitVec 64) : x <<< 0 = x := by simp
theorem ze8 (b : BitVec 8) : ((b.zeroExtend 64).truncate 32).zeroExtend 64 = b.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq; simp

/-- the conclusion of the memory bridge lemmas -/
def BridgedM (s : St) (t : Arm64.State) : Prop :=
  ∃ s' t', stepModel s = .ok () s' ∧ Arm64.Step Pg t t' ∧ Rel s' t' ∧ MemRel s' t' ∧
    (CodeOK s t → CodeOK s' t')

theorem bridgedM_of {s : St} {t : Arm64.State} (h : Bridged s t) (hM : MemRel s t) : BridgedM s t := by
  obtain ⟨s', t', h1, h2, h3, h4, h5⟩ := h
  refine ⟨s', t', h1, h2, h3, fun a ha => ?_, fun hC a ha hx => ?_⟩
  · rw [h5] at ha ⊢; rw [h4]; exact hM a ha
  · rw [h5] at hx ⊢; rw [h4]; exact hC a ha hx

/-- **`ldrb`** bridged, when DeepMind may read the byte -/
theorem br_ldrb (imm : BitVec 12) (n d : BitVec 5) (hn : n.toNat < 31) (hd : d.toNat < 31) {s : St} {t : Arm64.State}
    (hR : Rel s t) (hM : MemRel s t) (hW : WordAt s t (aiW 0x0E5#10 imm n d))
    (hp : t.mem.canRead (t.regs.read n + imm.zeroExtend 64) 1 = true) : BridgedM s t := by
  have hK : (aiW 0x0E5#10 imm n d : BitVec 32) &&& 0xFFC00000#32 = 0x39400000#32 := by rw [aiW_K]; decide
  obtain ⟨hlt, hb⟩ := hM _ (.inl hp)
  have hx := abs_x t hn
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_ldrb hR.full hR.abs hR.pc hW.lt hW.al hW.sail hK
    (by rw [sl_ext, aiW_d]; exact hd) (by rw [sl_ext, aiW_n]; exact hn)
    (by rw [sl_ext, sl_ext, aiW_n, aiW_imm, hx]; exact hlt) (by rw [sl_ext, sl_ext, aiW_n, aiW_imm, hx]; exact hb)
  rw [sl_ext, aiW_d] at h2
  refine bridgedM_of (bridge_of (dec_ldrb' imm n d (ne31 hn) (ne31 hd)) hR hW ⟨s', h1, ?_, h3, ?_, h5⟩ ?_ ?_) hM
  all_goals simp only [Pg, Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.execLdr, Arm64.checkAddrSPAligned,
    Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.State.readReg64, ne31 hn, sh0,
    Arm64.MemWidth.bytes, hp, Bool.not_true, Bool.false_eq_true, if_false, Bool.not_false]
  all_goals first | rfl | skip
  · show Abs s' (Proven.Apc.abs ((t.writeReg64 (.gpr d) _).advancePC))
    rw [abs_adv, abs_wr t hd]
    simpa [Arm64.Memory.readSized, Arm64.State.writeReg, ze8] using h2
  · exact h4

theorem canExec4_w8 (m : Arm64.Memory) (a b : BitVec 64) (v : BitVec 8) : (m.write8 a v).canExec b 4 = m.canExec b 4 := by
  simp [Arm64.Memory.canExec, Arm64.Memory.allPerm, perm_w8]

theorem exec4 {m : Arm64.Memory} {b : BitVec 64} (h : m.canExec b 4 = true) (j : Nat) (hj : j < 4) :
    m.canExec (b + BitVec.ofNat 64 j) 1 = true := by
  simp only [Arm64.Memory.canExec, Arm64.Memory.allPerm, Bool.and_true, Bool.and_eq_true] at h ⊢
  obtain ⟨h0, h1, h2, h3⟩ := h
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
  · simpa using h0
  · simpa using h1
  · simpa [BitVec.add_assoc] using h2
  · simpa [BitVec.add_assoc] using h3

theorem read32_w8 {m : Arm64.Memory} {a b : BitVec 64} (v : BitVec 8) (h : ∀ j < 4, b + BitVec.ofNat 64 j ≠ a) :
    (m.write8 a v).read32 b = m.read32 b := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide); have h3 := h 3 (by decide)
  simp only [Arm64.Memory.read32, read_w8]
  simp only [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
    show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl,
    h0, h1, h2, h3, if_false]

theorem gi (m : Std.ExtHashMap Nat (BitVec 8)) (k a : Nat) (v : BitVec 8) :
    (m.insert k v).get? a = if k = a then some v else m.get? a := by
  simp [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]

theorem exec_ne_write {m : Arm64.Memory} {a b : BitVec 64} (hx : m.canExec b 1 = true) (hw : m.canWrite a 1 = true) :
    b ≠ a := by
  rintro rfl
  simp only [Arm64.Memory.canExec, Arm64.Memory.canWrite, Arm64.Memory.allPerm, Bool.and_true,
    Bool.and_eq_true, Bool.not_eq_true'] at hx hw
  rw [hx] at hw; exact absurd hw.2 (by decide)

theorem toNat_ne {a b : BitVec 64} (h : a ≠ b) : a.toNat ≠ b.toNat := fun e => h (BitVec.eq_of_toNat_eq e)

/-- **`strb`** bridged, when DeepMind may write the byte -/
theorem br_strb (imm : BitVec 12) (n d : BitVec 5) (hn : n.toNat < 31) (hd : d.toNat < 31) {s : St} {t : Arm64.State}
    (hR : Rel s t) (hM : MemRel s t) (hW : WordAt s t (aiW 0x0E4#10 imm n d))
    (hp : t.mem.canWrite (t.regs.read n + imm.zeroExtend 64) 1 = true) : BridgedM s t := by
  have hK : (aiW 0x0E4#10 imm n d : BitVec 32) &&& 0xFFC00000#32 = 0x39000000#32 := by rw [aiW_K]; decide
  let ea := t.regs.read n + imm.zeroExtend 64
  obtain ⟨hlt, -⟩ := hM ea (.inr hp)
  have hx := abs_x t hn
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_strb hR.full hR.abs hR.pc hW.lt hW.al hW.sail hK
    (by rw [sl_ext, aiW_d]; exact hd) (by rw [sl_ext, aiW_n]; exact hn)
    (by rw [sl_ext, sl_ext, aiW_n, aiW_imm, hx]; exact hlt)
  rw [sl_ext, sl_ext, sl_ext, aiW_n, aiW_imm, aiW_d, hx, abs_x t hd] at h5
  have hev : Pg.evalInst (.str .B8 (.gpr d) (.Offset (.gpr n) (imm.zeroExtend 64 <<< 0))) t =
      (t.setMem (t.mem.write8 ea ((t.regs.read d).truncate 8))).advancePC := by
    simp only [Pg, Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.execStr, Arm64.checkAddrSPAligned,
      Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.State.readReg64, ne31 hn, ne31 hd, sh0,
      Arm64.MemWidth.bytes, hp, Bool.not_true, Bool.false_eq_true, if_false, Bool.not_false, Arm64.Memory.writeSized]
    rfl
  have hsw : (BitVec.setWidth 64 imm) = imm.zeroExtend 64 := rfl
  rw [hsw] at h5
  have hfetch : Pg.fetchMem t.mem t.pc = some (.str .B8 (.gpr d) (.Offset (.gpr n) (imm.zeroExtend 64 <<< 0))) := by
    unfold Arm64.Program.fetchMem; rw [pg_ext]; simp [hW.al, hW.exec, hW.rd, dec_strb' imm n d (ne31 hn) (ne31 hd)]
  have st := Arm64.Step.exec hR.run hfetch
  rw [hev] at st
  refine ⟨s', _, h1, st, ⟨h3, h2, h4, hR.run⟩, fun c hc => ?_, fun hC a ha hxa => ?_⟩
  · show c.toNat < 2 ^ 29 ∧ s'.mem.get? c.toNat = some ((t.mem.write8 ea _).read8 c)
    change (t.mem.write8 ea _).canRead c 1 = true ∨ (t.mem.write8 ea _).canWrite c 1 = true at hc
    rw [h5, read_w8]
    by_cases e : c = ea
    · subst e; refine ⟨hlt, ?_⟩; simp [ea, gi]
    · rw [canRead_w8_ne _ _ _ _ e, canWrite_w8] at hc
      obtain ⟨g1, g2⟩ := hM c hc
      refine ⟨g1, ?_⟩
      rw [gi, if_neg, if_neg e]; exact g2
      intro e'; exact toNat_ne e (by simpa [ea] using e'.symm)
  · change (t.mem.write8 ea _).canExec a 4 = true at hxa
    rw [canExec4_w8] at hxa
    obtain ⟨g1, g2, g3⟩ := hC a ha hxa
    have hne : ∀ j < 4, a + BitVec.ofNat 64 j ≠ ea := fun j hj => exec_ne_write (exec4 hxa j hj) hp
    show a.toNat < 2 ^ 29 ∧ MemWord s'.mem a.toNat ((t.mem.write8 ea _).read32 a) ∧ brW ((t.mem.write8 ea _).read32 a) = true
    rw [read32_w8 _ hne]
    refine ⟨g1, ?_, g3⟩
    have hk : ∀ j < 4, a.toNat + j ≠ ea.toNat := fun j hj e' => hne j hj (BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]; simp [ea] at e' ⊢; omega))
    obtain ⟨m0, m1, m2, m3⟩ := g2
    rw [h5]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [gi, if_neg] <;> first | assumption | skip
    all_goals intro e'
    · exact hk 0 (by decide) (by simpa [ea] using e'.symm)
    · exact hk 1 (by decide) (by simpa [ea] using e'.symm)
    · exact hk 2 (by decide) (by simpa [ea] using e'.symm)
    · exact hk 3 (by decide) (by simpa [ea] using e'.symm)

end ArmProof
