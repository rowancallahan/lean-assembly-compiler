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

/-- `CodeOK` for any set `P` of words -/
def CodeOKP (P : BitVec 32 → Bool) (s : St) (t : Arm64.State) : Prop :=
  ∀ a : BitVec 64, a.toNat % 4 = 0 → t.mem.canExec a 4 = true →
    a.toNat < 2 ^ 29 ∧ MemWord s.mem a.toNat (t.mem.read32 a) ∧ P (t.mem.read32 a) = true

/-- the conclusion of the memory bridge lemmas -/
def BridgedM (s : St) (t : Arm64.State) : Prop :=
  ∃ s' t', stepModel s = .ok () s' ∧ Arm64.Step Pg t t' ∧ Rel s' t' ∧ MemRel s' t' ∧
    (∀ P, CodeOKP P s t → CodeOKP P s' t')

theorem bridgedM_of {s : St} {t : Arm64.State} (h : Bridged s t) (hM : MemRel s t) : BridgedM s t := by
  obtain ⟨s', t', h1, h2, h3, h4, h5⟩ := h
  refine ⟨s', t', h1, h2, h3, fun a ha => ?_, fun P hC a ha hx => ?_⟩
  · rw [h5] at ha ⊢; rw [h4]; exact hM a ha
  · rw [h5] at hx ⊢; rw [h4]; exact hC a ha hx

/-- **`ldrb`** bridged, when DeepMind may read the byte -/
theorem br_ldrb (imm : BitVec 12) (n d : BitVec 5) (hn : n.toNat < 31) (hd : d.toNat < 31) {s : St} {t : Arm64.State}
    (hR : Rel s t) (hM : MemRel s t) (hW : WordAt s t (aiW 0x0E5#10 imm n d))
    (hp : t.mem.canRead (t.regs.read n + imm.zeroExtend 64) 1 = true) : BridgedM s t := by
  have hK : (aiW 0x0E5#10 imm n d : BitVec 32) &&& 0xFFC00000#32 = 0x39400000#32 := by rw [aiW_K]; decide
  obtain ⟨hlt, hb⟩ := hM _ (.inl hp)
  have hx := abs_x t hn
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_ldrb hR.full hR.abs hR.pc (va29 hW.lt) hW.al hW.sail hK
    (by rw [sl_ext, aiW_d]; exact hd) (by rw [sl_ext, aiW_n]; exact hn)
    (by rw [sl_ext, sl_ext, aiW_n, aiW_imm, hx]; exact va29 hlt) (by rw [sl_ext, sl_ext, aiW_n, aiW_imm, hx]; exact hb)
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
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_strb hR.full hR.abs hR.pc (va29 hW.lt) hW.al hW.sail hK
    (by rw [sl_ext, aiW_d]; exact hd) (by rw [sl_ext, aiW_n]; exact hn)
    (by rw [sl_ext, sl_ext, aiW_n, aiW_imm, hx]; exact va29 hlt)
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
  refine ⟨s', _, h1, st, ⟨h3, h2, h4, hR.run⟩, fun c hc => ?_, fun P hC a ha hxa => ?_⟩
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
    show a.toNat < 2 ^ 29 ∧ MemWord s'.mem a.toNat ((t.mem.write8 ea _).read32 a) ∧ P ((t.mem.write8 ea _).read32 a) = true
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

/-! ## runs with byte memory -/
/-- the bridged words with byte loads/stores (`ldrb`/`strb wt, [xn, #imm12]`, `t n ≠ 31`) -/
def brM (w : BitVec 32) : Bool :=
  brW w || (w &&& 0xFFC00000#32 == 0x39400000#32 && w.extractLsb' 0 5 != 31#5 && w.extractLsb' 5 5 != 31#5) ||
  (w &&& 0xFFC00000#32 == 0x39000000#32 && w.extractLsb' 0 5 != 31#5 && w.extractLsb' 5 5 != 31#5)

/-- one step of a `brM` word: bridged, or DeepMind faults (status no longer `Running`) -/
theorem bridgeM_step {w : BitVec 32} (hb : brM w = true) {s : St} {t : Arm64.State} (hR : Rel s t) (hM : MemRel s t)
    (hW : WordAt s t w) {i : Arm64.Instr} (hd : Arm64.decode w = some i) :
    BridgedM s t ∨ (Pg.evalInst i t).status ≠ .Running := by
  simp only [brM, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hb
  rcases hb with (h | ⟨⟨h, h'⟩, h''⟩) | ⟨⟨h, h'⟩, h''⟩
  · exact .inl (bridgedM_of (bridge_step h hR hW) hM)
  · rw [t_ldrb h] at hW hd
    rw [dec_ldrb' _ _ _ (ne31 (lt31 h'')) (ne31 (lt31 h'))] at hd; cases hd
    by_cases hp : t.mem.canRead (t.regs.read (w.extractLsb' 5 5) + (w.extractLsb' 10 12).zeroExtend 64) 1 = true
    · exact .inl (br_ldrb _ _ _ (lt31 h'') (lt31 h') hR hM hW hp)
    · right
      simp only [Pg, Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.execLdr, Arm64.checkAddrSPAligned,
        Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.State.readReg64, ne31 (lt31 h''), sh0,
        Arm64.MemWidth.bytes, Bool.not_true, Bool.false_eq_true, if_false, Bool.not_false]
      simp [hp, Arm64.State.setStatus]
  · rw [t_strb h] at hW hd
    rw [dec_strb' _ _ _ (ne31 (lt31 h'')) (ne31 (lt31 h'))] at hd; cases hd
    by_cases hp : t.mem.canWrite (t.regs.read (w.extractLsb' 5 5) + (w.extractLsb' 10 12).zeroExtend 64) 1 = true
    · exact .inl (br_strb _ _ _ (lt31 h'') (lt31 h') hR hM hW hp)
    · right
      simp only [Pg, Arm64.Program.evalInst, Arm64.execInstWithSvc, Arm64.execStr, Arm64.checkAddrSPAligned,
        Arm64.checkRegSPAligned, Arm64.AddrMode.baseReg, Arm64.evalAddrMode, Arm64.State.readReg64, ne31 (lt31 h''), sh0,
        Arm64.MemWidth.bytes, Bool.not_true, Bool.false_eq_true, if_false, Bool.not_false]
      simp [hp, Arm64.State.setStatus]

/-- **simulation with memory**: a DeepMind run ending `Running`, from states related on registers, PC and memory,
with the code mirrored and bridged (`brM`), is matched by full Sail steps ending in related states -/
theorem simM {t t' : Arm64.State} (h : Arm64.Steps Pg t t') (ht' : t'.status = .Running) :
    ∀ {s : St}, Rel s t → MemRel s t → CodeOKP brM s t → ∃ n s', ArmSteps n s s' ∧ Rel s' t' ∧ MemRel s' t' := by
  induction h with
  | refl => intro s hR hM _; exact ⟨0, s, rfl, hR, hM⟩
  | @step t1 t2 t3 h1 h2 ih =>
    intro s hR hM hC
    cases h1 with
    | halt_unmapped _ _ _ =>
      have := steps_stuck h2 (by simp); subst this; simp at ht'
    | extern _ he => rw [pg_ext] at he; cases he
    | extern_fault _ he => rw [pg_ext] at he; cases he
    | exec hrun hf =>
      rename_i i
      have hf' := hf
      unfold Arm64.Program.fetchMem at hf'
      rw [pg_ext] at hf'
      simp only [Option.isSome_none, Bool.false_eq_true, if_false] at hf'
      by_cases hal : t1.pc.toNat % 4 = 0
      · by_cases hx : t1.mem.canExec t1.pc 4 = true
        · simp only [hal, hx, ne_eq, not_true_eq_false, if_false, Bool.not_true, Bool.false_eq_true] at hf'
          obtain ⟨hlt, hm, hb⟩ := hC t1.pc hal hx
          rcases bridgeM_step hb hR hM ⟨hlt, hal, hm, hx, rfl⟩ hf' with
            ⟨s', t2', h1', h2', hR', hM', hC'⟩ | hst
          · have e := step_det h2' (.exec hrun hf); subst e
            obtain ⟨n, s'', h3, h4, h5⟩ := ih ht' hR' hM' (hC' _ hC)
            exact ⟨n + 1, s'', ⟨s', h1', h3⟩, h4, h5⟩
          · have := steps_stuck h2 hst; subst this; exact absurd ht' hst
        · simp [hal, hx] at hf'
      · simp [hal] at hf'

/-! ## insertion sort on Sail, end to end -/
theorem bytes_rel {m m' : Mem} : ∀ {a n : Nat} {l : List (BitVec 8)},
    (∀ j, j < n → ∀ v, m (a + j) = some v → m' (a + j) = some v) → bytes m a n = l.map some → bytes m' a n = l.map some
  | _, 0, _, _, h => h
  | a, n + 1, [], _, h => by simp [bytes] at h
  | a, n + 1, x :: l, hj, h => by
    simp only [bytes, List.map_cons, List.cons.injEq] at h ⊢
    refine ⟨hj 0 (by omega) x (by simpa using h.1) |>.trans rfl |> fun e => by simpa using e, ?_⟩
    exact bytes_rel (fun j hj' v hv => by
      have := hj (j + 1) (by omega) v (by rw [show a + (j + 1) = a + 1 + j by omega]; exact hv)
      rwa [show a + (j + 1) = a + 1 + j by omega] at this) h.2

theorem memV_sail {s : St} {t : Arm64.State} (hM : MemRel s t) (x : Nat) (v : BitVec 8) (h : memV t x = some v) :
    s.mem.get? x = some v := by
  unfold memV at h
  split at h
  · rename_i hc
    cases h
    obtain ⟨-, g⟩ := hM _ (.inl hc.2)
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc.1] at g
  · cases h

theorem codeOKP_of {L : Lay} {P : BitVec 32 → Bool} {s : St} {t : Arm64.State} {pc : BitVec 64} {ws : List (BitVec 32)}
    (hc : (base L).codeAt t pc ws) (hS : CodeAt s.mem pc.toNat ws) (hlt : pc.toNat + 4 * ws.length < 2 ^ 29)
    (hb : ∀ w ∈ ws, P w = true)
    (hX : ∀ a : BitVec 64, a.toNat % 4 = 0 → t.mem.canExec a 4 = true →
      ∃ i < ws.length, a = pc + BitVec.ofNat 64 (4 * i)) : CodeOKP P s t := by
  intro a ha hx
  obtain ⟨i, hi, rfl⟩ := hX a ha hx
  have e : (pc + BitVec.ofNat 64 (4 * i)).toNat = pc.toNat + 4 * i := by simp [BitVec.toNat_add]; omega
  rw [instr_read32 (hc i hi), e]
  exact ⟨by omega, hS i hi, hb _ (List.getElem_mem _)⟩

theorem sort_words0 : ((apc L0).code ((apc L0).compAF [0, 3] sortProg)).all brM = true := by decide +kernel
theorem sort_words (L : Lay) : ∀ w ∈ (apc L).code ((apc L).compAF [0, 3] sortProg), brM w = true :=
  List.all_eq_true.mp sort_words0

/-- **insertion sort on Sail ARMv9, end to end**: under the hypotheses of `sort_apc` on a DeepMind state `t`, from a
Sail state related to `t` on registers, PC and memory (`MemRel`), with the code mirrored in Sail memory and no other
executable memory, full Sail steps reach `PC = x30` with the sorted bytes at `outb` in the Sail memory. -/
theorem sort_sail (L : Lay) {t : Arm64.State} {pc : BitVec 64}
    (hA : (apc L).At t pc ((apc L).code ((apc L).compAF [0, 3] sortProg)))
    {xs out : List (BitVec 8)} {inb outb : Nat} (hd : L.dHi < 2 ^ 63)
    (hi : L.dLo ≤ inb ∧ inb + xs.length ≤ L.dHi) (ho' : L.dLo ≤ outb ∧ outb + xs.length ≤ L.dHi)
    (hio : disjoint ⟨inb, xs.length⟩ ⟨outb, xs.length⟩)
    (hcd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨outb, xs.length⟩],
      disjoint ⟨pc.toNat, 4 * ((apc L).code ((apc L).compAF [0, 3] sortProg)).length⟩ r)
    (h0 : t.regs.read 0#5 = BitVec.ofNat 64 inb) (h1 : t.regs.read 1#5 = BitVec.ofNat 64 xs.length)
    (h3 : t.regs.read 3#5 = BitVec.ofNat 64 outb)
    (hx : bytes (memV t) inb xs.length = xs.map some) (ho : bytes (memV t) outb xs.length = out.map some)
    {s : St} (hR : Rel s t) (hM : MemRel s t)
    (hS : CodeAt s.mem pc.toNat ((apc L).code ((apc L).compAF [0, 3] sortProg)))
    (hlt : pc.toNat + 4 * ((apc L).code ((apc L).compAF [0, 3] sortProg)).length < 2 ^ 29)
    (hX : ∀ a : BitVec 64, a.toNat % 4 = 0 → t.mem.canExec a 4 = true →
      ∃ i < ((apc L).code ((apc L).compAF [0, 3] sortProg)).length, a = pc + BitVec.ofNat 64 (4 * i)) :
    ∃ n s', ArmSteps n s s' ∧ s'.regs.get? ._PC = some (t.regs.read 30#5) ∧
      bytes (fun a => s'.mem.get? a) outb xs.length = (xs.mergeSort leB).map some ∧ ArmFull s' := by
  obtain ⟨t', hs, e1, e2, -, -, e5, -⟩ := sort_apc L hA hd hi ho' hio hcd h0 h1 h3 hx ho
  have hC := codeOKP_of hA.code hS hlt (sort_words L) hX
  obtain ⟨n, s', h, hR', hM'⟩ := simM hs e5 hR hM hC
  exact ⟨n, s', h, by rw [hR'.pc, e1], bytes_rel (fun j _ v hv => memV_sail hM' _ v hv) e2, hR'.full⟩

#print axioms simM
#print axioms sort_sail
end ArmProof
