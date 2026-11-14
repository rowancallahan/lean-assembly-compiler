/- Byte arrays with spill slots: the whole function `compileBF N bv p` (prologue, body, epilogue) on
the Sail model.  The prologue puts the frame below `sp` (`fp = alignDown(sp, 8) - 8 (N + 1)`), saves `gp`
at `fp`, sets `gp := fp` and zeroes the `N` slots; the epilogue restores `gp` and returns. -/
import Proven.Arr2
import Proven.Arr2Src

set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Proven

def frameBase (N : Nat) (sp : BitVec 64) : Nat := sp.toNat / 8 * 8 - 8 * (N + 1)

/-- registers other than the temporaries and `gp` kept -/
def KeepX (s s' : St) : Prop := ∀ j : Fin 32, (∀ i, i < 7 → j ≠ T i) → j ≠ 3 → getX s' j = getX s j

theorem KeepX.trans {s₁ s₂ s₃ : St} (a : KeepX s₁ s₂) (b : KeepX s₂ s₃) : KeepX s₁ s₃ :=
  fun j h1 h3 => by rw [b j h1 h3, a j h1 h3]

theorem KeepX.ofNext {s s' : St} {pc rd v m} (hn : Next s s' pc rd v m) (hrd : rd = 0 ∨ rd = 3 ∨ ∃ k, k < 7 ∧ rd = T k) :
    KeepX s s' := fun j h1 h3 => by
  rw [hn.x j]
  rcases hrd with rfl | rfl | ⟨k, hk, rfl⟩
  · simp
  · simp [h3]
  · simp [h1 k hk]

theorem KeepX.ofRan7 {s s' : St} {pc n k} (r : Ran7 s s' pc n k) : KeepX s s' :=
  fun j h1 _ => r.keep j fun i _ hi => h1 i hi

theorem unchanged_trans {s₁ s₂ s₃ : St} {R : List Region} (a : unchangedOutside s₁ s₂ R)
    (b : unchangedOutside s₂ s₃ R) : unchangedOutside s₁ s₃ R := fun x hx => by rw [b x hx, a x hx]

/-- a range outside every region of `R` reads the same -/
theorem bytesAt_out {s s' : St} {R : List Region} (hu : unchangedOutside s s' R) {a n : Nat}
    (hd : ∀ r ∈ R, disjoint ⟨a, n⟩ r) : bytesAt s' a n = bytesAt s a n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact hu _ fun r hr => by have := hd r hr; unfold disjoint at this; dsimp only at this; omega

theorem slotRegs_mem {N fp : Nat} {r : Region} (h : r ∈ slotRegs N fp) :
    ∃ j < N, r = ⟨fp + 8 * (j + 1), 8⟩ := by
  simp only [slotRegs, List.mem_map, List.mem_range] at h
  obtain ⟨j, hj, rfl⟩ := h; exact ⟨j, hj, rfl⟩

theorem slotRegs_ok {N fp : Nat} (hf : FrOK N fp) : RegOK (slotRegs N fp) := by
  refine ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := slotRegs_mem hr; have := hf.hi; have := hf.lo
    unfold Region.inRAM; dsimp only; omega
  · simp only [slotRegs]
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
    intro a b ha hb hab; unfold disjoint; dsimp only; left; omega

/-- frame `⟨fp, 8(N+1)⟩` and the regions: everything in RAM, pairwise disjoint -/
theorem RegOK_frame {N fp : Nat} (hf : FrOK N fp) {R : List Region} (hR : RegOK R)
    (hd : ∀ r ∈ R, disjoint ⟨fp, 8 * (N + 1)⟩ r) : RegOK (R ++ slotRegs N fp) := by
  have hs := slotRegs_ok hf
  refine ⟨fun r hr => ?_, List.pairwise_append.mpr ⟨hR.2, hs.2, fun a ha b hb => ?_⟩⟩
  · rcases List.mem_append.mp hr with h | h; exact hR.1 r h; exact hs.1 r h
  · obtain ⟨j, hj, rfl⟩ := slotRegs_mem hb
    have := hd a ha; unfold disjoint at this ⊢; dsimp only at this ⊢; omega

theorem frame_val (N : Nat) (sp : BitVec 64) (h : 8 * (N + 1) ≤ sp.toNat / 8 * 8) :
    Op.raw .sub (Op.raw .shl (Op.raw .lshr sp (BitVec.ofNat 64 3)) (BitVec.ofNat 64 3)) (BitVec.ofNat 64 (8 * (N + 1)))
      = BitVec.ofNat 64 (frameBase N sp) := by
  have hs := sp.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [Op.raw, Op.eval, reduceCtorEq, if_false, BitVec.toNat_sub, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, frameBase]
  have h8 : 8 * (N + 1) % 2 ^ 64 = 8 * (N + 1) := Nat.mod_eq_of_lt (by omega)
  rw [show (3 % 2 ^ 64 % 64 : Nat) = 3 by rfl, h8, Nat.mod_eq_of_lt (a := sp.toNat / 2 ^ 3 * 2 ^ 3) (by omega)]
  rw [Nat.mod_eq_of_lt (a := sp.toNat / 8 * 8 - 8 * (N + 1)) (by omega)]
  omega

theorem pcB (pc : BitVec 64) (a : Nat) : pc + BitVec.ofNat 64 (4 * a) + 4 = pc + BitVec.ofNat 64 (4 * (a + 1)) :=
  pc_add pc a 1

/-- zeroing slots `0 .. m-1` (`t0 = 0`, `gp = fp`) -/
theorem zero_slots {N fp : Nat} (hf : FrOK N fp) : ∀ m ≤ N, ∀ {s : St} (h : Cfg s) {pc : BitVec 64},
    s.regs.get? .PC = some pc → codeAt s pc ((List.range m).map iSdS) → codeOK pc m →
    (∀ r ∈ slotRegs N fp, disjoint ⟨pc.toNat, 4 * m⟩ r) → getX s 3 = BitVec.ofNat 64 fp → getX s 5 = 0 →
    ∃ s', Reach s s' ∧ Cfg s' ∧ s'.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * m)) ∧
      unchangedOutside s s' (slotRegs N fp) ∧ (∀ j, getX s' j = getX s j) ∧
      ∀ j < m, bytesAt s' (fp + 8 * (j + 1)) 8 = (le8 0).map some
  | 0, _, s, h, pc, hpc, _, _, _, _, _ => ⟨s, ⟨0, rfl⟩, h, by simpa using hpc, fun _ _ => rfl, fun _ => rfl,
      fun j hj => absurd hj (by omega)⟩
  | m + 1, hm, s, h, pc, hpc, hc, hok, hcd, h3, h5 => by
    rw [List.range_succ, List.map_append, codeAt_append] at hc
    simp only [List.length_map, List.length_range, List.map_cons, List.map_nil] at hc
    obtain ⟨ok1, ok2⟩ := codeOK_append (a := m) (b := 1) hok
    obtain ⟨s₁, r₁, h₁, pc₁, u₁, x₁, z₁⟩ := zero_slots hf m (by omega) h hpc hc.1 ok1 (disj_sub hcd (Nat.le_refl _) (by omega)) h3 h5
    have hR := slotRegs_ok hf
    obtain ⟨e1, e2, e3, e4⟩ := slot_addr hf (show m < N by omega) (g := getX s₁ 3) (by rw [x₁]; exact h3)
    have e := pc_toNat hok (a := m) (by omega)
    have hc₂ : codeAt s₁ (pc + BitVec.ofNat 64 (4 * m)) [iSdS m] :=
      codeAt_out hc.2 ok2 (disj_sub hcd (by omega) (by simp; omega)) u₁
    obtain ⟨s₂, hn⟩ := step_sdS h₁ pc₁ (codeOK_pcOK ok2 (by simp)) m (by have := hf.ns; omega) (codeAt_one hc₂) e3 e4 e1
    rw [e2, x₁, h5] at hn
    have hk : m < (slotRegs N fp).length := by simp [slotRegs]; omega
    have hk' : (slotRegs N fp)[m] = ⟨fp + 8 * (m + 1), 8⟩ := by simp [slotRegs]
    obtain ⟨st1, st2, st3⟩ := Next.store_region8 hR.1 hR.2 hk hk' hn
    refine ⟨s₂, r₁.trans (Reach.next hn), hn.cfg, by rw [hn.pc, pcB], fun a ha => ?_, fun j => by rw [hn.keep0, x₁],
      fun j hj => ?_⟩
    · rw [st3 a fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ha _ (List.getElem_mem hk)]
      exact u₁ a ha
    · by_cases hjm : j = m
      · subst hjm; exact st1
      · have hj' : j < (slotRegs N fp).length := by simp [slotRegs]; omega
        have := st2 j hj' hjm; simp only [slotRegs, List.getElem_map, List.getElem_range] at this
        rw [this]; exact z₁ j (by omega)

/-! ## Straight-line code with a cursor `pc + 4 o` -/

theorem cur_app {s : St} {pc : BitVec 64} {o : Nat} {A ws : List (BitVec 32)}
    (hc : codeAt s (pc + BitVec.ofNat 64 (4 * o)) (A ++ ws)) :
    codeAt s (pc + BitVec.ofNat 64 (4 * o)) A ∧ codeAt s (pc + BitVec.ofNat 64 (4 * (o + A.length))) ws := by
  rw [codeAt_append, pc_add] at hc; exact hc

theorem cur_cons {s : St} {pc : BitVec 64} {o : Nat} {w : BitVec 32} {ws : List (BitVec 32)}
    (hc : codeAt s (pc + BitVec.ofNat 64 (4 * o)) (w :: ws)) :
    instrAt s (pc + BitVec.ofNat 64 (4 * o)) w ∧ codeAt s (pc + BitVec.ofNat 64 (4 * (o + 1))) ws := by
  have := cur_app (A := [w]) (ws := ws) hc; exact ⟨codeAt_one this.1, this.2⟩

theorem cur_ok {pc : BitVec 64} {n o m : Nat} (hok : codeOK pc n) (h : o + m ≤ n) :
    codeOK (pc + BitVec.ofNat 64 (4 * o)) m :=
  (codeOK_append (a := o) (b := m) ⟨hok.1, hok.2.1, by have := hok.2.2; omega⟩).2

theorem cur_pcOK {pc : BitVec 64} {n o : Nat} (hok : codeOK pc n) (h : o < n) : pcOK (pc + BitVec.ofNat 64 (4 * o)) :=
  codeOK_pcOK (cur_ok (m := 1) hok h) (by omega)

theorem cur_next {s s' : St} {pc : BitVec 64} {o rd v m} (hn : Next s s' (pc + BitVec.ofNat 64 (4 * o) + 4) rd v m) :
    s'.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * (o + 1))) := by rw [hn.pc, pcB]

theorem cur_codeOut {s s' : St} {pc : BitVec 64} {o : Nat} {ws : List (BitVec 32)} {R : List Region} {n : Nat}
    (hc : codeAt s (pc + BitVec.ofNat 64 (4 * o)) ws) (hok : codeOK pc n) (hn : o + ws.length ≤ n)
    (hd : ∀ r ∈ R, disjoint ⟨pc.toNat, 4 * n⟩ r) (hu : unchangedOutside s s' R) :
    codeAt s' (pc + BitVec.ofNat 64 (4 * o)) ws :=
  codeAt_out hc (cur_ok hok hn) (disj_sub hd (by rw [pc_toNat hok (by omega)]; omega)
    (by rw [pc_toNat hok (by omega)]; omega)) hu

theorem prologue_eq (N : Nat) : prologue N = iSpT :: (genConst 1 3 ++ (iOp .lshr 0 :: iOp .shl 0 ::
    (genConst 1 (8 * (N + 1)) ++ (iOp .sub 0 :: iSdGp :: iGpT :: iZero 0 :: (List.range N).map iSdS)))) := by
  simp [prologue]

theorem T1_ne_T0 : T 1 ≠ T 0 := by decide

/-- **the prologue**: frame at `fp = frameBase N sp`, `gp` saved at `fp`, `gp := fp`, slots zeroed -/
theorem prologue_ok {N : Nat} {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (prologue N)) (hok : codeOK pc (prologue N).length)
    (hf : FrOK N (frameBase N (getX s 2))) (hsp : 8 * (N + 1) ≤ (getX s 2).toNat / 8 * 8)
    (hcd : disjoint ⟨pc.toNat, 4 * (prologue N).length⟩ ⟨frameBase N (getX s 2), 8 * (N + 1)⟩) :
    ∃ s', Reach s s' ∧ Cfg s' ∧ s'.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * (prologue N).length)) ∧
      unchangedOutside s s' [⟨frameBase N (getX s 2), 8 * (N + 1)⟩] ∧ KeepX s s' ∧
      getX s' 3 = BitVec.ofNat 64 (frameBase N (getX s 2)) ∧
      bytesAt s' (frameBase N (getX s 2)) 8 = (le8 (getX s 3)).map some ∧
      ∀ j < N, bytesAt s' (frameBase N (getX s 2) + 8 * (j + 1)) 8 = (le8 0).map some := by
  generalize hfp : frameBase N (getX s 2) = fp at *
  generalize hL : (prologue N).length = L at *
  have hL' := hL; rw [prologue_eq] at hL'
  simp only [List.length_cons, List.length_append, List.length_map, List.length_range] at hL'
  rw [prologue_eq, show pc = pc + BitVec.ofNat 64 (4 * 0) by simp] at hc
  have hpc0 : s.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * 0)) := by simpa using hpc
  -- t0 := sp
  obtain ⟨i1, hc1⟩ := cur_cons hc
  obtain ⟨s₁, n₁⟩ := W2.spT h hpc0 (cur_pcOK hok (by omega)) i1
  -- t1 := 3
  obtain ⟨hc2a, hc2⟩ := cur_app hc1
  obtain ⟨s₂, r₂, R₂, v₂⟩ := const_ok7 1 (by omega) 3 n₁.cfg (cur_next n₁) (codeAt_mem n₁.mem hc2a)
    (cur_ok hok (by omega))
  have P₂ : s₂.regs.get? .PC = some (pc + BitVec.ofNat 64 (4 * (0 + 1 + (genConst 1 3).length))) := by
    rw [R₂.pc, pc_add]
  have m₂ : s₂.mem = s.mem := by rw [R₂.mem, n₁.mem]
  have t0₂ : getX s₂ (T 0) = getX s 2 := by
    rw [R₂.keep _ (fun i hi hi7 he => by have := T_inj (i := 0) (j := i) (by omega) (by omega) he; omega), n₁.x]; rfl
  -- t0 := t0 >>> 3; t0 := t0 <<< 3
  obtain ⟨i3, hc3⟩ := cur_cons (codeAt_mem m₂ hc2)
  obtain ⟨s₃, n₃⟩ := step_op R₂.cfg P₂ (cur_pcOK hok (by omega)) .lshr 0 (by omega) i3
  obtain ⟨i4, hc4⟩ := cur_cons (codeAt_mem n₃.mem hc3)
  obtain ⟨s₄, n₄⟩ := step_op n₃.cfg (cur_next n₃) (cur_pcOK hok (by omega)) .shl 0 (by omega) i4
  -- t1 := 8 (N + 1); t0 := t0 - t1
  obtain ⟨hc5a, hc5⟩ := cur_app (codeAt_mem n₄.mem hc4)
  obtain ⟨s₅, r₅, R₅, v₅⟩ := const_ok7 1 (by omega) (8 * (N + 1)) n₄.cfg (cur_next n₄) hc5a (cur_ok hok (by omega))
  have P₅ : s₅.regs.get? .PC = some (pc + BitVec.ofNat 64
      (4 * (0 + 1 + (genConst 1 3).length + 1 + 1 + (genConst 1 (8 * (N + 1))).length))) := by
    rw [R₅.pc, pc_add]
  obtain ⟨i6, hc6⟩ := cur_cons (codeAt_mem R₅.mem hc5)
  obtain ⟨s₆, n₆⟩ := step_op R₅.cfg P₅ (cur_pcOK hok (by omega)) .sub 0 (by omega) i6
  have a3 : getX s₃ (T 0) = Op.raw .lshr (getX s 2) (BitVec.ofNat 64 3) := by
    rw [n₃.x, if_pos ⟨rfl, by decide⟩, t0₂, show T (0 + 1) = T 1 from rfl, v₂]
  have b3 : getX s₃ (T 1) = BitVec.ofNat 64 3 := by rw [n₃.x, if_neg (fun h => T1_ne_T0 h.1), v₂]
  have a4 : getX s₄ (T 0) = Op.raw .shl (Op.raw .lshr (getX s 2) (BitVec.ofNat 64 3)) (BitVec.ofNat 64 3) := by
    rw [n₄.x, if_pos ⟨rfl, by decide⟩, a3, show T (0 + 1) = T 1 from rfl, b3]
  have a5 : getX s₅ (T 0) = getX s₄ (T 0) :=
    R₅.keep _ (fun i hi hi7 he => by have := T_inj (i := 0) (j := i) (by omega) (by omega) he; omega)
  have t0₆ : getX s₆ 5 = BitVec.ofNat 64 fp := by
    rw [show (5 : Fin 32) = T 0 from rfl, n₆.x, if_pos ⟨rfl, by decide⟩, a5, a4, show T (0 + 1) = T 1 from rfl, v₅,
      ← hfp]
    exact frame_val N (getX s 2) hsp
  have g3 : getX s₆ 3 = getX s 3 := by
    rw [n₆.x, if_neg (by decide), R₅.keep 3 (fun i _ hi => three_ne_T i hi), n₄.x, if_neg (by decide),
      n₃.x, if_neg (by decide), R₂.keep 3 (fun i _ hi => three_ne_T i hi), n₁.x, if_neg (by decide)]
  -- sd gp, 0(t0)
  have hfr := hf
  obtain ⟨i7, hc7⟩ := cur_cons (codeAt_mem n₆.mem hc6)
  have hram : 0x80000000 ≤ (getX s₆ 5).toNat ∧ (getX s₆ 5).toNat + 8 ≤ 0x100000000 := by
    rw [t0₆, toNat_ofNat' (by have := hf.hi; omega)]; have := hf.hi; have := hf.lo; omega
  obtain ⟨s₇, n₇⟩ := W2.sdGp n₆.cfg (cur_next n₆) (cur_pcOK hok (by omega)) i7 hram
    (by rw [t0₆, toNat_ofNat' (by have := hf.hi; omega)]; exact hf.al)
  rw [t0₆, toNat_ofNat' (by have := hf.hi; omega), g3] at n₇
  have hR0 : RegOK [(⟨fp, 8⟩ : Region)] :=
    ⟨fun r hr => by simp at hr; subst hr; have := hf.hi; have := hf.lo; unfold Region.inRAM; dsimp only; omega,
      List.pairwise_singleton _ _⟩
  obtain ⟨st1, -, st3⟩ := Next.store_region8 hR0.1 hR0.2 (k := 0) (by simp) rfl n₇
  have hF : ∀ r ∈ [(⟨fp, 8 * (N + 1)⟩ : Region)], disjoint ⟨pc.toNat, 4 * L⟩ r := by
    intro r hr; simp at hr; subst hr; exact hcd
  have hF8 : ∀ r ∈ [(⟨fp, 8⟩ : Region)], disjoint ⟨pc.toNat, 4 * L⟩ r := by
    intro r hr; simp at hr; subst hr; unfold disjoint at hcd ⊢; dsimp only at hcd ⊢; omega
  -- gp := t0; t0 := 0
  have hc8 := cur_codeOut hc7 hok (by simp; omega) hF8 st3
  obtain ⟨i8, hc8'⟩ := cur_cons hc8
  obtain ⟨s₈, n₈⟩ := W2.gpT n₇.cfg (cur_next n₇) (cur_pcOK hok (by omega)) i8
  obtain ⟨i9, hc9⟩ := cur_cons (codeAt_mem n₈.mem hc8')
  obtain ⟨s₉, n₉⟩ := step_zero n₈.cfg (cur_next n₈) (cur_pcOK hok (by omega)) 0 (by omega) i9
  have g3₉ : getX s₉ 3 = BitVec.ofNat 64 fp := by
    rw [n₉.x, if_neg (by decide), n₈.x, if_pos ⟨rfl, by decide⟩, n₇.keep0, t0₆]
  have g5₉ : getX s₉ 5 = 0 := by rw [show (5 : Fin 32) = T 0 from rfl, n₉.x, if_pos ⟨rfl, by decide⟩]
  -- the slots
  have hS : ∀ r ∈ slotRegs N fp, disjoint ⟨(pc + BitVec.ofNat 64 (4 * (L - N))).toNat, 4 * N⟩ r := by
    intro r hr; obtain ⟨j, hj, rfl⟩ := slotRegs_mem hr
    rw [pc_toNat hok (by omega)]; unfold disjoint at hcd ⊢; dsimp only at hcd ⊢; omega
  obtain ⟨s₁₀, r₁₀, h₁₀, pc₁₀, u₁₀, x₁₀, z₁₀⟩ := zero_slots hf N (Nat.le_refl _) n₉.cfg
    (by rw [cur_next n₉]; congr 3; omega) (by rw [show L - N = 0 + 1 + (genConst 1 3).length + 1 + 1 +
      (genConst 1 (8 * (N + 1))).length + 1 + 1 + 1 + 1 by omega]; exact codeAt_mem n₉.mem hc9) (cur_ok hok (by omega)) hS g3₉ g5₉
  have m₆ : s₆.mem = s.mem := by rw [n₆.mem, R₅.mem, n₄.mem, n₃.mem, R₂.mem, n₁.mem]
  have m₉ : s₉.mem = s₇.mem := by rw [n₉.mem, n₈.mem]
  have hslot : ∀ r ∈ slotRegs N fp, disjoint ⟨fp, 8⟩ r := by
    intro r hr; obtain ⟨j, hj, rfl⟩ := slotRegs_mem hr; unfold disjoint; dsimp only; omega
  refine ⟨s₁₀, (((((((((Reach.next n₁).trans r₂).trans (Reach.next n₃)).trans (Reach.next n₄)).trans r₅).trans
    (Reach.next n₆)).trans (Reach.next n₇)).trans (Reach.next n₈)).trans (Reach.next n₉)).trans r₁₀, h₁₀,
    by rw [pc₁₀, pc_add]; congr 3; omega, fun a ha => ?_, ?_, by rw [x₁₀, g3₉], ?_, z₁₀⟩
  · have ha' := ha _ (List.mem_singleton_self _); dsimp only at ha'
    rw [u₁₀ a (fun r hr => by obtain ⟨j, hj, rfl⟩ := slotRegs_mem hr; dsimp only; omega), m₉,
      st3 a (fun r hr => by simp at hr; subst hr; dsimp only; omega), m₆]
  · have T0 : ∃ k, k < 7 ∧ (5 : Fin 32) = T k := ⟨0, by omega, rfl⟩
    have k1 := KeepX.ofNext n₁ (.inr (.inr T0))
    have k3 := KeepX.ofNext n₃ (.inr (.inr ⟨0, by omega, rfl⟩))
    have k4 := KeepX.ofNext n₄ (.inr (.inr ⟨0, by omega, rfl⟩))
    have k6 := KeepX.ofNext n₆ (.inr (.inr ⟨0, by omega, rfl⟩))
    have k7 := KeepX.ofNext n₇ (.inl rfl)
    have k8 := KeepX.ofNext n₈ (.inr (.inl rfl))
    have k9 := KeepX.ofNext n₉ (.inr (.inr ⟨0, by omega, rfl⟩))
    have k10 : KeepX s₉ s₁₀ := fun j _ _ => x₁₀ j
    exact ((((((((k1.trans (KeepX.ofRan7 R₂)).trans k3).trans k4).trans (KeepX.ofRan7 R₅)).trans k6).trans k7).trans
      k8).trans k9).trans k10
  · rw [bytesAt_out u₁₀ hslot, bytesAt_mem m₉]; simpa using st1

/-! ## The whole function -/

/-- registers other than the temporaries, the variable registers and `gp` kept -/
def KeepB (s s' : St) : Prop :=
  ∀ j : Fin 32, (∀ i, i < 7 → j ≠ T i) → (∀ i : Fin 8, j ≠ A8 i) → j ≠ 3 → getX s' j = getX s j

theorem calleeSaved_of_keepB {s s' : St} (h : Cfg s) (h₃ : Cfg s') (f : KeepB s s') : calleeSavedKept s s' := by
  have ne : ∀ j ∈ ([2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] : List (Fin 32)),
      (∀ i, i < 7 → j ≠ T i) ∧ (∀ i : Fin 8, j ≠ A8 i) ∧ j ≠ 3 := by decide
  have k : ∀ j ∈ ([2, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] : List (Fin 32)), getX s' j = getX s j :=
    fun j hj => f j (ne j hj).1 (ne j hj).2.1 (ne j hj).2.2
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₃.x2, h.x2, k 2 (by decide)]
  · rw [h₃.x8, h.x8, k 8 (by decide)]
  · rw [h₃.x9, h.x9, k 9 (by decide)]
  · rw [h₃.x18, h.x18, k 18 (by decide)]
  · rw [h₃.x19, h.x19, k 19 (by decide)]
  · rw [h₃.x20, h.x20, k 20 (by decide)]
  · rw [h₃.x21, h.x21, k 21 (by decide)]
  · rw [h₃.x22, h.x22, k 22 (by decide)]
  · rw [h₃.x23, h.x23, k 23 (by decide)]
  · rw [h₃.x24, h.x24, k 24 (by decide)]
  · rw [h₃.x25, h.x25, k 25 (by decide)]
  · rw [h₃.x26, h.x26, k 26 (by decide)]
  · rw [h₃.x27, h.x27, k 27 (by decide)]

theorem A8_ne_T : ∀ i : Fin 8, ∀ k < 7, A8 i ≠ T k := by decide

set_option maxHeartbeats 2000000 in
/-- **Correctness of `compileBF`** (a called function with `N` spill slots): if `p` runs from `σ` to `σ'`
(slots start at `0`), the machine state holds `σ` in `a0..a7` and the regions `R`, and the frame
`⟨frameBase N sp, 8 (N + 1)⟩` below `sp` is in RAM and disjoint from the regions and the code, then the Sail
model returns to `ra` with `σ'` in `a0..a7` and the regions, memory outside the frame and the regions
unchanged, callee-saved registers, `gp` and `Cfg` kept. -/
theorem compileBF_ok (N : Nat) (bv : List Nat) (hbv : ∀ x ∈ bv, x < 8 + N) {p : BStmt} (hp : p.wf N bv)
    {R : List Region} (hR : RegOK R) {σ σ' : BState} (hex : BExec p σ σ') {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (compileBF N bv p)) (hok : codeOK pc (compileBF N bv p).length)
    (hf : FrOK N (frameBase N (getX s 2))) (hfd : ∀ r ∈ R, disjoint ⟨frameBase N (getX s 2), 8 * (N + 1)⟩ r)
    (hcd : ∀ r ∈ (⟨frameBase N (getX s 2), 8 * (N + 1)⟩ : Region) :: R,
      disjoint ⟨pc.toNat, 4 * (compileBF N bv p).length⟩ r)
    (hreg : ∀ i : Fin 8, getX s (A8 i) = σ.env i.val) (hslot : ∀ j < N, σ.env (8 + j) = 0)
    (hheap : HeapRel bv R σ s) (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ (∀ i : Fin 8, getX s' (A8 i) = σ'.env i.val) ∧
      HeapRel bv R σ' s' ∧ unchangedOutside s s' ((⟨frameBase N (getX s 2), 8 * (N + 1)⟩ : Region) :: R) ∧
      Cfg s' ∧ calleeSavedKept s s' ∧ getX s' 3 = getX s 3 := by
  have hsp : 8 * (N + 1) ≤ (getX s 2).toNat / 8 * 8 := by have := hf.lo; unfold frameBase at this; omega
  generalize hfp : frameBase N (getX s 2) = fp at *
  simp only [compileBF] at hc hok hcd
  rw [codeAt_append, codeAt_append] at hc
  rw [List.length_append, List.length_append] at hok hcd
  obtain ⟨ok12, ok3⟩ := codeOK_append hok
  obtain ⟨ok1, ok2⟩ := codeOK_append ok12
  have hcF := hcd _ (List.mem_cons_self ..)
  have hcR : ∀ r ∈ R, disjoint ⟨pc.toNat, 4 * ((prologue N).length + (compileB bv p).length + [iLdGp, iRet].length)⟩ r :=
    fun r hr => hcd r (List.mem_cons_of_mem _ hr)
  -- prologue
  obtain ⟨s₁, r₁, h₁, pc₁, u₁, k₁, g₁, sv₁, z₁⟩ := prologue_ok h hpc hc.1.1 ok1 (by rw [hfp]; exact hf) hsp
    (by rw [hfp]; unfold disjoint at hcF ⊢; dsimp only at hcF ⊢; omega)
  rw [hfp] at u₁ g₁ sv₁ z₁
  have hRR := RegOK_frame hf hR hfd
  have hrel₁ : Rel2 N fp bv R σ s₁ := by
    refine ⟨⟨fun i => ?_, g₁, fun j hj => by rw [z₁ j hj, hslot j hj]⟩,
      ⟨hheap.hlen, hheap.bvlen, hheap.base, hheap.blen, fun b hb => ?_⟩⟩
    · rw [k₁ _ (fun k hk => A8_ne_T i k hk) (A8_ne_3 i), hreg]
    · rw [bytesAt_out u₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; have := hfd _ (List.getElem_mem hb)
        unfold disjoint at this ⊢; dsimp only at this ⊢; omega), hheap.bytes b hb]
  have hF1 : ∀ r ∈ [(⟨fp, 8 * (N + 1)⟩ : Region)], disjoint ⟨pc.toNat, 4 * ((prologue N).length +
      (compileB bv p).length + [iLdGp, iRet].length)⟩ r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hcF
  have e1 := pc_toNat hok (a := (prologue N).length) (by omega)
  have e2 := pc_toNat hok (a := (prologue N).length + (compileB bv p).length) (by omega)
  -- body
  have hcb : codeAt s₁ (pc + BitVec.ofNat 64 (4 * (prologue N).length)) (compileB bv p) :=
    codeAt_out hc.1.2 ok2 (disj_sub hF1 (by omega) (by omega)) u₁
  have hslotIn : ∀ r ∈ slotRegs N fp, r.base ≥ fp ∧ r.base + r.len ≤ fp + 8 * (N + 1) ∧ fp + 8 ≤ r.base := by
    intro r hr; obtain ⟨j, hj, rfl⟩ := slotRegs_mem hr; dsimp only; omega
  have hcdB : ∀ r ∈ R ++ slotRegs N fp, disjoint ⟨(pc + BitVec.ofNat 64 (4 * (prologue N).length)).toNat,
      4 * (compileB bv p).length⟩ r := by
    intro r hr; rw [e1]
    rcases List.mem_append.mp hr with hr | hr
    · have := hcR r hr; unfold disjoint at this ⊢; dsimp only at this ⊢; omega
    · have := hslotIn r hr; unfold disjoint at hcF ⊢; dsimp only at hcF ⊢; omega
  obtain ⟨s₂, r₂, F₂, pc₂, v₂⟩ := execB_ok hf bv hbv hRR hex hp h₁ pc₁ hcb ok2 hcdB hrel₁
  rw [pc_add] at pc₂
  -- epilogue: ld gp, 0(gp); ret
  have hout : ∀ r ∈ R ++ slotRegs N fp, disjoint ⟨fp, 8⟩ r := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · have := hfd r hr; unfold disjoint at this ⊢; dsimp only at this ⊢; omega
    · have := hslotIn r hr; unfold disjoint; dsimp only; omega
  have hFR : ∀ r ∈ R ++ slotRegs N fp, disjoint ⟨pc.toNat, 4 * ((prologue N).length +
      (compileB bv p).length + [iLdGp, iRet].length)⟩ r := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hcR r hr
    · have := hslotIn r hr; unfold disjoint at hcF ⊢; dsimp only at hcF ⊢; omega
  have hc3 : codeAt s₂ (pc + BitVec.ofNat 64 (4 * ((prologue N).length + (compileB bv p).length))) [iLdGp, iRet] :=
    codeAt_out (codeAt_out (by have := hc.2; rwa [List.length_append] at this) ok3 (disj_sub hF1 (by omega) (by omega)) u₁) ok3
      (disj_sub hFR (by omega) (by omega)) F₂.out
  have g₂ := v₂.env.gp
  have hfpn : (BitVec.ofNat 64 fp).toNat = fp := toNat_ofNat' (by have := hf.hi; omega)
  obtain ⟨s₃, n₃⟩ := step_ldGp F₂.cfg pc₂ (codeOK_pcOK ok3 (by simp)) (by simpa using hc3 0 (by simp))
    (by rw [g₂, hfpn]; have := hf.hi; have := hf.lo; omega) (by rw [g₂, hfpn]; exact hf.al)
    (v := getX s 3) (by rw [g₂, hfpn, bytesAt_out F₂.out hout, sv₁])
  have hra₂ : getX s₂ 1 = getX s 1 := by
    rw [F₂.keep 1 (by decide) (by decide), k₁ 1 (by decide) (by decide)]
  have hra₃ : getX s₃ 1 = getX s 1 := by rw [n₃.x, if_neg (by decide), hra₂]
  obtain ⟨s₄, n₄⟩ := step_ret n₃.cfg (by rw [n₃.pc, pc4, pc_add]) (codeOK_pcOK (codeOK_append (a := 1) (b := 1) ok3).2 (by simp))
    (by simpa using (codeAt_mem n₃.mem hc3) 1 (by simp)) (by rw [hra₃]; exact hra)
  refine runsTo_of_reach (((r₁.trans r₂).trans (Reach.next n₃)).trans (Reach.next n₄))
    ⟨by rw [n₄.pc, hra₃], fun i => ?_, ⟨v₂.heap.hlen, v₂.heap.bvlen, v₂.heap.base, v₂.heap.blen, fun b hb => ?_⟩,
      fun a ha => ?_, n₄.cfg, calleeSaved_of_keepB h n₄.cfg fun j h1 h2 h3 => ?_, ?_⟩
  · rw [n₄.keep0, n₃.x, if_neg (fun h => A8_ne_3 i h.1)]; exact v₂.env.reg i
  · rw [bytesAt_mem (s' := s₄) (s := s₂) (by rw [n₄.mem, n₃.mem]), v₂.heap.bytes b hb]
  · rw [n₄.mem, n₃.mem]
    have hF := ha _ (List.mem_cons_self ..); dsimp only at hF
    rw [F₂.out a fun r hr => ?_, u₁ a fun r hr => ?_]
    · simp only [List.mem_singleton] at hr; subst hr; exact hF
    · rcases List.mem_append.mp hr with hr | hr
      · exact ha r (List.mem_cons_of_mem _ hr)
      · have := hslotIn r hr; omega
  · rw [n₄.keep0, n₃.x, if_neg (fun h => h3 h.1), F₂.keep j h1 h2, k₁ j h1 h3]
  · rw [n₄.keep0, n₃.x, if_pos ⟨rfl, by decide⟩]

end Proven
