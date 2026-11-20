/- The ARM adapter `armTarget M` over ANY machine `M` with the abstract A64 steps `A64Sem M` (Machine/A64Sem.lean).
Words: O's `ArmEnc.blk` (rv2arm's blocks, 4 words per J instruction); registers `armReg` (π); scratch x16, x17;
link width 16 (`Rel.ww`: wk = 3).  `lay` = the generic layout ∧ rv2arm's validation `progOK`.

PROOF NOTES (per J kind: block, relation, lemmas) — Testing/nano/v2self/arm/PROOF_NOTES.md; here:
* `Mid K C s0 p k s`: `Rel` with the pc at word `k` of block `p.1` (base + 16·p.1 + 4·k).  `Rel ↔ Mid _ 0`.
* `mid_regs`: an instruction that keeps memory, writes registers only in π's image of the J registers it changes
  and in the scratch registers, and moves the pc, keeps `Mid` (for the new J state).
* per block: the words from `Mid.word`, the A64Sem fields in sequence, `mid_regs` after each. -/
import Nano.V2Self.Proof.Machine.A64Sem
import Nano.V2Self.Proof.Machine.HostOn
namespace JT
open Proven.Top SimW CallProbe ArmEnc

/-- **the ARM target** over a machine `M` -/
def armTarget (M : Machine) : JTarget where
  M := M
  blockLen := 4
  enc := blk
  reg := armReg
  scratch := armScratch
  lay K C := JTarget.LayOK M (16 * C.length) K ∧ progOK C = true
  m0 s a := ((M.observe s).memory (UInt64.ofNat a)).map UInt8.toBitVec
  inv _ _ := True
  words _ := []
  valid C := progOK C = true

variable {M : Machine}

/-! ## registers -/

theorem mapped_iff {r : Nat} : mapped r = true ↔ r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 10 ∨
    r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 ∨ r = 28 ∨ r = 29 ∨ r = 30 ∨ r = 31 := by
  simp [mapped]

theorem armReg_lt {r : Nat} (h : mapped r = true) (h0 : r ≠ 0) : armReg r < 31 := by
  rcases mapped_iff.1 h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> first | decide | exact absurd rfl h0

/-- π is injective on the mapped registers -/
theorem armReg_inj {r j : Nat} (hr : mapped r = true) (hj : j < 32) (h : armReg j = armReg r) : j = r := by
  rcases mapped_iff.1 hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> revert h <;> revert hj <;> revert j <;> decide

theorem body_len (j : J) : (body j).length ≤ 4 := by
  cases j <;> simp only [body, zpre, compBr] <;> (repeat' split) <;> simp

theorem blockJ_len (j : J) : (blockJ j).length = 4 := by
  have := body_len j; simp [blockJ, pad4]; omega

theorem blk_len (j : J) : (blk j).length = 4 := by simp [blk, blockJ_len]

/-! ## the mid-block relation -/

/-- `Rel` with the pc at word `k` of block `p.1` -/
structure Mid (K : LayW) (C : List J) (s0 : M.State) (p : Nat × CallProbe.St) (k : Nat) (s : M.State) : Prop where
  cfg : M.configured s
  pc : (M.observe s).programCounter = UInt64.ofNat (K.base + 16 * p.1 + 4 * k)
  code : ∀ i (h : i < C.length) k' (hk : k' < (blk C[i]).length) b, b < 4 →
    (M.observe s).memory (UInt64.ofNat (K.base + 4 * 4 * i + 4 * k' + b)) = some (wbyte (blk C[i])[k'] b)
  x0 : p.2.x 0 = 0
  bb : p.2.b = K.base
  ww : p.2.wk = 3
  x : ∀ j, 0 < j → j < 32 → (M.observe s).register (armReg j) = p.2.x j
  keep : ∀ r, (∀ j, 0 < j → j < 32 → armReg j ≠ r) → r ∉ armScratch →
    (M.observe s).register r = (M.observe s0).register r
  w : ∀ a, wok K a → ∀ k < 8, (M.observe s).memory (UInt64.ofNat (a + k)) = some (cbyte (p.2.m a) k)
  bw : ∀ a, io K a → (M.observe s).memory (UInt64.ofNat a) = some (cbyte (p.2.m (a - a % 8)) (a % 8))
  fr : ∀ a, a < 2 ^ 64 → ¬ wok K (a - a % 8) → ¬ outB K a →
    (M.observe s).memory (UInt64.ofNat a) = (K.m0 a).map UInt8.ofBitVec

theorem mid_of_rel {K : LayW} {C : List J} {s0 s : M.State} {p : Nat × CallProbe.St}
    (h : (armTarget M).Rel K C s0 p s) : Mid K C s0 p 0 s :=
  ⟨h.cfg, by have := h.pc; simp only [JTarget.addr, armTarget] at this; rw [this]; congr 1, h.code, h.x0, h.bb, h.ww, h.x, h.keep, h.w, h.bw, h.fr⟩

theorem rel_of_mid {K : LayW} {C : List J} {s0 s : M.State} {p : Nat × CallProbe.St}
    (h : Mid K C s0 p 0 s) : (armTarget M).Rel K C s0 p s :=
  ⟨h.cfg, by show (M.observe s).programCounter = _; rw [h.pc]; simp only [JTarget.addr, armTarget]; congr 1, h.code, h.x0, h.bb, h.ww, h.x, h.keep, h.w, h.bw, h.fr,
    trivial⟩

/-- an instruction that keeps memory and writes only the registers of the J registers it changes (and scratch) -/
theorem mid_regs {K : LayW} {C : List J} {s0 s s' : M.State} {p : Nat × CallProbe.St} {k : Nat}
    (hM : Mid K C s0 p k s) {st' : CallProbe.St} {pc' k' : Nat} (hcfg : M.configured s')
    (hpc : (M.observe s').programCounter = UInt64.ofNat (K.base + 16 * pc' + 4 * k'))
    (hmem : (M.observe s').memory = (M.observe s).memory)
    (hx : ∀ j, 0 < j → j < 32 → (M.observe s').register (armReg j) = st'.x j)
    (hkeep : ∀ r, (∀ j, 0 < j → j < 32 → armReg j ≠ r) → r ∉ armScratch →
      (M.observe s').register r = (M.observe s).register r)
    (h0 : st'.x 0 = 0) (hb : st'.b = p.2.b) (hw : st'.wk = p.2.wk) (hm : st'.m = p.2.m) :
    Mid K C s0 (pc', st') k' s' where
  cfg := hcfg
  pc := hpc
  code := fun i h k hk b hb => by rw [hmem]; exact hM.code i h k hk b hb
  x0 := h0
  bb := by rw [hb]; exact hM.bb
  ww := by rw [hw]; exact hM.ww
  x := hx
  keep := fun r h1 h2 => by rw [hkeep r h1 h2]; exact hM.keep r h1 h2
  w := fun a ha k hk => by rw [hmem, hm]; exact hM.w a ha k hk
  bw := fun a ha => by rw [hmem, hm]; exact hM.bw a ha
  fr := fun a ha h1 h2 => by rw [hmem]; exact hM.fr a ha h1 h2

theorem ofNat_add4 (a : Nat) : UInt64.ofNat a + 4 = UInt64.ofNat (a + 4) := by
  apply UInt64.toNat_inj.1; simp [UInt64.toNat_add]

theorem armReg_ne_scr {j : Nat} : armReg j ≠ 16 ∧ armReg j ≠ 17 := by
  unfold armReg; split <;> decide

/-- a scratch write (x16 / x17) that falls through: the J state is unchanged -/
theorem mid_scr {K : LayW} {C : List J} {s0 s : M.State} {p : Nat × CallProbe.St} {k : Nat}
    (hM : Mid K C s0 p k s) {d : Nat} (hd : d = 16 ∨ d = 17) {v : UInt64}
    (hg : Goes M s (setReg (M.observe s) d v)) : ∃ s', Runs M s s' ∧ Mid K C s0 p (k + 1) s' := by
  obtain ⟨s', r, c, o⟩ := hg
  refine ⟨s', r, mid_regs hM c (by rw [o]; simp only [setReg]; rw [hM.pc, ofNat_add4]; congr 1)
    (by rw [o]; rfl) (fun j h0 h32 => ?_) (fun r' _ hr => ?_) hM.x0 rfl rfl rfl⟩
  · rw [o]; simp only [setReg]
    have := @armReg_ne_scr j
    rw [if_neg (by omega)]; exact hM.x j h0 h32
  · rw [o]; simp only [setReg]
    rw [if_neg (by intro e; subst e; simp [armScratch] at hr; omega)]

/-- a write of a J register `rd` (≠ x0, mapped) with J's new value, falling through -/
theorem mid_set {K : LayW} {C : List J} {s0 s : M.State} {p : Nat × CallProbe.St} {k : Nat}
    (hM : Mid K C s0 p k s) {rd : Nat} (hrd : mapped rd = true) (h0 : rd ≠ 0) {v : UInt64}
    (hg : Goes M s (setReg (M.observe s) (armReg rd) v)) :
    ∃ s', Runs M s s' ∧ Mid K C s0 (p.1, CallProbe.wr p.2 rd v) (k + 1) s' := by
  obtain ⟨s', r, c, o⟩ := hg
  refine ⟨s', r, mid_regs hM c (by rw [o]; simp only [setReg]; rw [hM.pc, ofNat_add4]; congr 1)
    (by rw [o]; rfl) (fun j hj0 h32 => ?_) (fun r' hr _ => ?_) ?_ ?_ ?_ ?_⟩
  · rw [o]; simp only [setReg]
    by_cases e : j = rd
    · subst e; simp [CallProbe.wr, h0, CallProbe.upd]
    · rw [if_neg (fun q => e (armReg_inj hrd h32 q)), hM.x j hj0 h32]
      simp [CallProbe.wr, h0, CallProbe.upd, e]
  · rw [o]; simp only [setReg]
    have hlt : rd < 32 := by rcases mapped_iff.1 hrd with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
    rw [if_neg (fun q => hr rd (by omega) hlt q.symm)]
  · simp [CallProbe.wr, h0, CallProbe.upd, hM.x0]; omega
  · exact CallProbe.wr_b _ _ _
  · exact CallProbe.wr_w _ _ _
  · simp [CallProbe.wr, h0]

/-! ## fetching the block's words -/

theorem mid_word {K : LayW} {C : List J} {s0 s : M.State} {p : Nat × CallProbe.St} {k : Nat}
    (hM : Mid K C s0 p k s) {j : J} (hC : C[p.1]? = some j) (i : Nat) (hi : i < 4) :
    WordAt (M.observe s) (K.base + 16 * p.1 + 4 * i) ((blockJ j).getD i 0) := by
  intro b hb
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 hC
  have := hM.code p.1 hlt i (by rw [blk_len]; exact hi) b hb
  rw [show K.base + 4 * 4 * p.1 + 4 * i + b = K.base + 16 * p.1 + 4 * i + b by omega] at this
  rw [this]; congr 2
  simp only [blk, heq, List.getElem_map]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [blockJ_len]; exact hi)]; rfl

/-- the pc as a number, below 2^64 -/
theorem mid_pcN {K : LayW} {C : List J} {s0 s : M.State} {p : Nat × CallProbe.St} {k : Nat}
    (hM : Mid K C s0 p k s) (hb : K.base + 16 * p.1 + 4 * k < 2 ^ 64) :
    (M.observe s).programCounter.toNat = K.base + 16 * p.1 + 4 * k := by
  rw [hM.pc]; simp; omega

theorem ofInt_toNat' (f : Int) : (UInt64.ofInt f).toNat = (f % 2 ^ 64).toNat := by
  simp [UInt64.ofInt]; omega

/-- a branch offset `f` words from the pc -/
theorem ofNat_addInt (a : Nat) (f : Int) (h : 0 ≤ (a : Int) + 4 * f) (h2 : (a : Int) + 4 * f < 2 ^ 64) :
    UInt64.ofNat a + 4 * UInt64.ofInt f = UInt64.ofNat ((a : Int) + 4 * f).toNat := by
  apply UInt64.toNat_inj.1
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', ofInt_toNat']
  simp; omega

end JT
