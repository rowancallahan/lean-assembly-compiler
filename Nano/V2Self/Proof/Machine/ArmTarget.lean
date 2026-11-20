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
import Nano.V2Self.Proof.Machine.StartCode
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
    (hg : Goes M s (setReg (M.observe s) d v)) :
    ∃ s', Runs M s s' ∧ Mid K C s0 p (k + 1) s' ∧ M.observe s' = setReg (M.observe s) d v := by
  obtain ⟨s', r, c, o⟩ := hg
  refine ⟨s', r, ?_, o⟩
  refine (mid_regs hM c (by rw [o]; simp only [setReg]; rw [hM.pc, ofNat_add4]; congr 1)
    (by rw [o]; rfl) (fun j h0 h32 => ?_) (fun r' _ hr => ?_) hM.x0 rfl rfl rfl)
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

/-! ## common block steps -/

theorem mid_next {K : LayW} {C : List J} {s0 s : M.State} {p : Nat × CallProbe.St}
    (hM : Mid K C s0 p 4 s) : Mid K C s0 (p.1 + 1, p.2) 0 s :=
  { hM with pc := by rw [hM.pc]; congr 1 }

/-- the remaining words `k..3` of the block are PAD: fall through to the next block -/
theorem run_pads (S : A64Sem M) {K : LayW} {C : List J} {s0 : M.State} {p : Nat × CallProbe.St} {j : J}
    (hC : C[p.1]? = some j) (hB : K.base + 16 * C.length ≤ 2 ^ 32) (hpcl : p.1 < C.length) :
    ∀ n k (s : M.State), k + n = 4 → Mid K C s0 p k s → (∀ i, k ≤ i → i < 4 → (blockJ j).getD i 0 = PAD) →
      ∃ s', Runs M s s' ∧ Mid K C s0 (p.1 + 1, p.2) 0 s'
  | 0, k, s, hk, hM, _ => ⟨s, .stop, mid_next (by rw [show k = 4 by omega] at hM; exact hM)⟩
  | n + 1, k, s, hk, hM, hpad => by
    have hw := mid_word hM hC k (by omega)
    rw [hpad k (Nat.le_refl _) (by omega), ← mid_pcN hM (by omega)] at hw
    obtain ⟨s1, r1, M1, -⟩ := mid_scr hM (Or.inl rfl) (S.addi s 16 16 0 hM.cfg (by decide) (by decide) (by decide) hw)
    obtain ⟨s2, r2, M2⟩ := run_pads S hC hB hpcl n (k + 1) s1 (by omega) M1 (fun i h1 h2 => hpad i (by omega) h2)
    exact ⟨s2, Runs.trans r1 r2, M2⟩

/-- a jump that changes no register, to block `pc'` -/
theorem mid_jump {K : LayW} {C : List J} {s0 s : M.State} {p : Nat × CallProbe.St} {k : Nat}
    (hM : Mid K C s0 p k s) {pc' : Nat} (hg : Goes M s (jumpTo (M.observe s) (UInt64.ofNat (K.base + 16 * pc')))) :
    ∃ s', Runs M s s' ∧ Mid K C s0 (pc', p.2) 0 s' := by
  obtain ⟨s', r, c, o⟩ := hg
  exact ⟨s', r, mid_regs hM c (by rw [o]; rfl) (by rw [o]; rfl) (fun j h0 h32 => by rw [o]; exact hM.x j h0 h32)
    (fun r' _ _ => by rw [o]; rfl) hM.x0 rfl rfl rfl⟩

/-- PAD words `k..k+n−1` inside the block -/
theorem pads_mid (S : A64Sem M) {K : LayW} {C : List J} {s0 : M.State} {p : Nat × CallProbe.St} {j : J}
    (hC : C[p.1]? = some j) (hB : K.base + 16 * C.length ≤ 2 ^ 32) (hpcl : p.1 < C.length) :
    ∀ n k (s : M.State), k + n ≤ 4 → Mid K C s0 p k s → (∀ i, k ≤ i → i < k + n → (blockJ j).getD i 0 = PAD) →
      ∃ s', Runs M s s' ∧ Mid K C s0 p (k + n) s'
  | 0, k, s, _, hM, _ => ⟨s, .stop, hM⟩
  | n + 1, k, s, hk, hM, hpad => by
    have hw := mid_word hM hC k (by omega)
    rw [hpad k (Nat.le_refl _) (by omega), ← mid_pcN hM (by omega)] at hw
    obtain ⟨s1, r1, M1, -⟩ := mid_scr hM (Or.inl rfl) (S.addi s 16 16 0 hM.cfg (by decide) (by decide) (by decide) hw)
    obtain ⟨s2, r2, M2⟩ := pads_mid S hC hB hpcl n (k + 1) s1 (by omega) M1 (fun i h1 h2 => hpad i (by omega) (by omega))
    exact ⟨s2, Runs.trans r1 r2, by rw [show k + (n + 1) = k + 1 + n by omega]; exact M2⟩

/-- the word `i` of the block at the pc (word `i` = the current one) -/
theorem word_pc {K : LayW} {C : List J} {s0 s : M.State} {p : Nat × CallProbe.St} {k : Nat} {j : J}
    (hM : Mid K C s0 p k s) (hC : C[p.1]? = some j) (hB : K.base + 16 * C.length ≤ 2 ^ 32) (hpcl : p.1 < C.length)
    (hk : k < 4) {w : Nat} (hw : (blockJ j).getD k 0 = w) :
    WordAt (M.observe s) (M.observe s).programCounter.toNat w := by
  rw [mid_pcN hM (by omega), ← hw]; exact mid_word hM hC k hk

/-! ## the blocks, one per J kind -/

/-- `jal x0, o`: `b 4o` -/
theorem blk_jal0 (S : A64Sem M) {K : LayW} {C : List J} {s0 s : M.State} {pc : Nat} {st : CallProbe.St} {o : Int}
    (hM : Mid K C s0 (pc, st) 0 s) (hC : C[pc]? = some (.jal 0 o)) (hB : K.base + 16 * C.length ≤ 2 ^ 32)
    (hpcl : pc < C.length) (h1 : -2 ^ 18 ≤ o) (h2 : o < 2 ^ 18) (h3 : 0 ≤ (pc : Int) + o) (h4 : (pc : Int) + o < C.length) :
    ∃ s', Runs M s s' ∧ Mid K C s0 (((pc : Int) + o).toNat, st) 0 s' := by
  have hw := mid_word hM hC 0 (by decide)
  simp only [blockJ, body, pad4, if_true] at hw
  rw [show K.base + 16 * pc + 4 * 0 = K.base + 16 * pc + 4 * 0 from rfl, ← mid_pcN hM (by omega)] at hw
  have g := S.b s (4 * o) hM.cfg (by omega) (by omega) (by simpa using hw)
  rw [hM.pc, show K.base + 16 * pc + 4 * 0 = K.base + 16 * pc by omega, ofNat_addInt _ _ (by omega) (by omega),
    show ((K.base + 16 * pc : Nat) + 4 * (4 * o) : Int).toNat = K.base + 16 * ((pc : Int) + o).toNat by omega] at g
  exact mid_jump hM g

/-- `jal x1, o`: `PAD; PAD; PAD; bl 4o−3` (x30 := the next block = J's link, w = 16) -/
theorem blk_jal1 (S : A64Sem M) {K : LayW} {C : List J} {s0 s : M.State} {pc : Nat} {st : CallProbe.St} {o : Int}
    (hM : Mid K C s0 (pc, st) 0 s) (hC : C[pc]? = some (.jal 1 o)) (hB : K.base + 16 * C.length ≤ 2 ^ 32)
    (hpcl : pc < C.length) (h1 : -2 ^ 18 ≤ o) (h2 : o < 2 ^ 18) (h3 : 0 ≤ (pc : Int) + o) (h4 : (pc : Int) + o < C.length) :
    ∃ s', Runs M s s' ∧ Mid K C s0 (((pc : Int) + o).toNat,
      CallProbe.wr st 1 (UInt64.ofNat (st.b + st.w * (pc + 1)))) 0 s' := by
  have hb : blockJ (.jal 1 o) = [PAD, PAD, PAD, blB (4 * o - 3)] := by simp [blockJ, body, pad4]
  obtain ⟨s1, r1, M1⟩ := pads_mid S (p := (pc, st)) hC hB hpcl 3 0 s (by decide) hM
    (fun i _ hi => by rw [hb]; rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> rfl)
  have hw := word_pc M1 hC hB hpcl (by decide) (w := blB (4 * o - 3)) (by rw [hb]; rfl)
  obtain ⟨s2, r2, c2, o2⟩ := S.bl s1 (4 * o - 3) M1.cfg (by omega) (by omega) hw
  have hw16 : st.w = 16 := by unfold CallProbe.St.w; rw [M1.ww]
  have hpc1 := M1.pc
  refine ⟨s2, Runs.trans r1 r2, mid_regs M1 c2 ?_ (by rw [o2]) (fun j h0 h32 => ?_) (fun r hr _ => ?_) ?_ ?_ ?_ ?_⟩
  · rw [o2]; dsimp only; rw [hpc1, ofNat_addInt _ _ (by omega) (by omega)]; congr 1; omega
  · rw [o2]; dsimp only
    by_cases e : j = 1
    · subst e
      rw [if_pos (show armReg 1 = 30 from rfl), hpc1, ofNat_add4, CallProbe.wr, if_neg (by decide)]; dsimp only
      rw [CallProbe.upd_same, hw16, M1.bb]; congr 1
    · rw [if_neg (show ¬ armReg j = 30 from fun q => e (armReg_inj (r := 1) rfl h32 q)), M1.x j h0 h32]
      simp [CallProbe.wr, CallProbe.upd, e]
  · rw [o2]; dsimp only; rw [if_neg (fun q => hr 1 (by decide) (by decide) q.symm)]
  · simpa [CallProbe.wr, CallProbe.upd] using M1.x0
  · exact CallProbe.wr_b _ _ _
  · exact CallProbe.wr_w _ _ _
  · simp [CallProbe.wr]

/-- `jalr x0, r`: `br π r` (the target is a block start: SafeX gives x = base + 16·j) -/
theorem blk_jalr (S : A64Sem M) {K : LayW} {C : List J} {s0 s : M.State} {pc : Nat} {st : CallProbe.St} {rd rs : Nat}
    (hM : Mid K C s0 (pc, st) 0 s) (hC : C[pc]? = some (.jalr rd rs)) (hB : K.base + 16 * C.length ≤ 2 ^ 32)
    (hpcl : pc < C.length) (hrs0 : rs ≠ 0) (hrs : rs < 32) (hlt : armReg rs < 31) {jt : Nat}
    (hj : (st.x rs).toNat = K.base + st.w * jt) :
    ∃ s', Runs M s s' ∧ Mid K C s0 (((st.x rs).toNat - st.b) / st.w, st) 0 s' := by
  have hw := word_pc hM hC hB hpcl (by decide) (w := brR (armReg rs)) (by simp [blockJ, body, pad4])
  have g := S.br s (armReg rs) hM.cfg hlt hw
  have hw16 : st.w = 16 := by unfold CallProbe.St.w; rw [hM.ww]
  have e : ((st.x rs).toNat - st.b) / st.w = jt := by rw [hj, hM.bb, hw16]; omega
  rw [hM.x rs (by omega) hrs, ← @UInt64.ofNat_toNat (st.x rs), hj, hw16] at g
  rw [e]; exact mid_jump hM g

theorem mapped_lt {r : Nat} (h : mapped r = true) : r < 32 := by
  rcases mapped_iff.1 h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

/-- an operand register: x0 is read from x17 (= 0) -/
theorem opR_val {K : LayW} {C : List J} {s0 s : M.State} {pc k : Nat} {st : CallProbe.St}
    (hM : Mid K C s0 (pc, st) k s) {r : Nat} (hr : mapped r = true)
    (h17 : r = 0 → (M.observe s).register 17 = 0) : (M.observe s).register (opR r) = st.x r := by
  unfold opR; split
  · rename_i h; subst h; rw [h17 rfl, hM.x0]
  · rename_i h; exact hM.x r (by omega) (mapped_lt hr)

theorem opR_lt {r : Nat} (hr : mapped r = true) : opR r < 31 := by
  unfold opR; split
  · decide
  · rename_i h; exact armReg_lt hr h

/-- `subs x16, xn, xm; b.cond (4o − 1 − k)` at words k, k+1 of the block, then PADs -/
theorem cmp_tail (S : A64Sem M) {K : LayW} {C : List J} {s0 s : M.State} {pc k : Nat} {st : CallProbe.St} {j : J}
    (hM : Mid K C s0 (pc, st) k s) (hk : k ≤ 1) (hC : C[pc]? = some j) (hB : K.base + 16 * C.length ≤ 2 ^ 32)
    (hpcl : pc < C.length) {c n m a b : Nat} {o : Int} (hc : c < 4) (hn : n < 31) (hm : m < 31)
    (hwS : (blockJ j).getD k 0 = subsR n m) (hwB : (blockJ j).getD (k + 1) 0 = bc c (4 * o - 1 - k))
    (hpad : ∀ i, k + 2 ≤ i → i < 4 → (blockJ j).getD i 0 = PAD)
    (vn : (M.observe s).register n = st.x a) (vm : (M.observe s).register m = st.x b)
    (h1 : -65535 ≤ o) (h2 : o ≤ 65535) (h3 : 0 ≤ (pc : Int) + o) (h4 : (pc : Int) + o < C.length) :
    ∃ s', Runs M s s' ∧
      Mid K C s0 (if condV c (st.x a) (st.x b) = true then ((pc : Int) + o).toNat else pc + 1, st) 0 s' := by
  have w1 := word_pc hM hC hB hpcl (by omega) hwS
  have w2 := mid_word hM hC (k + 1) (by omega)
  rw [hwB, show K.base + 16 * pc + 4 * (k + 1) = (M.observe s).programCounter.toNat + 4 by
    rw [mid_pcN hM (by omega)]; omega] at w2
  have g := S.cmpbr s c n m (4 * o - 1 - k) hM.cfg hc hn hm (by omega) (by omega) w1 w2
  rw [vn, vm] at g
  obtain ⟨s2, r2, c2, o2⟩ := g
  have hpcA := hM.pc
  have hx : ∀ j, 0 < j → j < 32 → (M.observe s2).register (armReg j) = st.x j := fun j h0 h32 => by
    rw [o2]; dsimp only; rw [if_neg (by have := @armReg_ne_scr j; omega)]; exact hM.x j h0 h32
  have hkeep : ∀ r, (∀ j, 0 < j → j < 32 → armReg j ≠ r) → r ∉ armScratch →
      (M.observe s2).register r = (M.observe s).register r := fun r _ hr => by
    rw [o2]; dsimp only; rw [if_neg (by intro e; subst e; simp [armScratch] at hr)]
  by_cases hcond : condV c (st.x a) (st.x b) = true
  · rw [if_pos hcond]
    refine ⟨s2, r2, mid_regs hM c2 ?_ (by rw [o2]) hx hkeep hM.x0 rfl rfl rfl⟩
    rw [o2]; dsimp only
    rw [if_pos hcond, hpcA, ofNat_add4, ofNat_addInt _ _ (by omega) (by omega)]; congr 1; omega
  · rw [if_neg hcond]
    have M2 : Mid K C s0 (pc, st) (k + 2) s2 := by
      refine mid_regs hM c2 ?_ (by rw [o2]) hx hkeep hM.x0 rfl rfl rfl
      rw [o2]; dsimp only; rw [if_neg hcond, hpcA]; apply UInt64.toNat_inj.1; simp; omega
    obtain ⟨s3, r3, M3⟩ := run_pads S hC hB hpcl (4 - (k + 2)) (k + 2) s2 (by omega) M2 hpad
    exact ⟨s3, Runs.trans r2 r3, M3⟩

/-- the compare-branch block `compBr c a b o` (with `movz x17, #0` first when an operand is x0) -/
theorem blk_cmp (S : A64Sem M) {K : LayW} {C : List J} {s0 s : M.State} {pc : Nat} {st : CallProbe.St} {j : J}
    (hM : Mid K C s0 (pc, st) 0 s) (hC : C[pc]? = some j) (hB : K.base + 16 * C.length ≤ 2 ^ 32)
    (hpcl : pc < C.length) {c a b : Nat} {o : Int} (hc : c < 4) (ha : mapped a = true) (hb : mapped b = true)
    (hblk : blockJ j = pad4 (compBr c a b o))
    (h1 : -65535 ≤ o) (h2 : o ≤ 65535) (h3 : 0 ≤ (pc : Int) + o) (h4 : (pc : Int) + o < C.length) :
    ∃ s', Runs M s s' ∧
      Mid K C s0 (if condV c (st.x a) (st.x b) = true then ((pc : Int) + o).toNat else pc + 1, st) 0 s' := by
  unfold compBr at hblk
  by_cases hz : a = 0 ∨ b = 0
  · rw [if_pos hz] at hblk
    have w0 := word_pc hM hC hB hpcl (by decide) (w := movz 17 0) (by rw [hblk]; rfl)
    obtain ⟨s1, r1, M1, o1⟩ := mid_scr hM (Or.inr rfl) (S.movz s 17 0 hM.cfg (by decide) (by decide) w0)
    have r17 : (M.observe s1).register 17 = 0 := by rw [o1]; simp [setReg]
    obtain ⟨s2, r2, M2⟩ := cmp_tail S M1 (Nat.le_refl _) hC hB hpcl hc (opR_lt ha) (opR_lt hb)
      (by rw [hblk]; rfl) (by rw [hblk]; show bc c (4 * o - 2) = _; congr 1; omega)
      (fun i h1 h2 => by rw [show i = 3 by omega, hblk]; rfl)
      (opR_val M1 ha (fun _ => r17)) (opR_val M1 hb (fun _ => r17)) h1 h2 h3 h4
    exact ⟨s2, Runs.trans r1 r2, M2⟩
  · rw [if_neg hz] at hblk
    have a0 : a ≠ 0 := fun e => hz (Or.inl e)
    have b0 : b ≠ 0 := fun e => hz (Or.inr e)
    exact cmp_tail S hM (Nat.zero_le _) hC hB hpcl hc (armReg_lt ha a0) (armReg_lt hb b0)
      (by rw [hblk]; rfl) (by rw [hblk]; show bc c (4 * o - 1) = _; congr 1; omega)
      (fun i h1 h2 => by rcases (by omega : i = 2 ∨ i = 3) with rfl | rfl <;> rw [hblk] <;> rfl)
      (hM.x a (by omega) (mapped_lt ha)) (hM.x b (by omega) (mapped_lt hb)) h1 h2 h3 h4

/-- `cbz xt, 4o` (a J `beq` against x0), then PADs -/
theorem blk_cbz (S : A64Sem M) {K : LayW} {C : List J} {s0 s : M.State} {pc : Nat} {st : CallProbe.St} {j : J}
    (hM : Mid K C s0 (pc, st) 0 s) (hC : C[pc]? = some j) (hB : K.base + 16 * C.length ≤ 2 ^ 32)
    (hpcl : pc < C.length) {a : Nat} {o : Int} (ha : mapped a = true) (a0 : a ≠ 0)
    (hblk : blockJ j = [cbz (armReg a) (4 * o), PAD, PAD, PAD])
    (h1 : -65535 ≤ o) (h2 : o ≤ 65535) (h3 : 0 ≤ (pc : Int) + o) (h4 : (pc : Int) + o < C.length) :
    ∃ s', Runs M s s' ∧ Mid K C s0 (if st.x a = 0 then ((pc : Int) + o).toNat else pc + 1, st) 0 s' := by
  have w0 := word_pc hM hC hB hpcl (by decide) (w := cbz (armReg a) (4 * o)) (by rw [hblk]; rfl)
  obtain ⟨s1, r1, c1, o1⟩ := S.cbz s (armReg a) (4 * o) hM.cfg (armReg_lt ha a0) (by omega) (by omega) w0
  rw [hM.x a (by omega) (mapped_lt ha)] at o1
  have hpcA := hM.pc
  by_cases hz : st.x a = 0
  · rw [if_pos hz]
    refine ⟨s1, r1, mid_regs hM c1 ?_ (by rw [o1]; rfl) (fun j h0 h32 => by rw [o1]; exact hM.x j h0 h32)
      (fun r _ _ => by rw [o1]; rfl) hM.x0 rfl rfl rfl⟩
    rw [o1]; simp only [jumpTo, if_pos hz]
    rw [hpcA, ofNat_addInt _ _ (by omega) (by omega)]; congr 1; omega
  · rw [if_neg hz]
    have M1 : Mid K C s0 (pc, st) 1 s1 := by
      refine mid_regs hM c1 ?_ (by rw [o1]; rfl) (fun j h0 h32 => by rw [o1]; exact hM.x j h0 h32)
        (fun r _ _ => by rw [o1]; rfl) hM.x0 rfl rfl rfl
      rw [o1]; simp only [jumpTo, if_neg hz]; rw [hpcA, ofNat_add4]
    obtain ⟨s2, r2, M2⟩ := run_pads S hC hB hpcl 3 1 s1 (by decide) M1
      (fun i h1 h2 => by rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl <;> rw [hblk] <;> rfl)
    exact ⟨s2, Runs.trans r1 r2, M2⟩

/-! ## constants and immediates -/

/-- `movz d, #(65536 − n); movk d, #0xFFFF, lsl 16/32/48` builds −n (1 ≤ n ≤ 2048) -/
theorem movk_chain : ∀ n, n < 2049 → 1 ≤ n →
    movkV (movkV (movkV (UInt64.ofNat (65536 - n)) 65535 1) 65535 2) 65535 3 = UInt64.ofInt (-(n : Int)) := by
  decide +kernel

theorem ofNat_imm {imm : Int} (h : 0 ≤ imm) : UInt64.ofNat imm.toNat = UInt64.ofInt imm := by
  apply UInt64.toNat_inj.1; rw [ofInt_toNat']; simp; omega

theorem sub_imm (x : UInt64) {imm : Int} (h : imm < 0) (h2 : -2048 ≤ imm) :
    x - UInt64.ofNat imm.natAbs = x + UInt64.ofInt imm := by
  apply UInt64.toNat_inj.1
  rw [UInt64.toNat_sub, UInt64.toNat_add, ofInt_toNat']; simp; omega

theorem wr_wr (s : CallProbe.St) (r : Nat) (a b : UInt64) : CallProbe.wr (CallProbe.wr s r a) r b = CallProbe.wr s r b := by
  unfold CallProbe.wr; split
  · rfl
  · simp only; congr 1; funext i; unfold CallProbe.upd; split <;> rfl

theorem wr_same (s : CallProbe.St) {r : Nat} (h : r ≠ 0) (v : UInt64) : (CallProbe.wr s r v).x r = v := by
  simp [CallProbe.wr, h, CallProbe.upd]

theorem wr_zero (s : CallProbe.St) (v : UInt64) : CallProbe.wr s 0 v = s := by simp [CallProbe.wr]

/-- `addi rd, rs, imm` with the machine's wrapping sum (`movz`/`movk`, `add`/`sub` imm, or PADs for rd = x0) -/
theorem blk_addi (S : A64Sem M) {K : LayW} {C : List J} {s0 s : M.State} {pc : Nat} {st : CallProbe.St}
    {rd rs : Nat} {imm : Int}
    (hM : Mid K C s0 (pc, st) 0 s) (hC : C[pc]? = some (.addi rd rs imm)) (hB : K.base + 16 * C.length ≤ 2 ^ 32)
    (hpcl : pc < C.length) (hrd : mapped rd = true) (hrs : mapped rs = true) (hi1 : -2048 ≤ imm) (hi2 : imm < 2048) :
    ∃ s', Runs M s s' ∧ Mid K C s0 (pc + 1, CallProbe.wr st rd (st.x rs + UInt64.ofInt imm)) 0 s' := by
  by_cases hd : rd = 0
  · subst hd; rw [wr_zero]
    have hb : blockJ (.addi 0 rs imm) = [PAD, PAD, PAD, PAD] := rfl
    exact run_pads S hC hB hpcl 4 0 s (by decide) hM (fun i _ h2 => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rw [hb] <;> rfl)
  have hdl := armReg_lt hrd hd
  by_cases hs : rs = 0
  · subst hs; rw [hM.x0, UInt64.zero_add]
    by_cases hn : imm < 0
    · have hb : blockJ (.addi rd 0 imm) = [movz (armReg rd) (65536 - imm.natAbs), movk (armReg rd) 65535 1,
          movk (armReg rd) 65535 2, movk (armReg rd) 65535 3] := by simp [blockJ, body, pad4, hd, hn]
      have w0 := word_pc hM hC hB hpcl (by decide) (w := movz (armReg rd) (65536 - imm.natAbs)) (by rw [hb]; rfl)
      obtain ⟨s1, r1, M1⟩ := mid_set hM hrd hd (S.movz s _ _ hM.cfg hdl (by omega) w0)
      have w1 := word_pc M1 hC hB hpcl (by decide) (w := movk (armReg rd) 65535 1) (by rw [hb]; rfl)
      have g1 := S.movk s1 _ _ _ M1.cfg hdl (by decide) (by decide) w1
      rw [M1.x rd (by omega) (mapped_lt hrd)] at g1
      obtain ⟨s2, r2, M2⟩ := mid_set M1 hrd hd g1
      have w2 := word_pc M2 hC hB hpcl (by decide) (w := movk (armReg rd) 65535 2) (by rw [hb]; rfl)
      have g2 := S.movk s2 _ _ _ M2.cfg hdl (by decide) (by decide) w2
      rw [M2.x rd (by omega) (mapped_lt hrd)] at g2
      obtain ⟨s3, r3, M3⟩ := mid_set M2 hrd hd g2
      have w3 := word_pc M3 hC hB hpcl (by decide) (w := movk (armReg rd) 65535 3) (by rw [hb]; rfl)
      have g3 := S.movk s3 _ _ _ M3.cfg hdl (by decide) (by decide) w3
      rw [M3.x rd (by omega) (mapped_lt hrd)] at g3
      obtain ⟨s4, r4, M4⟩ := mid_set M3 hrd hd g3
      refine ⟨s4, Runs.trans r1 (Runs.trans r2 (Runs.trans r3 r4)), ?_⟩
      have M5 := mid_next M4
      simp only [wr_wr, wr_same _ hd] at M5
      rw [movk_chain imm.natAbs (by omega) (by omega), show (-(imm.natAbs : Int)) = imm by omega] at M5
      exact M5
    · have hb : blockJ (.addi rd 0 imm) = [movz (armReg rd) imm.toNat, PAD, PAD, PAD] := by
        simp [blockJ, body, pad4, hd, hn]
      have w0 := word_pc hM hC hB hpcl (by decide) (w := movz (armReg rd) imm.toNat) (by rw [hb]; rfl)
      obtain ⟨s1, r1, M1⟩ := mid_set hM hrd hd (S.movz s _ _ hM.cfg hdl (by omega) w0)
      obtain ⟨s2, r2, M2⟩ := run_pads S hC hB hpcl 3 1 s1 (by decide) M1
        (fun i h1 h2 => by rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl <;> rw [hb] <;> rfl)
      rw [ofNat_imm (by omega)] at M2
      exact ⟨s2, Runs.trans r1 r2, M2⟩
  · have hsl := armReg_lt hrs hs
    by_cases hn : imm < 0
    · have hb : blockJ (.addi rd rs imm) = [subi (armReg rd) (armReg rs) imm.natAbs, PAD, PAD, PAD] := by
        simp [blockJ, body, pad4, hd, hs, hn]
      have w0 := word_pc hM hC hB hpcl (by decide) (w := subi (armReg rd) (armReg rs) imm.natAbs) (by rw [hb]; rfl)
      have g := S.subi s _ _ _ hM.cfg hdl hsl (by omega) w0
      rw [hM.x rs (by omega) (mapped_lt hrs), sub_imm _ hn hi1] at g
      obtain ⟨s1, r1, M1⟩ := mid_set hM hrd hd g
      obtain ⟨s2, r2, M2⟩ := run_pads S hC hB hpcl 3 1 s1 (by decide) M1
        (fun i h1 h2 => by rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl <;> rw [hb] <;> rfl)
      exact ⟨s2, Runs.trans r1 r2, M2⟩
    · have hb : blockJ (.addi rd rs imm) = [addi (armReg rd) (armReg rs) imm.toNat, PAD, PAD, PAD] := by
        simp [blockJ, body, pad4, hd, hs, hn]
      have w0 := word_pc hM hC hB hpcl (by decide) (w := addi (armReg rd) (armReg rs) imm.toNat) (by rw [hb]; rfl)
      have g := S.addi s _ _ _ hM.cfg hdl hsl (by omega) w0
      rw [hM.x rs (by omega) (mapped_lt hrs), ofNat_imm (by omega)] at g
      obtain ⟨s1, r1, M1⟩ := mid_set hM hrd hd g
      obtain ⟨s2, r2, M2⟩ := run_pads S hC hB hpcl 3 1 s1 (by decide) M1
        (fun i h1 h2 => by rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl <;> rw [hb] <;> rfl)
      exact ⟨s2, Runs.trans r1 r2, M2⟩

theorem aluV_eq (op : Nat) (a b z : UInt64) (h : op ≠ 3 ∨ z = 0) : aluV op a b z = CallProbe.aluf op a b := by
  unfold aluV CallProbe.aluf
  by_cases h3 : op = 3
  · subst h3; simp at h; simp [h]
  · simp [h3]

/-- `alu op rd a b` (rd ≠ x0): [`movz x17, #0`] `add/sub/madd/and/orr/lslv/lsrv/eor` -/
theorem blk_alu (S : A64Sem M) {K : LayW} {C : List J} {s0 s : M.State} {pc : Nat} {st : CallProbe.St}
    {op rd a b : Nat}
    (hM : Mid K C s0 (pc, st) 0 s) (hC : C[pc]? = some (.alu op rd a b)) (hB : K.base + 16 * C.length ≤ 2 ^ 32)
    (hpcl : pc < C.length) (h1 : 1 ≤ op) (h8 : op ≤ 8) (hrd : mapped rd = true) (hd : rd ≠ 0) (ha : mapped a = true)
    (hb : mapped b = true) :
    ∃ s', Runs M s s' ∧ Mid K C s0 (pc + 1, CallProbe.wr st rd (CallProbe.aluf op (st.x a) (st.x b))) 0 s' := by
  have hdl := armReg_lt hrd hd
  by_cases hz : a = 0 ∨ b = 0 ∨ op = 3
  · have hbk : blockJ (.alu op rd a b) = [movz 17 0, rr (aluC op) (armReg rd) (opR a) (opR b), PAD, PAD] := by
      simp [blockJ, body, pad4, hd, hz, zpre]
    have w0 := word_pc hM hC hB hpcl (by decide) (w := movz 17 0) (by rw [hbk]; rfl)
    obtain ⟨s1, r1, M1, o1⟩ := mid_scr hM (Or.inr rfl) (S.movz s 17 0 hM.cfg (by decide) (by decide) w0)
    have r17 : (M.observe s1).register 17 = 0 := by rw [o1]; simp [setReg]
    have w1 := word_pc M1 hC hB hpcl (by decide) (w := rr (aluC op) (armReg rd) (opR a) (opR b)) (by rw [hbk]; rfl)
    have g := S.alu s1 op _ _ _ M1.cfg h1 h8 hdl (opR_lt ha) (opR_lt hb) w1
    rw [opR_val M1 ha (fun _ => r17), opR_val M1 hb (fun _ => r17), r17, aluV_eq _ _ _ _ (Or.inr rfl)] at g
    obtain ⟨s2, r2, M2⟩ := mid_set M1 hrd hd g
    obtain ⟨s3, r3, M3⟩ := run_pads S hC hB hpcl 2 2 s2 (by decide) M2
      (fun i h1 h2 => by rcases (by omega : i = 2 ∨ i = 3) with rfl | rfl <;> rw [hbk] <;> rfl)
    exact ⟨s3, Runs.trans r1 (Runs.trans r2 r3), M3⟩
  · have a0 : a ≠ 0 := fun e => hz (Or.inl e)
    have b0 : b ≠ 0 := fun e => hz (Or.inr (Or.inl e))
    have o3 : op ≠ 3 := fun e => hz (Or.inr (Or.inr e))
    have hbk : blockJ (.alu op rd a b) = [rr (aluC op) (armReg rd) (opR a) (opR b), PAD, PAD, PAD] := by
      simp [blockJ, body, pad4, hd, hz, zpre]
    have w0 := word_pc hM hC hB hpcl (by decide) (w := rr (aluC op) (armReg rd) (opR a) (opR b)) (by rw [hbk]; rfl)
    have g := S.alu s op _ _ _ hM.cfg h1 h8 hdl (opR_lt ha) (opR_lt hb) w0
    rw [opR_val hM ha (fun e => absurd e a0), opR_val hM hb (fun e => absurd e b0), aluV_eq _ _ _ _ (Or.inl o3)] at g
    obtain ⟨s1, r1, M1⟩ := mid_set hM hrd hd g
    obtain ⟨s2, r2, M2⟩ := run_pads S hC hB hpcl 3 1 s1 (by decide) M1
      (fun i h1 h2 => by rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl <;> rw [hbk] <;> rfl)
    exact ⟨s2, Runs.trans r1 r2, M2⟩

/-- a shift by `sh` (`slli` op 6, `srli` op 7): [`movz x17, #0`] `movz x16, #sh; lslv/lsrv d, s, x16`; PADs for x0 -/
theorem blk_shift (S : A64Sem M) {K : LayW} {C : List J} {s0 s : M.State} {pc : Nat} {st : CallProbe.St}
    {rd rs sh op : Nat} {j : J}
    (hM : Mid K C s0 (pc, st) 0 s) (hC : C[pc]? = some j) (hB : K.base + 16 * C.length ≤ 2 ^ 32)
    (hpcl : pc < C.length) (hop : op = 6 ∨ op = 7)
    (hbody : body j = if rd = 0 then [] else zpre rs ++ [movz 16 sh, rr (aluC op) (armReg rd) (opR rs) 16])
    (hrd : mapped rd = true) (hrs : mapped rs = true) (hsh : sh < 64) :
    ∃ s', Runs M s s' ∧ Mid K C s0 (pc + 1, CallProbe.wr st rd (aluV op (st.x rs) (UInt64.ofNat sh) 0)) 0 s' := by
  by_cases hd : rd = 0
  · subst hd; rw [wr_zero]
    have hb : blockJ j = [PAD, PAD, PAD, PAD] := by simp [blockJ, hbody, pad4]
    exact run_pads S hC hB hpcl 4 0 s (by decide) hM (fun i _ h2 => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rw [hb] <;> rfl)
  have hdl := armReg_lt hrd hd
  have hv : ∀ z : UInt64, aluV op (st.x rs) (UInt64.ofNat sh) z = aluV op (st.x rs) (UInt64.ofNat sh) 0 := by
    intro z; unfold aluV; rcases hop with rfl | rfl <;> simp
  -- the shift itself, from word k (x16 := sh first)
  have tail : ∀ k (s1 : M.State), k ≤ 1 → Mid K C s0 (pc, st) k s1 →
      (blockJ j).getD k 0 = movz 16 sh → (blockJ j).getD (k + 1) 0 = rr (aluC op) (armReg rd) (opR rs) 16 →
      (∀ i, k + 2 ≤ i → i < 4 → (blockJ j).getD i 0 = PAD) →
      (rs = 0 → (M.observe s1).register 17 = 0) →
      ∃ s', Runs M s1 s' ∧ Mid K C s0 (pc + 1, CallProbe.wr st rd (aluV op (st.x rs) (UInt64.ofNat sh) 0)) 0 s' := by
    intro k s1 hk M1 e1 e2 e3 z17
    have w1 := word_pc M1 hC hB hpcl (by omega) e1
    obtain ⟨s2, r2, M2, o2⟩ := mid_scr M1 (Or.inl rfl) (S.movz s1 16 sh M1.cfg (by decide) (by omega) w1)
    have w2 := word_pc M2 hC hB hpcl (by omega) e2
    have g := S.alu s2 op _ _ _ M2.cfg (by omega) (by omega) hdl (opR_lt hrs) (by decide) w2
    have r16 : (M.observe s2).register 16 = UInt64.ofNat sh := by rw [o2]; simp [setReg]
    have z2 : rs = 0 → (M.observe s2).register 17 = 0 := fun e => by rw [o2]; simp [setReg]; exact z17 e
    rw [opR_val M2 hrs z2, r16, hv] at g
    obtain ⟨s3, r3, M3⟩ := mid_set M2 hrd hd g
    obtain ⟨s4, r4, M4⟩ := run_pads S hC hB hpcl (4 - (k + 2)) (k + 2) s3 (by omega) M3 e3
    exact ⟨s4, Runs.trans r2 (Runs.trans r3 r4), M4⟩
  by_cases hs : rs = 0
  · have hb : blockJ j = [movz 17 0, movz 16 sh, rr (aluC op) (armReg rd) (opR rs) 16, PAD] := by
      simp [blockJ, hbody, pad4, hd, hs, zpre]
    have w0 := word_pc hM hC hB hpcl (by decide) (w := movz 17 0) (by rw [hb]; rfl)
    obtain ⟨s1, r1, M1, o1⟩ := mid_scr hM (Or.inr rfl) (S.movz s 17 0 hM.cfg (by decide) (by decide) w0)
    obtain ⟨s2, r2, M2⟩ := tail 1 s1 (Nat.le_refl _) M1 (by rw [hb]; rfl) (by rw [hb]; rfl)
      (fun i h1 h2 => by rw [show i = 3 by omega, hb]; rfl) (fun _ => by rw [o1]; simp [setReg])
    exact ⟨s2, Runs.trans r1 r2, M2⟩
  · have hb : blockJ j = [movz 16 sh, rr (aluC op) (armReg rd) (opR rs) 16, PAD, PAD] := by
      simp [blockJ, hbody, pad4, hd, hs, zpre]
    exact tail 0 s (Nat.zero_le _) hM (by rw [hb]; rfl) (by rw [hb]; rfl)
      (fun i h1 h2 => by rcases (by omega : i = 2 ∨ i = 3) with rfl | rfl <;> rw [hb] <;> rfl) (fun e => absurd e hs)

/-! ## memory -/

theorem toUInt64_inj8 {a b : UInt8} (h : a.toUInt64 = b.toUInt64) : a = b := by
  apply UInt8.toNat_inj.1; have := congrArg UInt64.toNat h; simpa using this

/-- a byte store, seen in the cell `c` that holds byte `c + k` -/
theorem cbyte_sbm (m : Nat → UInt64) (a c k : Nat) (v : UInt64) (hc : c % 8 = 0) (hk : k < 8) :
    cbyte (CallProbe.sbm m a v c) k = if c + k = a then v.toUInt8 else cbyte (m c) k := by
  have e1 := lbm_cbyte (CallProbe.sbm m a v) (c + k)
  have e2 := lbm_cbyte m (c + k)
  rw [show c + k - (c + k) % 8 = c by omega, show (c + k) % 8 = k by omega] at e1 e2
  split
  · rename_i h; subst h
    rw [CallProbe.lbm_sbm_same] at e1
    apply toUInt64_inj8; rw [← e1]
    apply UInt64.toNat_inj.1
    simp [UInt64.toNat_and, Nat.and_two_pow_sub_one_eq_mod _ 8]
  · rename_i h
    rw [CallProbe.lbm_sbm_other _ _ _ _ h, e2] at e1
    exact (toUInt64_inj8 e1).symm

theorem toNat_ofNat_lt {q : Nat} (h : q < 2 ^ 64) : (UInt64.ofNat q).toNat = q := by simp; omega

/-- an 8-byte store to the work cell `a` with J's new value -/
theorem mid_store8 {K : LayW} {C : List J} {s0 s : M.State} {pc k : Nat} {st : CallProbe.St}
    (hM : Mid K C s0 (pc, st) k s) (hL : JTarget.LayOK M (16 * C.length) K) (hR : M.ramEnd ≤ 2 ^ 32)
    (hpcl : pc < C.length) (hk : k < 4) {a : Nat} (ha : wok K a) {v : UInt64}
    (hg : Goes M s (store8 (M.observe s) a v)) :
    ∃ s', Runs M s s' ∧ Mid K C s0 (pc, { st with m := CallProbe.upd st.m a v }) (k + 1) s' := by
  obtain ⟨s', r, c, o⟩ := hg
  have hpc := hM.pc
  have hwa := hL.wlo; have hwb := hL.whi; have hcw := hL.cw; have hbh := hL.bhi
  have hib := hL.ibh; have hob := hL.obh; have hil := hL.ibl; have hol := hL.obl
  unfold wok at ha
  refine ⟨s', r, ⟨c, by rw [o]; simp only [store8]; rw [hpc, ofNat_add4]; congr 1, ?_, hM.x0, hM.bb, hM.ww,
    fun j h0 h32 => by rw [o]; exact hM.x j h0 h32, fun r' h1 h2 => by rw [o]; exact hM.keep r' h1 h2, ?_, ?_, ?_⟩⟩
  · intro i h k' hk' b hb
    rw [o]; simp only [store8]
    rw [blk_len] at hk'
    have hq : K.base + 4 * 4 * i + 4 * k' + b < 2 ^ 64 := by omega
    rw [toNat_ofNat_lt hq, if_neg (by omega)]
    exact hM.code i h k' (by rw [blk_len]; exact hk') b hb
  · intro c' hc' k' hk'
    unfold wok at hc'
    rw [o]; simp only [store8]
    rw [toNat_ofNat_lt (by omega)]
    by_cases e : c' = a
    · subst e; rw [if_pos (by omega)]; simp [CallProbe.upd]
    · rw [if_neg (by omega)]; rw [hM.w c' (by unfold wok; omega) k' hk']; simp [CallProbe.upd, e]
  · intro x hx
    have hx64 : x < 2 ^ 64 := by unfold io outB at hx; omega
    rw [o]; simp only [store8]; rw [toNat_ofNat_lt hx64]
    by_cases e : a ≤ x ∧ x < a + 8
    · rw [if_pos e, show x - x % 8 = a by omega, show x - a = x % 8 by omega]; simp [CallProbe.upd]
    · rw [if_neg e, hM.bw x hx]; simp [CallProbe.upd, show x - x % 8 ≠ a by omega]
  · intro x hx h1 h2
    rw [o]; simp only [store8]; rw [toNat_ofNat_lt hx]
    rw [if_neg (fun e => h1 (by unfold wok; omega))]; exact hM.fr x hx h1 h2

/-- a byte store to a `sok` byte `a` (a work cell's byte or an output byte) with J's new memory -/
theorem mid_store1 {K : LayW} {C : List J} {s0 s : M.State} {pc k : Nat} {st : CallProbe.St}
    (hM : Mid K C s0 (pc, st) k s) (hL : JTarget.LayOK M (16 * C.length) K) (hR : M.ramEnd ≤ 2 ^ 32)
    (hpcl : pc < C.length) (hk : k < 4) {a : Nat} (ha : sok K a) {v : UInt64}
    (hg : Goes M s (store1 (M.observe s) a v)) :
    ∃ s', Runs M s s' ∧ Mid K C s0 (pc, { st with m := CallProbe.sbm st.m a v }) (k + 1) s' := by
  obtain ⟨s', r, c, o⟩ := hg
  have hpc := hM.pc
  have hwa := hL.wlo; have hwb := hL.whi; have hcw := hL.cw; have hbh := hL.bhi; have hoc := hL.oc
  have hib := hL.ibh; have hob := hL.obh; have hil := hL.ibl; have hol := hL.obl
  have ha' : (K.lo ≤ a - a % 8 ∧ a - a % 8 + 8 ≤ K.hi) ∨ (K.ob ≤ a ∧ a < K.ob + K.ol) := by
    unfold sok wok outB at ha; omega
  refine ⟨s', r, ⟨c, by rw [o]; simp only [store1]; rw [hpc, ofNat_add4]; congr 1, ?_, hM.x0, hM.bb, hM.ww,
    fun j h0 h32 => by rw [o]; exact hM.x j h0 h32, fun r' h1 h2 => by rw [o]; exact hM.keep r' h1 h2, ?_, ?_, ?_⟩⟩
  · intro i h k' hk' b hb
    rw [o]; simp only [store1]
    rw [blk_len] at hk'
    have hq : K.base + 4 * 4 * i + 4 * k' + b < 2 ^ 64 := by omega
    rw [toNat_ofNat_lt hq, if_neg (by omega)]
    exact hM.code i h k' (by rw [blk_len]; exact hk') b hb
  · intro c' hc' k' hk'
    have hc8 : c' % 8 = 0 := hc'.2.2
    unfold wok at hc'
    rw [o]; simp only [store1]
    rw [toNat_ofNat_lt (by omega), hM.w c' (by unfold wok; omega) k' hk', cbyte_sbm _ _ _ _ _ hc8 hk']
    by_cases e : c' + k' = a
    · rw [if_pos e, if_pos e]
    · rw [if_neg e, if_neg e]
  · intro x hx
    have hx64 : x < 2 ^ 64 := by unfold io outB at hx; omega
    rw [o]; simp only [store1]; rw [toNat_ofNat_lt hx64, hM.bw x hx]
    rw [cbyte_sbm _ _ _ _ _ (by omega) (Nat.mod_lt _ (by decide)), show x - x % 8 + x % 8 = x by omega]
    by_cases e : x = a
    · rw [if_pos e, if_pos e]
    · rw [if_neg e, if_neg e]
  · intro x hx h1 h2
    rw [o]; simp only [store1]; rw [toNat_ofNat_lt hx]
    rw [if_neg (fun e => by subst e; unfold sok at ha; exact ha.elim h1 h2)]; exact hM.fr x hx h1 h2

/-- `add/sub x16, xs, #|f|`: x16 := the effective address (no wrap: J's address is ≥ 0) -/
theorem addr_x16 (S : A64Sem M) {K : LayW} {C : List J} {s0 s : M.State} {pc k : Nat} {st : CallProbe.St} {j : J}
    (hM : Mid K C s0 (pc, st) k s) (hC : C[pc]? = some j) (hB : K.base + 16 * C.length ≤ 2 ^ 32)
    (hpcl : pc < C.length) (hk : k < 4) {rs : Nat} {f : Int} (hrs : mapped rs = true) (rs0 : rs ≠ 0)
    (hf1 : -2048 ≤ f) (hf2 : f < 2048) (hw : (blockJ j).getD k 0 = addr16 rs f)
    (h0 : 0 ≤ ((st.x rs).toNat : Int) + f) :
    ∃ s', Runs M s s' ∧ Mid K C s0 (pc, st) (k + 1) s' ∧
      (M.observe s').register 16 = UInt64.ofNat (CallProbe.ea (st.x rs) f) ∧
      (M.observe s').register 17 = (M.observe s).register 17 := by
  have hsl := armReg_lt hrs rs0
  have xr := hM.x rs (by omega) (mapped_lt hrs)
  unfold addr16 at hw
  split at hw
  · rename_i hn
    have w := word_pc hM hC hB hpcl hk hw
    obtain ⟨s1, r1, M1, o1⟩ := mid_scr hM (Or.inl rfl) (S.subi s 16 _ _ hM.cfg (by decide) hsl (by omega) w)
    refine ⟨s1, r1, M1, ?_, by rw [o1]; simp [setReg]⟩
    rw [o1]; simp only [setReg, if_true]; rw [xr]
    apply UInt64.toNat_inj.1
    rw [UInt64.toNat_sub]; simp [CallProbe.ea]; omega
  · rename_i hn
    have w := word_pc hM hC hB hpcl hk hw
    obtain ⟨s1, r1, M1, o1⟩ := mid_scr hM (Or.inl rfl) (S.addi s 16 _ _ hM.cfg (by decide) hsl (by omega) w)
    refine ⟨s1, r1, M1, ?_, by rw [o1]; simp [setReg]⟩
    rw [o1]; simp only [setReg, if_true]; rw [xr]
    apply UInt64.toNat_inj.1
    simp [CallProbe.ea, UInt64.toNat_add]; omega

/-- `ld rd, off(rs)` from the work cell `ea`: `ldr d, [s, #off]`, or `add/sub x16` + `ldr d, [x16]`; PADs for x0 -/
theorem blk_ld (S : A64Sem M) {K : LayW} {C : List J} {s0 s : M.State} {pc : Nat} {st : CallProbe.St}
    {rd rs : Nat} {off : Int}
    (hM : Mid K C s0 (pc, st) 0 s) (hC : C[pc]? = some (.ld rd rs off)) (hB : K.base + 16 * C.length ≤ 2 ^ 32)
    (hpcl : pc < C.length) (hL : JTarget.LayOK M (16 * C.length) K) (hR : M.ramEnd ≤ 2 ^ 32)
    (hrd : mapped rd = true) (hrs : mapped rs = true) (rs0 : rs ≠ 0) (hf1 : -2048 ≤ off) (hf2 : off < 2048)
    (h0 : 0 ≤ ((st.x rs).toNat : Int) + off) (hwk : wok K (CallProbe.ea (st.x rs) off)) :
    ∃ s', Runs M s s' ∧ Mid K C s0 (pc + 1, CallProbe.wr st rd (st.m (CallProbe.ea (st.x rs) off))) 0 s' := by
  by_cases hd : rd = 0
  · subst hd; rw [wr_zero]
    have hb : blockJ (.ld 0 rs off) = [PAD, PAD, PAD, PAD] := rfl
    exact run_pads S hC hB hpcl 4 0 s (by decide) hM (fun i _ h2 => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rw [hb] <;> rfl)
  have hdl := armReg_lt hrd hd
  have hsl := armReg_lt hrs rs0
  have wl := hL.wlo; have wh := hL.whi
  have hwk' := hwk
  unfold wok at hwk'
  -- the load itself from base register n with offset f, word k
  have ld_at : ∀ k (s1 : M.State) (n f : Nat), Mid K C s0 (pc, st) k s1 → k < 4 → n < 31 → f % 8 = 0 → f < 32768 →
      ((M.observe s1).register n).toNat + f = CallProbe.ea (st.x rs) off →
      (blockJ (.ld rd rs off)).getD k 0 = ldr (armReg rd) n f →
      (∀ i, k + 1 ≤ i → i < 4 → (blockJ (.ld rd rs off)).getD i 0 = PAD) →
      ∃ s', Runs M s1 s' ∧ Mid K C s0 (pc + 1, CallProbe.wr st rd (st.m (CallProbe.ea (st.x rs) off))) 0 s' := by
    intro k s1 n f M1 hk hn hf8 hf hea e1 e2
    have w := word_pc M1 hC hB hpcl hk e1
    have g := S.ldr s1 _ n f (st.m (CallProbe.ea (st.x rs) off)) M1.cfg hdl hn hf8 hf (by omega) (by omega)
      (by omega) (by omega) (fun k' hk' => by rw [hea]; exact M1.w _ hwk k' hk') w
    obtain ⟨s2, r2, M2⟩ := mid_set M1 hrd hd g
    obtain ⟨s3, r3, M3⟩ := run_pads S hC hB hpcl (4 - (k + 1)) (k + 1) s2 (by omega) M2 e2
    exact ⟨s3, Runs.trans r2 r3, M3⟩
  by_cases hdir : off % 8 = 0 ∧ 0 ≤ off ∧ off < 32768
  · have hb : blockJ (.ld rd rs off) = [ldr (armReg rd) (armReg rs) off.toNat, PAD, PAD, PAD] := by
      simp [blockJ, body, pad4, hd, hdir]
    exact ld_at 0 s (armReg rs) off.toNat hM (by decide) hsl (by omega) (by omega)
      (by rw [hM.x rs (by omega) (mapped_lt hrs)]; simp [CallProbe.ea]; omega) (by rw [hb]; rfl)
      (fun i h1 h2 => by rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl <;> rw [hb] <;> rfl)
  · have hb : blockJ (.ld rd rs off) = [addr16 rs off, ldr (armReg rd) 16 0, PAD, PAD] := by
      simp [blockJ, body, pad4, hd, hdir]
    obtain ⟨s1, r1, M1, x16, -⟩ := addr_x16 S hM hC hB hpcl (by decide) hrs rs0 hf1 hf2 (by rw [hb]; rfl) h0
    obtain ⟨s2, r2, M2⟩ := ld_at 1 s1 16 0 M1 (by decide) (by decide) (by decide) (by decide)
      (by rw [x16, toNat_ofNat_lt (by omega), Nat.add_zero]) (by rw [hb]; rfl)
      (fun i h1 h2 => by rcases (by omega : i = 2 ∨ i = 3) with rfl | rfl <;> rw [hb] <;> rfl)
    exact ⟨s2, Runs.trans r1 r2, M2⟩

/-- a byte `lbu` may read: its value in memory and its place in RAM -/
theorem byte_bok {K : LayW} {C : List J} {s0 s : M.State} {p : Nat × CallProbe.St} {k : Nat}
    (hM : Mid K C s0 p k s) (hL : JTarget.LayOK M (16 * C.length) K) {a : Nat} (ha : bok K a) :
    (M.observe s).memory (UInt64.ofNat a) = some (cbyte (p.2.m (a - a % 8)) (a % 8)) ∧
      M.ramStart ≤ a ∧ a < M.ramEnd := by
  have wl := hL.wlo; have wh := hL.whi; have il := hL.ibl; have ih := hL.ibh; have ol := hL.obl; have oh := hL.obh
  rcases ha with hw | hio
  · have := hM.w _ hw (a % 8) (Nat.mod_lt _ (by decide))
    rw [show a - a % 8 + a % 8 = a by omega] at this
    unfold wok at hw
    exact ⟨this, by omega, by omega⟩
  · refine ⟨hM.bw a hio, ?_, ?_⟩ <;> (unfold io outB at hio; omega)

/-- `lbu rd, off(rs)`: `ldrb d, [s, #off]`, or `add/sub x16` + `ldrb d, [x16]`; PADs for x0 -/
theorem blk_lbu (S : A64Sem M) {K : LayW} {C : List J} {s0 s : M.State} {pc : Nat} {st : CallProbe.St}
    {rd rs : Nat} {off : Int}
    (hM : Mid K C s0 (pc, st) 0 s) (hC : C[pc]? = some (.lbu rd rs off)) (hB : K.base + 16 * C.length ≤ 2 ^ 32)
    (hpcl : pc < C.length) (hL : JTarget.LayOK M (16 * C.length) K) (hR : M.ramEnd ≤ 2 ^ 32)
    (hrd : mapped rd = true) (hrs : mapped rs = true) (rs0 : rs ≠ 0) (hf1 : -2048 ≤ off) (hf2 : off < 2048)
    (h0 : 0 ≤ ((st.x rs).toNat : Int) + off) (hbk : bok K (CallProbe.ea (st.x rs) off)) :
    ∃ s', Runs M s s' ∧ Mid K C s0 (pc + 1, CallProbe.wr st rd (CallProbe.lbm st.m (CallProbe.ea (st.x rs) off))) 0 s' := by
  by_cases hd : rd = 0
  · subst hd; rw [wr_zero]
    have hb : blockJ (.lbu 0 rs off) = [PAD, PAD, PAD, PAD] := rfl
    exact run_pads S hC hB hpcl 4 0 s (by decide) hM (fun i _ h2 => by
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rw [hb] <;> rfl)
  have hdl := armReg_lt hrd hd
  have hsl := armReg_lt hrs rs0
  have ld_at : ∀ k (s1 : M.State) (n f : Nat), Mid K C s0 (pc, st) k s1 → k < 4 → n < 31 → f < 4096 →
      ((M.observe s1).register n).toNat + f = CallProbe.ea (st.x rs) off →
      (blockJ (.lbu rd rs off)).getD k 0 = ldrb (armReg rd) n f →
      (∀ i, k + 1 ≤ i → i < 4 → (blockJ (.lbu rd rs off)).getD i 0 = PAD) →
      ∃ s', Runs M s1 s' ∧
        Mid K C s0 (pc + 1, CallProbe.wr st rd (CallProbe.lbm st.m (CallProbe.ea (st.x rs) off))) 0 s' := by
    intro k s1 n f M1 hk hn hf hea e1 e2
    have w := word_pc M1 hC hB hpcl hk e1
    obtain ⟨hby, hr1, hr2⟩ := byte_bok M1 hL hbk
    have g := S.ldrb s1 _ n f _ M1.cfg hdl hn hf (by omega) (by omega) (by omega) (by rw [hea]; exact hby) w
    rw [← lbm_cbyte] at g
    obtain ⟨s2, r2, M2⟩ := mid_set M1 hrd hd g
    obtain ⟨s3, r3, M3⟩ := run_pads S hC hB hpcl (4 - (k + 1)) (k + 1) s2 (by omega) M2 e2
    exact ⟨s3, Runs.trans r2 r3, M3⟩
  by_cases hdir : 0 ≤ off ∧ off < 4096
  · have hb : blockJ (.lbu rd rs off) = [ldrb (armReg rd) (armReg rs) off.toNat, PAD, PAD, PAD] := by
      simp [blockJ, body, pad4, hd, hdir]
    exact ld_at 0 s (armReg rs) off.toNat hM (by decide) hsl (by omega)
      (by rw [hM.x rs (by omega) (mapped_lt hrs)]; simp [CallProbe.ea]; omega) (by rw [hb]; rfl)
      (fun i h1 h2 => by rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl <;> rw [hb] <;> rfl)
  · have hb : blockJ (.lbu rd rs off) = [addr16 rs off, ldrb (armReg rd) 16 0, PAD, PAD] := by
      simp [blockJ, body, pad4, hd, hdir]
    obtain ⟨hby, hr1, hr2⟩ := byte_bok hM hL hbk
    obtain ⟨s1, r1, M1, x16, -⟩ := addr_x16 S hM hC hB hpcl (by decide) hrs rs0 hf1 hf2 (by rw [hb]; rfl) h0
    obtain ⟨s2, r2, M2⟩ := ld_at 1 s1 16 0 M1 (by decide) (by decide) (by decide)
      (by rw [x16, toNat_ofNat_lt (by omega), Nat.add_zero]) (by rw [hb]; rfl)
      (fun i h1 h2 => by rcases (by omega : i = 2 ∨ i = 3) with rfl | rfl <;> rw [hb] <;> rfl)
    exact ⟨s2, Runs.trans r1 r2, M2⟩

/-- `sd r2, off(r1)` to the work cell `ea`: [`movz x17, #0`] `str` (direct or via x16), then PADs -/
theorem blk_sd (S : A64Sem M) {K : LayW} {C : List J} {s0 s : M.State} {pc : Nat} {st : CallProbe.St}
    {r1 r2 : Nat} {off : Int}
    (hM : Mid K C s0 (pc, st) 0 s) (hC : C[pc]? = some (.sd r2 r1 off)) (hB : K.base + 16 * C.length ≤ 2 ^ 32)
    (hpcl : pc < C.length) (hL : JTarget.LayOK M (16 * C.length) K) (hR : M.ramEnd ≤ 2 ^ 32)
    (hr1 : mapped r1 = true) (r10 : r1 ≠ 0) (hr2 : mapped r2 = true) (hf1 : -2048 ≤ off) (hf2 : off < 2048)
    (h0 : 0 ≤ ((st.x r1).toNat : Int) + off) (hwk : wok K (CallProbe.ea (st.x r1) off)) :
    ∃ s', Runs M s s' ∧
      Mid K C s0 (pc + 1, { st with m := CallProbe.upd st.m (CallProbe.ea (st.x r1) off) (st.x r2) }) 0 s' := by
  have hsl := armReg_lt hr1 r10
  have wl := hL.wlo; have wh := hL.whi
  have hwk' := hwk
  unfold wok at hwk'
  have st_at : ∀ k (s1 : M.State) (n f : Nat), Mid K C s0 (pc, st) k s1 → k < 4 → n < 31 → f % 8 = 0 → f < 32768 →
      ((M.observe s1).register n).toNat + f = CallProbe.ea (st.x r1) off →
      (M.observe s1).register (opR r2) = st.x r2 →
      (blockJ (.sd r2 r1 off)).getD k 0 = str (opR r2) n f →
      (∀ i, k + 1 ≤ i → i < 4 → (blockJ (.sd r2 r1 off)).getD i 0 = PAD) →
      ∃ s', Runs M s1 s' ∧
        Mid K C s0 (pc + 1, { st with m := CallProbe.upd st.m (CallProbe.ea (st.x r1) off) (st.x r2) }) 0 s' := by
    intro k s1 n f M1 hk hn hf8 hf hea hv e1 e2
    have w := word_pc M1 hC hB hpcl hk e1
    have g := S.str s1 _ n f M1.cfg (opR_lt hr2) hn hf8 hf (by omega) (by omega) (by omega) (by omega) w
    rw [hea, hv] at g
    obtain ⟨s2, r2', M2⟩ := mid_store8 M1 hL hR hpcl hk hwk g
    obtain ⟨s3, r3, M3⟩ := run_pads S hC hB hpcl (4 - (k + 1)) (k + 1) s2 (by omega) M2 e2
    exact ⟨s3, Runs.trans r2' r3, M3⟩
  have xr := hM.x r1 (by omega) (mapped_lt hr1)
  by_cases e : r2 = 0
  · subst e
    have w0 := word_pc hM hC hB hpcl (by decide) (w := movz 17 0) (by
      simp only [blockJ, body, zpre, if_true, pad4]; split <;> rfl)
    obtain ⟨s1, rr1, M1, o1⟩ := mid_scr hM (Or.inr rfl) (S.movz s 17 0 hM.cfg (by decide) (by decide) w0)
    have z1 : (M.observe s1).register 17 = 0 := by rw [o1]; simp [setReg]
    by_cases d : off % 8 = 0 ∧ 0 ≤ off ∧ off < 32768
    · have hb : blockJ (.sd 0 r1 off) = [movz 17 0, str 17 (armReg r1) off.toNat, PAD, PAD] := by
        simp [blockJ, body, pad4, zpre, d, opR]
      obtain ⟨s2, rr2, M2⟩ := st_at 1 s1 (armReg r1) off.toNat M1 (by decide) hsl (by omega) (by omega)
        (by rw [M1.x r1 (by omega) (mapped_lt hr1)]; simp [CallProbe.ea]; omega) (opR_val M1 hr2 (fun _ => z1))
        (by rw [hb]; rfl) (fun i h1 h2 => by rcases (by omega : i = 2 ∨ i = 3) with rfl | rfl <;> rw [hb] <;> rfl)
      exact ⟨s2, Runs.trans rr1 rr2, M2⟩
    · have hb : blockJ (.sd 0 r1 off) = [movz 17 0, addr16 r1 off, str 17 16 0, PAD] := by
        simp [blockJ, body, pad4, zpre, d, opR]
      obtain ⟨s2, rr2, M2, x16, x17⟩ := addr_x16 S M1 hC hB hpcl (by decide) hr1 r10 hf1 hf2 (by rw [hb]; rfl) h0
      obtain ⟨s3, rr3, M3⟩ := st_at 2 s2 16 0 M2 (by decide) (by decide) (by decide) (by decide)
        (by rw [x16, toNat_ofNat_lt (by omega), Nat.add_zero]) (opR_val M2 hr2 (fun _ => by rw [x17, z1]))
        (by rw [hb]; rfl) (fun i h1 h2 => by rw [show i = 3 by omega, hb]; rfl)
      exact ⟨s3, Runs.trans rr1 (Runs.trans rr2 rr3), M3⟩
  · by_cases d : off % 8 = 0 ∧ 0 ≤ off ∧ off < 32768
    · have hb : blockJ (.sd r2 r1 off) = [str (opR r2) (armReg r1) off.toNat, PAD, PAD, PAD] := by
        simp [blockJ, body, pad4, zpre, d, e]
      exact st_at 0 s (armReg r1) off.toNat hM (by decide) hsl (by omega) (by omega)
        (by rw [xr]; simp [CallProbe.ea]; omega) (opR_val hM hr2 (fun h => absurd h e))
        (by rw [hb]; rfl) (fun i h1 h2 => by rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl <;> rw [hb] <;> rfl)
    · have hb : blockJ (.sd r2 r1 off) = [addr16 r1 off, str (opR r2) 16 0, PAD, PAD] := by
        simp [blockJ, body, pad4, zpre, d, e]
      obtain ⟨s1, rr1, M1, x16, -⟩ := addr_x16 S hM hC hB hpcl (by decide) hr1 r10 hf1 hf2 (by rw [hb]; rfl) h0
      obtain ⟨s2, rr2, M2⟩ := st_at 1 s1 16 0 M1 (by decide) (by decide) (by decide) (by decide)
        (by rw [x16, toNat_ofNat_lt (by omega), Nat.add_zero]) (opR_val M1 hr2 (fun h => absurd h e))
        (by rw [hb]; rfl) (fun i h1 h2 => by rcases (by omega : i = 2 ∨ i = 3) with rfl | rfl <;> rw [hb] <;> rfl)
      exact ⟨s2, Runs.trans rr1 rr2, M2⟩

end JT
