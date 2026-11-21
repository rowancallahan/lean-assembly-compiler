/- The NATIVE AArch64 generator's machine side (`C/GenArm.lean` at native-arm d6db803; M3 of
Testing/notes/NATIVE_ARM_PROOF_PLAN.md): the relation `NMid` between a machine state at an absolute code WORD index
`q` and a register/memory view `st` (a `CallProbe.St`: the A64 registers through `armReg`, the 8-byte cells), and the
steps of single A64 instructions on it, from `A64SemN`.  Unlike ArmTarget's `Mid` it has no J pc: a GenArm template is
a run `NMid … st q s → NMid … st' q' s'`, compared with the J template's run only at the template's ends (the anchors
of `GTarget`).  The scratch registers x16 / x17 are not part of `st`; a step that writes one returns the observation. -/
import Nano.V2Self.Proof.Machine.ArmTarget
import Nano.V2Self.Proof.Machine.A64SemN
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop}

/-- the machine state `s` at code word `q` of the A64 words `A` shows the view `st` -/
structure NMid (X W : M.State → Nat → Prop) (K : LayW) (A : List Nat) (s0 : M.State) (st : CallProbe.St) (q : Nat)
    (s : M.State) : Prop where
  cfg : M.configured s
  pc : (M.observe s).programCounter = UInt64.ofNat (K.base + 4 * q)
  code : ∀ i (h : i < A.length), WordAt (M.observe s) (K.base + 4 * i) A[i]
  x0 : st.x 0 = 0
  x : ∀ j, 0 < j → j < 32 → (M.observe s).register (armReg j) = st.x j
  keep : ∀ r, (∀ j, 0 < j → j < 32 → armReg j ≠ r) → r ∉ armScratch →
    (M.observe s).register r = (M.observe s0).register r
  w : ∀ a, wok K a → ∀ k < 8, (M.observe s).memory (UInt64.ofNat (a + k)) = some (cbyte (st.m a) k)
  bw : ∀ a, io K a → (M.observe s).memory (UInt64.ofNat a) = some (cbyte (st.m (a - a % 8)) (a % 8))
  fr : ∀ a, a < 2 ^ 64 → ¬ wok K (a - a % 8) → ¬ outB K a →
    (M.observe s).memory (UInt64.ofNat a) = (K.m0 a).map UInt8.ofBitVec
  lay : JTarget.LayOK M (4 * A.length) K
  pm : PermOK X W K (4 * A.length) s

variable {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St} {q : Nat}

/-- a step that keeps memory: new registers, new pc -/
theorem nmid_regs (hM : NMid X W K A s0 st q s) {s' : M.State} {st' : CallProbe.St} {q' : Nat}
    (hcfg : M.configured s') (hkp : Keep X W s s')
    (hpc : (M.observe s').programCounter = UInt64.ofNat (K.base + 4 * q'))
    (hmem : (M.observe s').memory = (M.observe s).memory)
    (hx : ∀ j, 0 < j → j < 32 → (M.observe s').register (armReg j) = st'.x j)
    (hkeep : ∀ r, (∀ j, 0 < j → j < 32 → armReg j ≠ r) → r ∉ armScratch →
      (M.observe s').register r = (M.observe s).register r)
    (h0 : st'.x 0 = 0) (hm : st'.m = st.m) : NMid X W K A s0 st' q' s' where
  cfg := hcfg
  pc := hpc
  code := fun i h b hb => by rw [hmem]; exact hM.code i h b hb
  x0 := h0
  x := hx
  keep := fun r h1 h2 => by rw [hkeep r h1 h2]; exact hM.keep r h1 h2
  w := fun a ha k hk => by rw [hmem, hm]; exact hM.w a ha k hk
  bw := fun a ha => by rw [hmem, hm]; exact hM.bw a ha
  fr := fun a ha h1 h2 => by rw [hmem]; exact hM.fr a ha h1 h2
  lay := hM.lay
  pm := perm_keep hM.pm hkp

/-- the word at the pc -/
theorem nmid_word (hM : NMid X W K A s0 st q s) {w : Nat} (hA : A[q]? = some w) (hB : K.base + 4 * A.length ≤ 2 ^ 32) :
    WordAt (M.observe s) (M.observe s).programCounter.toNat w := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 hA
  have e : (UInt64.ofNat (K.base + 4 * q)).toNat = K.base + 4 * q := by simp; omega
  rw [hM.pc, e, ← heq]; exact hM.code q hlt

/-- the following word -/
theorem nmid_word1 (hM : NMid X W K A s0 st q s) {w : Nat} (hA : A[q + 1]? = some w)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32) : WordAt (M.observe s) ((M.observe s).programCounter.toNat + 4) w := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 hA
  have e : (UInt64.ofNat (K.base + 4 * q)).toNat = K.base + 4 * q := by simp; omega
  rw [hM.pc, e, ← heq, show K.base + 4 * q + 4 = K.base + 4 * (q + 1) by omega]; exact hM.code (q + 1) hlt

theorem nmid_pcN (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32) (hq : q < A.length) :
    (M.observe s).programCounter.toNat = K.base + 4 * q := by rw [hM.pc]; simp; omega

theorem nmid_pcok (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32) (hq : q < A.length) :
    PcOK M (M.observe s) := by
  have := hM.lay.b4; have := hM.lay.blo; have := hM.lay.bhi
  unfold PcOK; rw [nmid_pcN hM hB hq]; omega

/-- `n` bytes at the pc are executable (`n = 4`: the word; `n = 8`: also the next one) -/
theorem nmid_fx (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32) {n : Nat}
    (hq : 4 * q + n ≤ 4 * A.length) (hn : 0 < n) : FetchX M X s n := by
  intro i hi; rw [nmid_pcN hM hB (by omega)]; exact hM.pm.1 _ (by omega) (by omega)

/-- a scratch write (x16 / x17) that falls through: the view is unchanged -/
theorem nmid_scr (hM : NMid X W K A s0 st q s) {d : Nat} (hd : d = 16 ∨ d = 17) {v : UInt64}
    (hg : GoesK M X W s (setReg (M.observe s) d v)) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st (q + 1) s' ∧ M.observe s' = setReg (M.observe s) d v := by
  obtain ⟨s', r, c, o, kp⟩ := hg
  refine ⟨s', r, ?_, o⟩
  refine nmid_regs hM c kp (by rw [o]; simp only [setReg]; rw [hM.pc, ofNat_add4]; congr 1)
    (by rw [o]; rfl) (fun j h0 h32 => ?_) (fun r' _ hr => ?_) hM.x0 rfl
  · rw [o]; simp only [setReg]
    have := @armReg_ne_scr j
    rw [if_neg (by omega)]; exact hM.x j h0 h32
  · rw [o]; simp only [setReg]
    rw [if_neg (by intro e; subst e; simp [armScratch] at hr; omega)]

/-- a write of the register of J register `rd` (≠ x0, mapped), falling through -/
theorem nmid_set (hM : NMid X W K A s0 st q s) {rd : Nat} (hrd : mapped rd = true) (h0 : rd ≠ 0) {v : UInt64}
    (hg : GoesK M X W s (setReg (M.observe s) (armReg rd) v)) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st rd v) (q + 1) s' := by
  obtain ⟨s', r, c, o, kp⟩ := hg
  refine ⟨s', r, nmid_regs hM c kp (by rw [o]; simp only [setReg]; rw [hM.pc, ofNat_add4]; congr 1)
    (by rw [o]; rfl) (fun j hj0 h32 => ?_) (fun r' hr _ => ?_) ?_ ?_⟩
  · rw [o]; simp only [setReg]
    by_cases e : j = rd
    · subst e; simp [CallProbe.wr, h0, CallProbe.upd]
    · rw [if_neg (fun h => e (armReg_inj hrd h32 h)), hM.x j hj0 h32]
      simp [CallProbe.wr, h0, CallProbe.upd, e]
  · rw [o]; simp only [setReg]
    rw [if_neg (fun h => hr rd (by omega) (mapped_lt hrd) h.symm)]
  · simp [CallProbe.wr, h0, CallProbe.upd, hM.x0]; omega
  · simp [CallProbe.wr, h0]

/-- a jump that changes no register, to word `q'` -/
theorem nmid_jump (hM : NMid X W K A s0 st q s) {q' : Nat}
    (hg : GoesK M X W s (jumpTo (M.observe s) (UInt64.ofNat (K.base + 4 * q')))) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st q' s' := by
  obtain ⟨s', r, c, o, kp⟩ := hg
  exact ⟨s', r, nmid_regs hM c kp (by rw [o]; rfl) (by rw [o]; rfl) (fun j h0 h32 => by rw [o]; exact hM.x j h0 h32)
    (fun r' _ _ => by rw [o]; rfl) hM.x0 rfl⟩

/-! ## single instructions (register forms) -/

section
variable (S : A64SemN M X W) (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
include S hM hB

/-- `movz xd, #i` -/
theorem n_movz {d i : Nat} (hA : A[q]? = some (ArmEnc.movz (armReg d) i)) (hd : mapped d = true) (h0 : d ≠ 0)
    (hi : i < 2 ^ 16) : ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (UInt64.ofNat i)) (q + 1) s' :=
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  nmid_set hM hd h0 (S.movz s _ i hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (armReg_lt hd h0) hi (nmid_word hM hA hB))

/-- `movn xd, #i, lsl 16h` -/
theorem n_movn {d i h : Nat} (hA : A[q]? = some (ArmEnc.movn (armReg d) i h)) (hd : mapped d = true) (h0 : d ≠ 0)
    (hi : i < 2 ^ 16) (hh : h < 4) : ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (movnV i h)) (q + 1) s' :=
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  nmid_set hM hd h0 (S.movn s _ i h hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (armReg_lt hd h0) hi hh (nmid_word hM hA hB))

/-- `movk xd, #i, lsl 16h` -/
theorem n_movk {d i h : Nat} (hA : A[q]? = some (ArmEnc.movk (armReg d) i h)) (hd : mapped d = true) (h0 : d ≠ 0)
    (hi : i < 2 ^ 16) (hh : h < 4) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (movkV (st.x d) i h)) (q + 1) s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have := S.movk s _ i h hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (armReg_lt hd h0) hi hh (nmid_word hM hA hB)
  rw [hM.x d (by omega) (mapped_lt hd)] at this
  exact nmid_set hM hd h0 this

/-- `add xd, xn, #i` -/
theorem n_addi {d n i : Nat} (hA : A[q]? = some (ArmEnc.addi (armReg d) (armReg n) i)) (hd : mapped d = true)
    (h0 : d ≠ 0) (hn : mapped n = true) (hn0 : n ≠ 0) (hi : i < 4096) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (st.x n + UInt64.ofNat i)) (q + 1) s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have := S.addi s _ _ i hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (armReg_lt hd h0) (armReg_lt hn hn0) hi (nmid_word hM hA hB)
  rw [hM.x n (by omega) (mapped_lt hn)] at this
  exact nmid_set hM hd h0 this

/-- `sub xd, xn, #i` -/
theorem n_subi {d n i : Nat} (hA : A[q]? = some (ArmEnc.subi (armReg d) (armReg n) i)) (hd : mapped d = true)
    (h0 : d ≠ 0) (hn : mapped n = true) (hn0 : n ≠ 0) (hi : i < 4096) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (st.x n - UInt64.ofNat i)) (q + 1) s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have := S.subi s _ _ i hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (armReg_lt hd h0) (armReg_lt hn hn0) hi (nmid_word hM hA hB)
  rw [hM.x n (by omega) (mapped_lt hn)] at this
  exact nmid_set hM hd h0 this

/-- `add xd, xn, xm, lsl #3` into scratch x16 (the buffer cell address) -/
theorem n_addLsl3_16 {n m : Nat} (hA : A[q]? = some (ArmEnc.addLsl3 16 (armReg n) (armReg m))) (hn : mapped n = true)
    (hn0 : n ≠ 0) (hm : mapped m = true) (hm0 : m ≠ 0) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st (q + 1) s' ∧
      (M.observe s').register 16 = st.x n + (st.x m <<< 3) := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have := S.addLsl3 s 16 _ _ hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (by decide) (armReg_lt hn hn0) (armReg_lt hm hm0) (nmid_word hM hA hB)
  rw [hM.x n (by omega) (mapped_lt hn), hM.x m (by omega) (mapped_lt hm)] at this
  obtain ⟨s', r, N, o⟩ := nmid_scr hM (Or.inl rfl) this
  exact ⟨s', r, N, by rw [o]; simp [setReg]⟩

/-- `b f` to word `q'` -/
theorem n_b {q' : Nat} (hA : A[q]? = some (ArmEnc.bB ((q' : Int) - q))) (hq' : q' ≤ A.length)
    (hL : A.length < 2 ^ 25) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st q' s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have := S.b s ((q' : Int) - q) hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (by omega) (by omega) (nmid_word hM hA hB)
  rw [hM.pc, ofNat_addInt _ _ (by omega) (by omega),
    show ((K.base + 4 * q : Nat) : Int) + 4 * ((q' : Int) - q) = ((K.base + 4 * q' : Nat) : Int) by omega,
    Int.toNat_natCast] at this
  exact nmid_jump hM this

/-- `add/sub/and/orr/lslv/lsrv/eor xd, xn, xm` (not `madd`: op ≠ 3) -/
theorem n_alu {op d n m : Nat} (hA : A[q]? = some (ArmEnc.rr (ArmEnc.aluC op) (armReg d) (armReg n) (armReg m)))
    (h1 : 1 ≤ op) (h2 : op ≤ 8) (h3 : op ≠ 3) (hd : mapped d = true) (h0 : d ≠ 0) (hn : mapped n = true) (hn0 : n ≠ 0)
    (hm : mapped m = true) (hm0 : m ≠ 0) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (CallProbe.aluf op (st.x n) (st.x m))) (q + 1) s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have := S.alu s op _ _ _ hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega)) h1 h2
    (armReg_lt hd h0) (armReg_lt hn hn0) (armReg_lt hm hm0) (nmid_word hM hA hB)
  rw [hM.x n (by omega) (mapped_lt hn), hM.x m (by omega) (mapped_lt hm), aluV_eq op _ _ _ (Or.inl h3)] at this
  exact nmid_set hM hd h0 this

/-- `cbz xt, f` to word `q'` -/
theorem n_cbz {t q' : Nat} (hA : A[q]? = some (ArmEnc.cbz (armReg t) ((q' : Int) - q))) (ht : mapped t = true)
    (ht0 : t ≠ 0) (hq' : q' ≤ A.length) (hL : A.length < 2 ^ 18) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st (if st.x t = 0 then q' else q + 1) s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have := S.cbz s _ ((q' : Int) - q) hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (armReg_lt ht ht0) (by omega) (by omega) (nmid_word hM hA hB)
  rw [hM.x t (by omega) (mapped_lt ht), hM.pc, ofNat_addInt _ _ (by omega) (by omega),
    show ((K.base + 4 * q : Nat) : Int) + 4 * ((q' : Int) - q) = ((K.base + 4 * q' : Nat) : Int) by omega,
    Int.toNat_natCast, ofNat_add4] at this
  split
  · rename_i h; rw [if_pos h] at this; exact nmid_jump hM this
  · rename_i h; rw [if_neg h] at this; exact nmid_jump hM (by rw [show K.base + 4 * (q + 1) = K.base + 4 * q + 4 by omega]; exact this)

/-- `cbnz xt, f` to word `q'` -/
theorem n_cbnz {t q' : Nat} (hA : A[q]? = some (ArmEnc.cbnz (armReg t) ((q' : Int) - q))) (ht : mapped t = true)
    (ht0 : t ≠ 0) (hq' : q' ≤ A.length) (hL : A.length < 2 ^ 18) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st (if st.x t = 0 then q + 1 else q') s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have := S.cbnz s _ ((q' : Int) - q) hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (armReg_lt ht ht0) (by omega) (by omega) (nmid_word hM hA hB)
  rw [hM.x t (by omega) (mapped_lt ht), hM.pc, ofNat_addInt _ _ (by omega) (by omega),
    show ((K.base + 4 * q : Nat) : Int) + 4 * ((q' : Int) - q) = ((K.base + 4 * q' : Nat) : Int) by omega,
    Int.toNat_natCast, ofNat_add4] at this
  split
  · rename_i h; rw [if_pos h] at this; exact nmid_jump hM (by rw [show K.base + 4 * (q + 1) = K.base + 4 * q + 4 by omega]; exact this)
  · rename_i h; rw [if_neg h] at this; exact nmid_jump hM this

/-- `subs x16, xn, xm; b.cond f` (c: EQ 0, NE 1, HS 2, LO 3) to word `q'` (offset from the `b.cond`) -/
theorem n_cmpbr {c n m q' : Nat} (hA : A[q]? = some (ArmEnc.subsR (armReg n) (armReg m)))
    (hA1 : A[q + 1]? = some (ArmEnc.bc c ((q' : Int) - (q + 1)))) (hc : c < 4) (hn : mapped n = true) (hn0 : n ≠ 0)
    (hm : mapped m = true) (hm0 : m ≠ 0) (hq' : q' ≤ A.length) (hL : A.length < 2 ^ 18) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st (if condV c (st.x n) (st.x m) then q' else q + 2) s' := by
  have hq1 := (List.getElem?_eq_some_iff.1 hA1).1
  have hR := S.ram.2; have hbh := hM.lay.bhi
  have hg := S.cmpbr s c _ _ ((q' : Int) - (q + 1)) hM.cfg (nmid_pcok hM hB (by omega)) (nmid_fx hM hB (by omega) (by omega))
    hc (armReg_lt hn hn0) (armReg_lt hm hm0) (by omega) (by omega)
    (by rw [nmid_pcN hM hB (by omega)]; omega) (nmid_word hM hA hB) (nmid_word1 hM hA1 hB)
  rw [hM.x n (by omega) (mapped_lt hn), hM.x m (by omega) (mapped_lt hm)] at hg
  obtain ⟨s', r, cf, o, kp⟩ := hg
  refine ⟨s', r, nmid_regs hM cf kp ?_ (by rw [o]) (fun j h0 h32 => ?_) (fun r' _ hr => ?_) hM.x0 rfl⟩
  · rw [o]; simp only []
    split
    · rw [hM.pc, ofNat_add4, ofNat_addInt _ _ (by omega) (by omega),
        show ((K.base + 4 * q + 4 : Nat) : Int) + 4 * ((q' : Int) - (q + 1)) = ((K.base + 4 * q' : Nat) : Int) by omega,
        Int.toNat_natCast]
    · rw [hM.pc]; apply UInt64.toNat_inj.1; simp; omega
  · rw [o]; simp only []
    have := @armReg_ne_scr j
    rw [if_neg (by omega)]; exact hM.x j h0 h32
  · rw [o]; simp only []
    rw [if_neg (by intro e; subst e; simp [armScratch] at hr)]

/-- an 8-byte store to the work cell `a` -/
theorem nmid_store8 {a : Nat} (ha : wok K a) {v : UInt64} (hg : GoesK M X W s (store8 (M.observe s) a v)) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 { st with m := CallProbe.upd st.m a v } (q + 1) s' := by
  obtain ⟨s', r, c, o, kp⟩ := hg
  have hL := hM.lay; have hR := S.ram.2
  have hwa := hL.wlo; have hwb := hL.whi; have hcw := hL.cw; have hbh := hL.bhi
  have hib := hL.ibh; have hob := hL.obh; have hil := hL.ibl; have hol := hL.obl
  unfold wok at ha
  refine ⟨s', r, ⟨c, by rw [o]; simp only [store8]; rw [hM.pc, ofNat_add4]; congr 1, ?_, hM.x0,
    fun j h0 h32 => by rw [o]; exact hM.x j h0 h32, fun r' h1 h2 => by rw [o]; exact hM.keep r' h1 h2, ?_, ?_, ?_,
    hM.lay, perm_keep hM.pm kp⟩⟩
  · intro i h b hb
    rw [o]; simp only [store8]
    rw [toNat_ofNat_lt (by omega), if_neg (by omega)]
    exact hM.code i h b hb
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

/-- `ldr xd, [xb, #f]` from the work cell `a = x[b] + f` (`nb`: any register < 31 holding `bv`, e.g. x16) -/
theorem n_ldr {d nb f a : Nat} {bv : UInt64} (hA : A[q]? = some (ArmEnc.ldr (armReg d) nb f)) (hd : mapped d = true)
    (h0 : d ≠ 0) (hnb : nb < 31) (hbv : (M.observe s).register nb = bv) (hf8 : f % 8 = 0) (hf : f < 32768)
    (ha : a = bv.toNat + f) (hw : wok K a) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (st.m a)) (q + 1) s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have hL := hM.lay; have hR := S.ram.2; have hwa := hL.wlo; have hwb := hL.whi
  have hw' := hw; unfold wok at hw'
  subst ha
  exact nmid_set hM hd h0 (S.ldr s _ nb f (st.m (bv.toNat + f)) hM.cfg (nmid_pcok hM hB hq)
    (nmid_fx hM hB (by omega) (by omega)) (armReg_lt hd h0) hnb hf8 hf (by rw [hbv]; omega) (by rw [hbv]; omega)
    (by rw [hbv]; omega) (by rw [hbv]; omega)
    (fun k hk => by rw [hbv]; exact hM.pm.2 _ (Or.inl (by omega)))
    (fun k hk => by rw [hbv]; exact hM.w _ hw k hk) (nmid_word hM hA hB))

/-- `str xt, [xb, #f]` to the work cell `a = x[b] + f` (`nt`, `nb`: any registers < 31 holding `v`, `bv`) -/
theorem n_str {nt nb f a : Nat} {v bv : UInt64} (hA : A[q]? = some (ArmEnc.str nt nb f)) (hnt : nt < 31)
    (hv : (M.observe s).register nt = v) (hnb : nb < 31) (hbv : (M.observe s).register nb = bv) (hf8 : f % 8 = 0)
    (hf : f < 32768) (ha : a = bv.toNat + f) (hw : wok K a) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 { st with m := CallProbe.upd st.m a v } (q + 1) s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have hL := hM.lay; have hR := S.ram.2; have hwa := hL.wlo; have hwb := hL.whi
  have hw' := hw; unfold wok at hw'
  subst ha
  have := S.str s nt nb f hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega)) hnt hnb hf8 hf
    (by rw [hbv]; omega) (by rw [hbv]; omega) (by rw [hbv]; omega) (by rw [hbv]; omega)
    (fun k hk => by rw [hbv]; exact hM.pm.2 _ (Or.inl (by omega))) (nmid_word hM hA hB)
  rw [hbv, hv] at this
  exact nmid_store8 S hM hB hw this

/-- `ldur xd, [xb, #f]` (−256 ≤ f < 256) from the work cell `a = x[b] + f` -/
theorem n_ldur {d nb a : Nat} {f : Int} {bv : UInt64} (hA : A[q]? = some (ArmEnc.ldur (armReg d) nb f))
    (hd : mapped d = true) (h0 : d ≠ 0) (hnb : nb < 31) (hbv : (M.observe s).register nb = bv) (hf1 : -256 ≤ f)
    (hf2 : f < 256) (ha : (a : Int) = bv.toNat + f) (hw : wok K a) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (st.m a)) (q + 1) s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have hL := hM.lay; have hR := S.ram.2; have hwa := hL.wlo; have hwb := hL.whi
  have hw' := hw; unfold wok at hw'
  exact nmid_set hM hd h0 (S.ldur s _ nb a f (st.m a) hM.cfg (nmid_pcok hM hB hq)
    (nmid_fx hM hB (by omega) (by omega)) (armReg_lt hd h0) hnb hf1 hf2 (by rw [hbv]; exact ha) hw'.2.2
    (by omega) (by omega) (fun k hk => hM.pm.2 _ (Or.inl (by omega))) (fun k hk => hM.w _ hw k hk)
    (nmid_word hM hA hB))

/-- `stur xt, [xb, #f]` to the work cell `a = x[b] + f` -/
theorem n_stur {nt nb a : Nat} {f : Int} {v bv : UInt64} (hA : A[q]? = some (ArmEnc.stur nt nb f)) (hnt : nt < 31)
    (hv : (M.observe s).register nt = v) (hnb : nb < 31) (hbv : (M.observe s).register nb = bv) (hf1 : -256 ≤ f)
    (hf2 : f < 256) (ha : (a : Int) = bv.toNat + f) (hw : wok K a) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 { st with m := CallProbe.upd st.m a v } (q + 1) s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have hL := hM.lay; have hR := S.ram.2; have hwa := hL.wlo; have hwb := hL.whi
  have hw' := hw; unfold wok at hw'
  have := S.stur s nt nb a f hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega)) hnt hnb hf1 hf2
    (by rw [hbv]; exact ha) hw'.2.2 (by omega) (by omega) (fun k hk => hM.pm.2 _ (Or.inl (by omega)))
    (nmid_word hM hA hB)
  rw [hv] at this
  exact nmid_store8 S hM hB hw this

/-- `ldp xt, xu, [xb]` from the work cells `a = x[b]`, `a + 8` (`t ≠ u`) -/
theorem n_ldp {dt du nb : Nat} {bv : UInt64} (hA : A[q]? = some (ArmEnc.ldp (armReg dt) (armReg du) nb))
    (hdt : mapped dt = true) (ht0 : dt ≠ 0) (hdu : mapped du = true) (hu0 : du ≠ 0) (hne : dt ≠ du) (hnb : nb < 31)
    (hbv : (M.observe s).register nb = bv) (hw : wok K bv.toNat) (hw8 : wok K (bv.toNat + 8)) :
    ∃ s', Runs M s s' ∧
      NMid X W K A s0 (CallProbe.wr (CallProbe.wr st dt (st.m bv.toNat)) du (st.m (bv.toNat + 8))) (q + 1) s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have hL := hM.lay; have hR := S.ram.2; have hwa := hL.wlo; have hwb := hL.whi
  have hw' := hw; have hw8' := hw8; unfold wok at hw' hw8'
  have h16 : bv.toNat + 16 ≤ K.hi := by have := hw8'.2.1; omega
  have hlo : K.lo ≤ bv.toNat := hw'.1
  have hna : armReg dt ≠ armReg du := fun h => hne (armReg_inj hdu (mapped_lt hdt) h)
  obtain ⟨s', r, c, o, kp⟩ := S.ldp s _ _ nb (st.m bv.toNat) (st.m (bv.toNat + 8)) hM.cfg (nmid_pcok hM hB hq)
    (nmid_fx hM hB (by omega) (by omega)) (armReg_lt hdt ht0) (armReg_lt hdu hu0) hnb hna (by rw [hbv]; exact hw'.2.2)
    (by rw [hbv]; omega) (by rw [hbv]; omega)
    (fun k hk => by rw [hbv]; exact hM.pm.2 _ (Or.inl (by omega)))
    (fun k hk => by rw [hbv]; exact hM.w _ hw k hk) (fun k hk => by rw [hbv]; exact hM.w _ hw8 k hk)
    (nmid_word hM hA hB)
  refine ⟨s', r, nmid_regs hM c kp (by rw [o]; simp only [setReg2]; rw [hM.pc, ofNat_add4]; congr 1)
    (by rw [o]; rfl) (fun j hj0 h32 => ?_) (fun r' hr _ => ?_) ?_ ?_⟩
  · rw [o]; simp only [setReg2]
    by_cases e : j = du
    · subst e; simp [CallProbe.wr, hu0, CallProbe.upd]
    · rw [if_neg (fun h => e (armReg_inj hdu h32 h))]
      by_cases e2 : j = dt
      · subst e2; simp [CallProbe.wr, hu0, ht0, CallProbe.upd, e]
      · rw [if_neg (fun h => e2 (armReg_inj hdt h32 h)), hM.x j hj0 h32]
        simp [CallProbe.wr, hu0, ht0, CallProbe.upd, e, e2]
  · rw [o]; simp only [setReg2]
    rw [if_neg (fun h => hr du (by omega) (mapped_lt hdu) h.symm),
      if_neg (fun h => hr dt (by omega) (mapped_lt hdt) h.symm)]
  · simp [CallProbe.wr, hu0, ht0, CallProbe.upd, hM.x0, Ne.symm hu0, Ne.symm ht0]
  · simp [CallProbe.wr, hu0, ht0]

/-- `bl f` to word `q'`: x30 (J's ra) := the address of the next word -/
theorem n_bl {q' : Nat} (hA : A[q]? = some (ArmEnc.blB ((q' : Int) - q))) (hq' : q' ≤ A.length)
    (hL : A.length < 2 ^ 25) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st 1 (UInt64.ofNat (K.base + 4 * (q + 1)))) q' s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  obtain ⟨s', r, c, o, kp⟩ := S.bl s ((q' : Int) - q) hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (by omega) (by omega) (nmid_word hM hA hB)
  rw [hM.pc, ofNat_addInt _ _ (by omega) (by omega),
    show ((K.base + 4 * q : Nat) : Int) + 4 * ((q' : Int) - q) = ((K.base + 4 * q' : Nat) : Int) by omega,
    Int.toNat_natCast, ofNat_add4] at o
  refine ⟨s', r, nmid_regs hM c kp (by rw [o]) (by rw [o]) (fun j hj0 h32 => ?_) (fun r' hr _ => ?_) ?_ ?_⟩
  · rw [o]; simp only []
    by_cases e : j = 1
    · subst e
      have : ∀ v, (CallProbe.wr st 1 v).x 1 = v := fun v => by simp [CallProbe.wr, CallProbe.upd]
      rw [this, if_pos (show armReg 1 = 30 from rfl)]; congr 1
    · rw [if_neg (show armReg j ≠ 30 from fun h => e (armReg_inj (r := 1) (by decide) h32 h)), hM.x j hj0 h32]
      simp [CallProbe.wr, CallProbe.upd, e]
  · rw [o]; simp only []
    rw [if_neg (show r' ≠ 30 from fun h => hr 1 (by omega) (by omega) h.symm)]
  · simp [CallProbe.wr, CallProbe.upd, hM.x0]
  · simp [CallProbe.wr]

/-- `br xn`: to the address in J register `n`, when that is the code word `q'` -/
theorem n_br {n q' : Nat} (hA : A[q]? = some (ArmEnc.brR (armReg n))) (hn : mapped n = true) (hn0 : n ≠ 0)
    (hv : st.x n = UInt64.ofNat (K.base + 4 * q')) : ∃ s', Runs M s s' ∧ NMid X W K A s0 st q' s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have := S.br s _ hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega)) (armReg_lt hn hn0)
    (nmid_word hM hA hB)
  rw [hM.x n (by omega) (mapped_lt hn), hv] at this
  exact nmid_jump hM this

/-- `movz x17, #0; madd xd, xn, xm, x17` (mul) -/
theorem n_mul {d n m : Nat} (hA : A[q]? = some (ArmEnc.movz 17 0))
    (hA1 : A[q + 1]? = some (ArmEnc.rr (ArmEnc.aluC 3) (armReg d) (armReg n) (armReg m)))
    (hd : mapped d = true) (h0 : d ≠ 0) (hn : mapped n = true) (hn0 : n ≠ 0) (hm : mapped m = true) (hm0 : m ≠ 0) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (CallProbe.aluf 3 (st.x n) (st.x m))) (q + 2) s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have hq1 := (List.getElem?_eq_some_iff.1 hA1).1
  obtain ⟨s1, r1, N1, o1⟩ := nmid_scr hM (Or.inr rfl) (S.movz s 17 0 hM.cfg (nmid_pcok hM hB hq)
    (nmid_fx hM hB (by omega) (by omega)) (by decide) (by decide) (nmid_word hM hA hB))
  have z17 : (M.observe s1).register 17 = 0 := by rw [o1]; simp [setReg]
  have := S.alu s1 3 _ _ _ N1.cfg (nmid_pcok N1 hB hq1) (nmid_fx N1 hB (by omega) (by omega)) (by decide) (by decide)
    (armReg_lt hd h0) (armReg_lt hn hn0) (armReg_lt hm hm0) (nmid_word N1 hA1 hB)
  rw [N1.x n (by omega) (mapped_lt hn), N1.x m (by omega) (mapped_lt hm), z17, aluV_eq 3 _ _ _ (Or.inr rfl)] at this
  obtain ⟨s2, r2, N2⟩ := nmid_set N1 hd h0 this
  exact ⟨s2, Runs.trans r1 r2, N2⟩

/-- a readable byte (`bok`: in a work cell, or an input/output byte) as the view shows it -/
theorem nmid_byte {a : Nat} (ha : bok K a) :
    (M.observe s).memory (UInt64.ofNat a) = some (cbyte (st.m (a - a % 8)) (a % 8)) ∧
      M.ramStart ≤ a ∧ a < M.ramEnd ∧ W s a := by
  have hL := hM.lay
  have wl := hL.wlo; have wh := hL.whi; have il := hL.ibl; have ih := hL.ibh; have ol := hL.obl; have oh := hL.obh
  have hW : W s a := hM.pm.2 _ (by unfold bok wok io outB at ha; unfold DataK; omega)
  rcases ha with hw | hio
  · have := hM.w _ hw (a % 8) (Nat.mod_lt _ (by decide))
    rw [show a - a % 8 + a % 8 = a by omega] at this
    unfold wok at hw
    exact ⟨this, by omega, by omega, hW⟩
  · refine ⟨hM.bw a hio, ?_, ?_, hW⟩ <;> (unfold io outB at hio; omega)

/-- `ldrb wd, [xn, xm]` of the byte at `x[n] + x[m]` -/
theorem n_ldrbR {d n m : Nat} (hA : A[q]? = some (ArmEnc.ldrbR (armReg d) (armReg n) (armReg m)))
    (hd : mapped d = true) (h0 : d ≠ 0) (hn : mapped n = true) (hn0 : n ≠ 0) (hm : mapped m = true) (hm0 : m ≠ 0)
    (hb : bok K ((st.x n).toNat + (st.x m).toNat)) :
    ∃ s', Runs M s s' ∧
      NMid X W K A s0 (CallProbe.wr st d (CallProbe.lbm st.m ((st.x n).toNat + (st.x m).toNat))) (q + 1) s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  obtain ⟨hby, hlo, hhi, hW⟩ := nmid_byte S hM hB hb
  have := S.ldrbR s _ _ _ _ hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (armReg_lt hd h0) (armReg_lt hn hn0) (armReg_lt hm hm0)
    (by rw [hM.x n (by omega) (mapped_lt hn), hM.x m (by omega) (mapped_lt hm)]; exact hlo)
    (by rw [hM.x n (by omega) (mapped_lt hn), hM.x m (by omega) (mapped_lt hm)]; exact hhi)
    (by rw [hM.x n (by omega) (mapped_lt hn), hM.x m (by omega) (mapped_lt hm)]; exact hW)
    (by rw [hM.x n (by omega) (mapped_lt hn), hM.x m (by omega) (mapped_lt hm)]; exact hby) (nmid_word hM hA hB)
  rw [← lbm_cbyte] at this
  exact nmid_set hM hd h0 this

end
end JT
