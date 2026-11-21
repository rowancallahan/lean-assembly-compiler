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

end
end JT
