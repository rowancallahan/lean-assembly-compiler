/- T12 (M3): GenArm's stubs (words 0-10) and start code (34 words, incl. the byte copy loop) as A64 runs on `NMid`.
Exits (`br x30` out of the code, to an address read from memory) end in `NOut`: `NMid` without the code-word pc.
Section "for ArmNat" = helpers meant to move to ArmNat.lean. -/
import Nano.Run.NatT.Base
namespace JT
open Proven.Top SimW CallProbe ArmEnc

variable {M : Machine} {X W : M.State → Nat → Prop} {K : LayW} {A : List Nat} {s0 s : M.State} {st : CallProbe.St}

/-! ## for ArmNat -/

/-- `nmid_set` that also returns the observation -/
theorem nmid_set' {q : Nat} (hM : NMid X W K A s0 st q s) {rd : Nat} (hrd : mapped rd = true) (h0 : rd ≠ 0) {v : UInt64}
    (hg : GoesK M X W s (setReg (M.observe s) (armReg rd) v)) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st rd v) (q + 1) s' ∧
      M.observe s' = setReg (M.observe s) (armReg rd) v := by
  obtain ⟨s', r, c, o, kp⟩ := hg
  refine ⟨s', r, nmid_regs hM c kp (by rw [o]; simp only [setReg]; rw [hM.pc, ofNat_add4]; congr 1)
    (by rw [o]; rfl) (fun j hj0 h32 => ?_) (fun r' hr _ => ?_) ?_ ?_, o⟩
  · rw [o]; simp only [setReg]
    by_cases e : j = rd
    · subst e; simp [CallProbe.wr, h0, CallProbe.upd]
    · rw [if_neg (fun h => e (armReg_inj hrd h32 h)), hM.x j hj0 h32]
      simp [CallProbe.wr, h0, CallProbe.upd, e]
  · rw [o]; simp only [setReg]
    rw [if_neg (fun h => hr rd (by omega) (mapped_lt hrd) h.symm)]
  · simp [CallProbe.wr, h0, CallProbe.upd, hM.x0]; omega
  · simp [CallProbe.wr, h0]

/-- `movz x16/x17, #i`: the scratch register holds `i` afterwards -/
theorem n_movzS (S : A64SemN M X W) {q : Nat} (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    {d i : Nat} (hA : A[q]? = some (ArmEnc.movz d i)) (hd : d = 16 ∨ d = 17) (hi : i < 2 ^ 16) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st (q + 1) s' ∧ (M.observe s').register d = UInt64.ofNat i := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  obtain ⟨s', r, N, o⟩ := nmid_scr hM hd (S.movz s d i hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega))
    (by omega) hi (nmid_word hM hA hB))
  exact ⟨s', r, N, by rw [o]; simp [setReg]⟩

/-- `lslv/lsrv/… xd, xn, x16` with x16 = `z` (the shift amount): x16 is kept -/
theorem n_alu16 (S : A64SemN M X W) {q : Nat} (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    {op d n : Nat} {z : UInt64} (hA : A[q]? = some (ArmEnc.rr (ArmEnc.aluC op) (armReg d) (armReg n) 16))
    (h1 : 1 ≤ op) (h2 : op ≤ 8) (h3 : op ≠ 3) (hd : mapped d = true) (h0 : d ≠ 0) (hn : mapped n = true) (hn0 : n ≠ 0)
    (hz : (M.observe s).register 16 = z) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st d (CallProbe.aluf op (st.x n) z)) (q + 1) s' ∧
      (M.observe s').register 16 = z := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have := S.alu s op _ _ _ hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega)) h1 h2
    (armReg_lt hd h0) (armReg_lt hn hn0) (by decide) (nmid_word hM hA hB)
  rw [hM.x n (by omega) (mapped_lt hn), hz, aluV_eq op _ _ _ (Or.inl h3)] at this
  obtain ⟨s', r, N, o⟩ := nmid_set' hM hd h0 this
  have e := (armReg_ne_scr (j := d)).1
  exact ⟨s', r, N, by rw [o]; simp [setReg, Ne.symm e, hz]⟩

/-- a byte store to `a` -/
theorem nmid_store1 (S : A64SemN M X W) {q : Nat} (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    {a : Nat} (hs : sok K a) {v : UInt64} (hg : GoesK M X W s (store1 (M.observe s) a v)) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 { st with m := CallProbe.sbm st.m a v } (q + 1) s' := by
  obtain ⟨s', r, c, o, kp⟩ := hg
  have hL := hM.lay; have hR := S.ram.2
  have hwa := hL.wlo; have hwb := hL.whi; have hcw := hL.cw; have hbh := hL.bhi; have hoc := hL.oc
  have hib := hL.ibh; have hob := hL.obh; have hil := hL.ibl; have hol := hL.obl
  have ha' : (K.lo ≤ a - a % 8 ∧ a - a % 8 + 8 ≤ K.hi) ∨ (K.ob ≤ a ∧ a < K.ob + K.ol) := by
    unfold sok wok outB at hs; omega
  refine ⟨s', r, ⟨c, by rw [o]; simp only [store1]; rw [hM.pc, ofNat_add4]; congr 1, ?_, hM.x0,
    fun j h0 h32 => by rw [o]; exact hM.x j h0 h32, fun r' h1 h2 => by rw [o]; exact hM.keep r' h1 h2, ?_, ?_, ?_,
    hM.lay, perm_keep hM.pm kp⟩⟩
  · intro i h b hb
    rw [o]; simp only [store1]
    rw [toNat_ofNat_lt (by omega), if_neg (by omega)]
    exact hM.code i h b hb
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
    rw [if_neg (fun e => by subst e; unfold sok at hs; exact hs.elim h1 h2)]; exact hM.fr x hx h1 h2

/-- `strb wt, [xb, #f]` to the byte `a = x[b] + f` (`nt`, `nb`: any registers < 31 holding `v`, `bv`) -/
theorem n_strb (S : A64SemN M X W) {q : Nat} (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    {nt nb f a : Nat} {v bv : UInt64} (hA : A[q]? = some (ArmEnc.strb nt nb f)) (hnt : nt < 31)
    (hv : (M.observe s).register nt = v) (hnb : nb < 31) (hbv : (M.observe s).register nb = bv) (hf : f < 4096)
    (ha : a = bv.toNat + f) (hs : sok K a) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 { st with m := CallProbe.sbm st.m a v } (q + 1) s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have hL := hM.lay; have hR := S.ram.2
  have hwa := hL.wlo; have hwb := hL.whi; have hil := hL.ibl; have hih := hL.ibh; have hol := hL.obl; have hoh := hL.obh
  have hs' := hs; unfold sok wok outB at hs'
  have hW : W s a := hM.pm.2 _ (by unfold DataK; omega)
  subst ha
  have := S.strb s nt nb f hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega)) hnt hnb hf
    (by rw [hbv]; omega) (by rw [hbv]; omega) (by rw [hbv]; omega) (by rw [hbv]; exact hW) (nmid_word hM hA hB)
  rw [hbv, hv] at this
  exact nmid_store1 S hM hB hs this

/-- the machine state `s` left the code (`br`): `NMid` without the code-word pc, with the pc `v` -/
structure NOut (X W : M.State → Nat → Prop) (K : LayW) (A : List Nat) (s0 : M.State) (st : CallProbe.St) (v : UInt64)
    (s : M.State) : Prop where
  cfg : M.configured s
  pc : (M.observe s).programCounter = v
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

/-- `br xn` (n ≠ x0): out of the code, to the address `st.x n` -/
theorem n_brOut (S : A64SemN M X W) {q : Nat} (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    {n : Nat} (hA : A[q]? = some (ArmEnc.brR (armReg n))) (hn : mapped n = true) (hn0 : n ≠ 0) :
    ∃ s', Runs M s s' ∧ NOut X W K A s0 st (st.x n) s' := by
  have hq := (List.getElem?_eq_some_iff.1 hA).1
  have := S.br s _ hM.cfg (nmid_pcok hM hB hq) (nmid_fx hM hB (by omega) (by omega)) (armReg_lt hn hn0)
    (nmid_word hM hA hB)
  rw [hM.x n (by omega) (mapped_lt hn)] at this
  obtain ⟨s', r, c, o, kp⟩ := this
  have hmem : (M.observe s').memory = (M.observe s).memory := by rw [o]; rfl
  refine ⟨s', r, ⟨c, by rw [o]; rfl, ?_, hM.x0, fun j h0 h32 => by rw [o]; exact hM.x j h0 h32,
    fun r' h1 h2 => by rw [o]; exact hM.keep r' h1 h2, ?_, ?_, ?_, hM.lay, perm_keep hM.pm kp⟩⟩
  · intro i h b hb; rw [hmem]; exact hM.code i h b hb
  · intro a ha k hk; rw [hmem]; exact hM.w a ha k hk
  · intro a ha; rw [hmem]; exact hM.bw a ha
  · intro a ha h1 h2; rw [hmem]; exact hM.fr a ha h1 h2

/-- the jump/branch steps with the offset as a free `f` (`f = q' - q`) -/
theorem n_b' (S : A64SemN M X W) {q : Nat} (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    {q' : Nat} {f : Int} (hA : A[q]? = some (ArmEnc.bB f)) (hf : f = (q' : Int) - q) (hq' : q' ≤ A.length)
    (hL : A.length < 2 ^ 25) : ∃ s', Runs M s s' ∧ NMid X W K A s0 st q' s' := by
  subst hf; exact n_b S hM hB hA hq' hL

theorem n_bl' (S : A64SemN M X W) {q : Nat} (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    {q' : Nat} {f : Int} (hA : A[q]? = some (ArmEnc.blB f)) (hf : f = (q' : Int) - q) (hq' : q' ≤ A.length)
    (hL : A.length < 2 ^ 25) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (CallProbe.wr st 1 (UInt64.ofNat (K.base + 4 * (q + 1)))) q' s' := by
  subst hf; exact n_bl S hM hB hA hq' hL

theorem n_cbz' (S : A64SemN M X W) {q : Nat} (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    {t q' : Nat} {f : Int} (hA : A[q]? = some (ArmEnc.cbz (armReg t) f)) (hf : f = (q' : Int) - q)
    (ht : mapped t = true) (ht0 : t ≠ 0) (hq' : q' ≤ A.length) (hL : A.length < 2 ^ 18) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st (if st.x t = 0 then q' else q + 1) s' := by
  subst hf; exact n_cbz S hM hB hA ht ht0 hq' hL

theorem n_cbnz' (S : A64SemN M X W) {q : Nat} (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    {t q' : Nat} {f : Int} (hA : A[q]? = some (ArmEnc.cbnz (armReg t) f)) (hf : f = (q' : Int) - q)
    (ht : mapped t = true) (ht0 : t ≠ 0) (hq' : q' ≤ A.length) (hL : A.length < 2 ^ 18) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st (if st.x t = 0 then q + 1 else q') s' := by
  subst hf; exact n_cbnz S hM hB hA ht ht0 hq' hL

theorem n_cmpbr' (S : A64SemN M X W) {q : Nat} (hM : NMid X W K A s0 st q s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    {c n m q' : Nat} {f : Int} (hA : A[q]? = some (ArmEnc.subsR (armReg n) (armReg m)))
    (hA1 : A[q + 1]? = some (ArmEnc.bc c f)) (hf : f = (q' : Int) - (q + 1)) (hc : c < 4) (hn : mapped n = true)
    (hn0 : n ≠ 0) (hm : mapped m = true) (hm0 : m ≠ 0) (hq' : q' ≤ A.length) (hL : A.length < 2 ^ 18) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st (if condV c (st.x n) (st.x m) then q' else q + 2) s' := by
  subst hf; exact n_cmpbr S hM hB hA hA1 hc hn hn0 hm hm0 hq' hL

/-! ## small view lemmas -/

theorem wrS_ne (st : CallProbe.St) {r j : Nat} (v : UInt64) (h : j ≠ r) : (CallProbe.wr st r v).x j = st.x j := by
  unfold CallProbe.wr; split <;> simp [CallProbe.upd, h]

theorem wrS_same (st : CallProbe.St) {r : Nat} (v : UInt64) (h : r ≠ 0) : (CallProbe.wr st r v).x r = v := by
  simp [CallProbe.wr, CallProbe.upd, h]

/-! ## exits: `movn x0,#c; movz x1,#0; br x30` and the return tail `ldr x30,[x2]; ldr x8,[x2,#8]; br x30` -/

/-- the view after the return tail's two loads -/
def retView (st : CallProbe.St) : CallProbe.St :=
  let st1 := CallProbe.wr st 1 (st.m (st.x 12).toNat)
  CallProbe.wr st1 8 (st1.m ((st.x 12).toNat + 8))

/-- **return tail** (stubs words 3-5 / 8-10, start code words 31-33) -/
theorem n_retTail (S : A64SemN M X W) {h : Nat} (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (a0 : A[h]? = some (ArmEnc.ldr (armReg 1) (armReg 12) 0))
    (a1 : A[h + 1]? = some (ArmEnc.ldr (armReg 8) (armReg 12) 8))
    (a2 : A[h + 2]? = some (ArmEnc.brR (armReg 1)))
    (hw : wok K (st.x 12).toNat) (hw8 : wok K ((st.x 12).toNat + 8)) :
    ∃ s', Runs M s s' ∧ NOut X W K A s0 (retView st) ((retView st).x 1) s' := by
  obtain ⟨s1, r1, N1⟩ := n_ldr (a := (st.x 12).toNat) S hM hB a0 (by decide) (by decide) (by decide)
    (hM.x 12 (by omega) (by omega)) (by decide) (by decide) rfl hw
  obtain ⟨s2, r2, N2⟩ := n_ldr (a := (st.x 12).toNat + 8) S N1 hB a1 (by decide) (by decide) (by decide)
    (N1.x 12 (by omega) (by omega)) (by decide) (by decide)
    (by rw [wrS_ne st _ (by decide : (12 : Nat) ≠ 1)]) hw8
  obtain ⟨s3, r3, N3⟩ := n_brOut S N2 hB a2 (by decide) (by decide)
  exact ⟨s3, Runs.trans (Runs.trans r1 r2) r3, N3⟩

/-- `movn x0, #c; movz x1, #0; br x30` (start code words 6-8 with c = 0) -/
theorem n_exitC (S : A64SemN M X W) {h c : Nat} (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hc : c < 2 ^ 16)
    (a0 : A[h]? = some (ArmEnc.movn (armReg 10) c 0)) (a1 : A[h + 1]? = some (ArmEnc.movz (armReg 11) 0))
    (a2 : A[h + 2]? = some (ArmEnc.brR (armReg 1))) :
    let st2 := CallProbe.wr (CallProbe.wr st 10 (movnV c 0)) 11 (UInt64.ofNat 0)
    ∃ s', Runs M s s' ∧ NOut X W K A s0 st2 (st2.x 1) s' := by
  intro st2
  obtain ⟨s1, r1, N1⟩ := n_movn S hM hB a0 (by decide) (by decide) hc (by decide)
  obtain ⟨s2, r2, N2⟩ := n_movz S N1 hB a1 (by decide) (by decide) (by decide)
  obtain ⟨s3, r3, N3⟩ := n_brOut S N2 hB a2 (by decide) (by decide)
  exact ⟨s3, Runs.trans (Runs.trans r1 r2) r3, N3⟩

/-- **stubs 1-5 (c = 0) and 6-10 (c = 1)**: `movn x0,#c; movz x1,#0; ldr x30,[x2]; ldr x8,[x2,#8]; br x30`
(word 0, `b <start>`, is `n_b'`) -/
theorem n_stubE (S : A64SemN M X W) {h c : Nat} (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hc : c < 2 ^ 16)
    (a0 : A[h]? = some (ArmEnc.movn (armReg 10) c 0)) (a1 : A[h + 1]? = some (ArmEnc.movz (armReg 11) 0))
    (a2 : A[h + 2]? = some (ArmEnc.ldr (armReg 1) (armReg 12) 0))
    (a3 : A[h + 3]? = some (ArmEnc.ldr (armReg 8) (armReg 12) 8))
    (a4 : A[h + 4]? = some (ArmEnc.brR (armReg 1)))
    (hw : wok K (st.x 12).toNat) (hw8 : wok K ((st.x 12).toNat + 8)) :
    let st2 := CallProbe.wr (CallProbe.wr st 10 (movnV c 0)) 11 (UInt64.ofNat 0)
    ∃ s', Runs M s s' ∧ NOut X W K A s0 (retView st2) ((retView st2).x 1) s' := by
  intro st2
  obtain ⟨s1, r1, N1⟩ := n_movn S hM hB a0 (by decide) (by decide) hc (by decide)
  obtain ⟨s2, r2, N2⟩ := n_movz S N1 hB a1 (by decide) (by decide) (by decide)
  have e12 : (CallProbe.wr (CallProbe.wr st 10 (movnV c 0)) 11 (UInt64.ofNat 0)).x 12 = st.x 12 := by
    rw [wrS_ne _ _ (by decide : (12 : Nat) ≠ 11), wrS_ne _ _ (by decide : (12 : Nat) ≠ 10)]
  obtain ⟨s3, r3, N3⟩ := n_retTail S N2 hB a2 a3 a4 (by rw [e12]; exact hw) (by rw [e12]; exact hw8)
  exact ⟨s3, Runs.trans (Runs.trans r1 r2) r3, N3⟩

/-! ## start code (34 words from `h`) -/

/-- words 0-5: `add x10,x2,#16; movz x16,#3; lsrv x11,x4,x16; lslv x11,x11,x16; subs x16,x11,x10; b.hs → h+9`
(J: `addi 30 12 16; srli 31 2 3; slli 31 31 3; bgeu 31 30`) -/
theorem n_startHead (S : A64SemN M X W) {h : Nat} (hM : NMid X W K A s0 st h s) (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (hL : A.length < 2 ^ 18) (hq : h + 9 ≤ A.length)
    (a0 : A[h]? = some (ArmEnc.addi (armReg 30) (armReg 12) 16))
    (a1 : A[h + 1]? = some (ArmEnc.movz 16 3))
    (a2 : A[h + 2]? = some (ArmEnc.rr (ArmEnc.aluC 7) (armReg 31) (armReg 2) 16))
    (a3 : A[h + 3]? = some (ArmEnc.rr (ArmEnc.aluC 6) (armReg 31) (armReg 31) 16))
    (a4 : A[h + 4]? = some (ArmEnc.subsR (armReg 31) (armReg 30)))
    (a5 : A[h + 5]? = some (ArmEnc.bc 2 4)) :
    let st1 := CallProbe.wr st 30 (st.x 12 + UInt64.ofNat 16)
    let st2 := CallProbe.wr st1 31 (CallProbe.aluf 7 (st1.x 2) (UInt64.ofNat 3))
    let st3 := CallProbe.wr st2 31 (CallProbe.aluf 6 (st2.x 31) (UInt64.ofNat 3))
    ∃ s', Runs M s s' ∧
      NMid X W K A s0 st3 (if condV 2 (st3.x 31) (st3.x 30) then h + 9 else h + 6) s' := by
  intro st1 st2 st3
  obtain ⟨s1, r1, N1⟩ := n_addi S hM hB a0 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s2, r2, N2, x2⟩ := n_movzS S N1 hB a1 (Or.inl rfl) (by decide)
  obtain ⟨s3, r3, N3, x3⟩ := n_alu16 S N2 hB a2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) x2
  obtain ⟨s4, r4, N4, x4⟩ := n_alu16 S N3 hB a3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) x3
  obtain ⟨s5, r5, N5⟩ := n_cmpbr' S N4 hB a4 a5 (q' := h + 9) (by push_cast; omega) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) hL
  exact ⟨s5, Runs.trans (Runs.trans (Runs.trans (Runs.trans r1 r2) r3) r4) r5, N5⟩

/-- words 9-13: `str x30,[x2]; str x8,[x2,#8]; add x12,x0,#0; add x13,x1,#0; bl main` (main at word `w`);
J: `sd 1 12 0; sd 8 12 8; addi 28 10 0; addi 29 11 0; jal 1 …` -/
theorem n_startMid (S : A64SemN M X W) {h w : Nat} (hM : NMid X W K A s0 st (h + 9) s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32) (hL : A.length < 2 ^ 18) (hw0 : w ≤ A.length)
    (a0 : A[h + 9]? = some (ArmEnc.str (armReg 1) (armReg 12) 0))
    (a1 : A[h + 10]? = some (ArmEnc.str (armReg 8) (armReg 12) 8))
    (a2 : A[h + 11]? = some (ArmEnc.addi (armReg 28) (armReg 10) 0))
    (a3 : A[h + 12]? = some (ArmEnc.addi (armReg 29) (armReg 11) 0))
    (a4 : A[h + 13]? = some (ArmEnc.blB ((w : Int) - ((h + 13 : Nat) : Int))))
    (hw : wok K (st.x 12).toNat) (hw8 : wok K ((st.x 12).toNat + 8)) :
    let st1 : CallProbe.St := { st with m := CallProbe.upd st.m (st.x 12).toNat (st.x 1) }
    let st2 : CallProbe.St := { st1 with m := CallProbe.upd st1.m ((st.x 12).toNat + 8) (st.x 8) }
    let st3 := CallProbe.wr st2 28 (st2.x 10 + UInt64.ofNat 0)
    let st4 := CallProbe.wr st3 29 (st3.x 11 + UInt64.ofNat 0)
    ∃ s', Runs M s s' ∧
      NMid X W K A s0 (CallProbe.wr st4 1 (UInt64.ofNat (K.base + 4 * (h + 13 + 1)))) w s' := by
  intro st1 st2 st3 st4
  obtain ⟨s1, r1, N1⟩ := n_str (a := (st.x 12).toNat) S hM hB a0 (by decide) (hM.x 1 (by omega) (by omega)) (by decide)
    (hM.x 12 (by omega) (by omega)) (by decide) (by decide) rfl hw
  obtain ⟨s2, r2, N2⟩ := n_str (a := (st.x 12).toNat + 8) S N1 hB a1 (by decide) (N1.x 8 (by omega) (by omega))
    (by decide) (N1.x 12 (by omega) (by omega)) (by decide) (by decide) rfl hw8
  obtain ⟨s3, r3, N3⟩ := n_addi S N2 hB a2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s4, r4, N4⟩ := n_addi S N3 hB a3 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s5, r5, N5⟩ := n_bl' S N4 hB a4 (q' := w) (by push_cast; omega) hw0 (by omega)
  exact ⟨s5, Runs.trans (Runs.trans (Runs.trans (Runs.trans r1 r2) r3) r4) r5, N5⟩

/-- words 14-16 (after `main` returned): `ldr x5,[x11]; ldr x7,[x5]; cbnz x7 → h+20` -/
theorem n_startRes (S : A64SemN M X W) {h : Nat} (hM : NMid X W K A s0 st (h + 14) s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32) (hL : A.length < 2 ^ 18) (hq : h + 20 ≤ A.length)
    (a0 : A[h + 14]? = some (ArmEnc.ldr (armReg 5) (armReg 31) 0))
    (a1 : A[h + 15]? = some (ArmEnc.ldr (armReg 7) (armReg 5) 0))
    (a2 : A[h + 16]? = some (ArmEnc.cbnz (armReg 7) 4))
    (hw : wok K (st.x 31).toNat) (hw1 : wok K (st.m (st.x 31).toNat).toNat) :
    let st1 := CallProbe.wr st 5 (st.m (st.x 31).toNat)
    let st2 := CallProbe.wr st1 7 (st1.m (st1.x 5).toNat)
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st2 (if st2.x 7 = 0 then h + 17 else h + 20) s' := by
  intro st1 st2
  obtain ⟨s1, r1, N1⟩ := n_ldr (a := (st.x 31).toNat) S hM hB a0 (by decide) (by decide) (by decide)
    (hM.x 31 (by omega) (by omega)) (by decide) (by decide) rfl hw
  obtain ⟨s2, r2, N2⟩ := n_ldr (a := (st1.x 5).toNat) S N1 hB a1 (by decide) (by decide) (by decide)
    (N1.x 5 (by omega) (by omega)) (by decide) (by decide) rfl
    (by rw [show st1.x 5 = st.m (st.x 31).toNat from wrS_same st _ (by decide)]; exact hw1)
  obtain ⟨s3, r3, N3⟩ := n_cbnz' S N2 hB a2 (q' := h + 20) (by push_cast; omega) (by decide) (by decide)
    (by omega) hL
  exact ⟨s3, Runs.trans (Runs.trans r1 r2) r3, N3⟩

/-- words 17-19 (empty result): `movz x0,#1; movz x1,#0; b → h+31` -/
theorem n_startEmpty (S : A64SemN M X W) {h : Nat} (hM : NMid X W K A s0 st (h + 17) s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32) (hL : A.length < 2 ^ 18) (hq : h + 31 ≤ A.length)
    (a0 : A[h + 17]? = some (ArmEnc.movz (armReg 10) 1)) (a1 : A[h + 18]? = some (ArmEnc.movz (armReg 11) 0))
    (a2 : A[h + 19]? = some (ArmEnc.bB 12)) :
    ∃ s', Runs M s s' ∧
      NMid X W K A s0 (CallProbe.wr (CallProbe.wr st 10 (UInt64.ofNat 1)) 11 (UInt64.ofNat 0)) (h + 31) s' := by
  obtain ⟨s1, r1, N1⟩ := n_movz S hM hB a0 (by decide) (by decide) (by decide)
  obtain ⟨s2, r2, N2⟩ := n_movz S N1 hB a1 (by decide) (by decide) (by decide)
  obtain ⟨s3, r3, N3⟩ := n_b' S N2 hB a2 (q' := h + 31) (by push_cast; omega) hq (by omega)
  exact ⟨s3, Runs.trans (Runs.trans r1 r2) r3, N3⟩

/-- words 20-22: `add x1,x7,#0; add x6,x5,#16; add x14,x3,#0` -/
theorem n_startInit (S : A64SemN M X W) {h : Nat} (hM : NMid X W K A s0 st (h + 20) s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (a0 : A[h + 20]? = some (ArmEnc.addi (armReg 11) (armReg 7) 0))
    (a1 : A[h + 21]? = some (ArmEnc.addi (armReg 6) (armReg 5) 16))
    (a2 : A[h + 22]? = some (ArmEnc.addi (armReg 14) (armReg 13) 0)) :
    let st1 := CallProbe.wr st 11 (st.x 7 + UInt64.ofNat 0)
    let st2 := CallProbe.wr st1 6 (st1.x 5 + UInt64.ofNat 16)
    let st3 := CallProbe.wr st2 14 (st2.x 13 + UInt64.ofNat 0)
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st3 (h + 23) s' := by
  intro st1 st2 st3
  obtain ⟨s1, r1, N1⟩ := n_addi S hM hB a0 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s2, r2, N2⟩ := n_addi S N1 hB a1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s3, r3, N3⟩ := n_addi S N2 hB a2 (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨s3, Runs.trans (Runs.trans r1 r2) r3, N3⟩

/-- one copy iteration (J `ld 15 6 0; sb 15 14 0; addi 6 6 8; addi 14 14 1; addi 7 7 (-1)`) -/
def copyStep (st : CallProbe.St) : CallProbe.St :=
  let s1 := CallProbe.wr st 15 (st.m (st.x 6).toNat)
  let s2 : CallProbe.St := { s1 with m := CallProbe.sbm s1.m (st.x 14).toNat (s1.x 15) }
  let s3 := CallProbe.wr s2 6 (s2.x 6 + UInt64.ofNat 8)
  let s4 := CallProbe.wr s3 14 (s3.x 14 + UInt64.ofNat 1)
  CallProbe.wr s4 7 (s4.x 7 - UInt64.ofNat 1)

/-- loop exit: `cbz x7 → h+30` with x7 = 0 -/
theorem n_copyExit (S : A64SemN M X W) {h : Nat} (hM : NMid X W K A s0 st (h + 23) s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32) (hL : A.length < 2 ^ 18) (hq : h + 30 ≤ A.length)
    (a0 : A[h + 23]? = some (ArmEnc.cbz (armReg 7) 7)) (h7 : st.x 7 = 0) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 st (h + 30) s' := by
  obtain ⟨s1, r1, N1⟩ := n_cbz' S hM hB a0 (q' := h + 30) (by push_cast; omega) (by decide) (by decide) hq hL
  rw [if_pos h7] at N1
  exact ⟨s1, r1, N1⟩

/-- one loop iteration, `x7 ≠ 0`: words 23-29 -/
theorem n_copyStep (S : A64SemN M X W) {h : Nat} (hM : NMid X W K A s0 st (h + 23) s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32) (hL : A.length < 2 ^ 18) (hq : h + 30 ≤ A.length)
    (a0 : A[h + 23]? = some (ArmEnc.cbz (armReg 7) 7))
    (a1 : A[h + 24]? = some (ArmEnc.ldr (armReg 15) (armReg 6) 0))
    (a2 : A[h + 25]? = some (ArmEnc.strb (armReg 15) (armReg 14) 0))
    (a3 : A[h + 26]? = some (ArmEnc.addi (armReg 6) (armReg 6) 8))
    (a4 : A[h + 27]? = some (ArmEnc.addi (armReg 14) (armReg 14) 1))
    (a5 : A[h + 28]? = some (ArmEnc.subi (armReg 7) (armReg 7) 1))
    (a6 : A[h + 29]? = some (ArmEnc.bB (-6)))
    (h7 : st.x 7 ≠ 0) (hw : wok K (st.x 6).toNat) (hs : sok K (st.x 14).toNat) :
    ∃ s', Runs M s s' ∧ NMid X W K A s0 (copyStep st) (h + 23) s' := by
  obtain ⟨s0', r0, N0⟩ := n_cbz' S hM hB a0 (q' := h + 30) (by push_cast; omega) (by decide) (by decide) hq hL
  rw [if_neg h7] at N0
  obtain ⟨s1, r1, N1⟩ := n_ldr (a := (st.x 6).toNat) S N0 hB a1 (by decide) (by decide) (by decide)
    (N0.x 6 (by omega) (by omega)) (by decide) (by decide) rfl hw
  obtain ⟨s2, r2, N2⟩ := n_strb (a := (st.x 14).toNat) S N1 hB a2 (by decide) (N1.x 15 (by omega) (by omega))
    (by decide) (N1.x 14 (by omega) (by omega)) (by decide)
    (by rw [wrS_ne st _ (by decide : (14 : Nat) ≠ 15)]; rfl) hs
  obtain ⟨s3, r3, N3⟩ := n_addi S N2 hB a3 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s4, r4, N4⟩ := n_addi S N3 hB a4 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s5, r5, N5⟩ := n_subi S N4 hB a5 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s6, r6, N6⟩ := n_b' S N5 hB a6 (q' := h + 23) (by push_cast; omega) (by omega) (by omega)
  exact ⟨s6, Runs.trans (Runs.trans (Runs.trans (Runs.trans (Runs.trans (Runs.trans r0 r1) r2) r3) r4) r5) r6, N6⟩

/-- `n` iterations -/
def copyIter : Nat → CallProbe.St → CallProbe.St
  | 0, st => st
  | n + 1, st => copyIter n (copyStep st)

theorem copyStep_x7 (st : CallProbe.St) : (copyStep st).x 7 = st.x 7 - UInt64.ofNat 1 := by
  simp [copyStep, CallProbe.wr, CallProbe.upd]

/-- **the copy loop**: `n` iterations (`n` = x7), to word h+30; side conditions along the iterates -/
theorem n_copyLoop (S : A64SemN M X W) {h : Nat} (hB : K.base + 4 * A.length ≤ 2 ^ 32) (hL : A.length < 2 ^ 18)
    (hq : h + 30 ≤ A.length)
    (a0 : A[h + 23]? = some (ArmEnc.cbz (armReg 7) 7))
    (a1 : A[h + 24]? = some (ArmEnc.ldr (armReg 15) (armReg 6) 0))
    (a2 : A[h + 25]? = some (ArmEnc.strb (armReg 15) (armReg 14) 0))
    (a3 : A[h + 26]? = some (ArmEnc.addi (armReg 6) (armReg 6) 8))
    (a4 : A[h + 27]? = some (ArmEnc.addi (armReg 14) (armReg 14) 1))
    (a5 : A[h + 28]? = some (ArmEnc.subi (armReg 7) (armReg 7) 1))
    (a6 : A[h + 29]? = some (ArmEnc.bB (-6))) :
    ∀ (n : Nat) (st : CallProbe.St) (s : M.State), NMid X W K A s0 st (h + 23) s → (st.x 7).toNat = n →
      (∀ i < n, wok K ((copyIter i st).x 6).toNat) → (∀ i < n, sok K ((copyIter i st).x 14).toNat) →
      ∃ s', Runs M s s' ∧ NMid X W K A s0 (copyIter n st) (h + 30) s' := by
  intro n
  induction n with
  | zero =>
    intro st s hM hn _ _
    exact n_copyExit S hM hB hL hq a0 (by apply UInt64.toNat_inj.1; simpa using hn)
  | succ n ih =>
    intro st s hM hn hw hs
    have h7 : st.x 7 ≠ 0 := by intro e; rw [e] at hn; simp at hn
    obtain ⟨s1, r1, N1⟩ := n_copyStep S hM hB hL hq a0 a1 a2 a3 a4 a5 a6 h7 (hw 0 (by omega)) (hs 0 (by omega))
    have hn1 : ((copyStep st).x 7).toNat = n := by
      have e1 : (UInt64.ofNat 1).toNat = 1 := by decide
      rw [copyStep_x7, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
      omega
    obtain ⟨s2, r2, N2⟩ := ih (copyStep st) s1 N1 hn1 (fun i hi => hw (i + 1) (by omega)) (fun i hi => hs (i + 1) (by omega))
    refine ⟨s2, Runs.trans r1 r2, ?_⟩
    exact N2

/-- words 30-33: `movz x0,#0; ldr x30,[x2]; ldr x8,[x2,#8]; br x30` (J `addi 10 0 0; ld 1 12 0; ld 8 12 8; jalr 0 1`) -/
theorem n_startRet (S : A64SemN M X W) {h : Nat} (hM : NMid X W K A s0 st (h + 30) s)
    (hB : K.base + 4 * A.length ≤ 2 ^ 32)
    (a0 : A[h + 30]? = some (ArmEnc.movz (armReg 10) 0))
    (a1 : A[h + 31]? = some (ArmEnc.ldr (armReg 1) (armReg 12) 0))
    (a2 : A[h + 32]? = some (ArmEnc.ldr (armReg 8) (armReg 12) 8))
    (a3 : A[h + 33]? = some (ArmEnc.brR (armReg 1)))
    (hw : wok K (st.x 12).toNat) (hw8 : wok K ((st.x 12).toNat + 8)) :
    let st1 := CallProbe.wr st 10 (UInt64.ofNat 0)
    ∃ s', Runs M s s' ∧ NOut X W K A s0 (retView st1) ((retView st1).x 1) s' := by
  intro st1
  obtain ⟨s1, r1, N1⟩ := n_movz S hM hB a0 (by decide) (by decide) (by decide)
  have e12 : (CallProbe.wr st 10 (UInt64.ofNat 0)).x 12 = st.x 12 := wrS_ne st _ (by decide)
  obtain ⟨s2, r2, N2⟩ := n_retTail S N1 hB a1 a2 a3 (by rw [e12]; exact hw) (by rw [e12]; exact hw8)
  exact ⟨s2, Runs.trans r1 r2, N2⟩

end JT
