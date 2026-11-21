/- T12 (round 2): the atoms `align8` (`srli d n 3; slli d d 3` ↔ `movz x16,#3; lsrv; lslv`) and `sb` (`sb s n 0` ↔ `strb`).
Section "for ArmNat": `nmid_set'`, `n_movzS`, `n_alu16`, `nmid_store1`, `n_strb` (to be moved into ArmNat). -/
import Nano.Run.NatA.Base
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


theorem wrS_ne (st : CallProbe.St) {r j : Nat} (v : UInt64) (h : j ≠ r) : (CallProbe.wr st r v).x j = st.x j := by
  unfold CallProbe.wr; split <;> simp [CallProbe.upd, h]

theorem wrS_same (st : CallProbe.St) {r : Nat} (v : UInt64) (h : r ≠ 0) : (CallProbe.wr st r v).x r = v := by
  simp [CallProbe.wr, CallProbe.upd, h]

theorem agree_wr2 {D : Nat → Prop} {v st : CallProbe.St} (h : Agree D v st) (d : Nat) (a b : UInt64) (hab : a = b) :
    Agree (fun r => D r ∧ r ≠ d) (CallProbe.wr v d a) (CallProbe.wr st d b) := by
  subst hab; exact agree_wr h d a

/-! ## the atoms -/

theorem asim_align8 (S : A64SemN M X W) {d x : Nat} (hok : (NTm.align8 d x).ok = true) :
    ASim M X W (NTm.align8 d x) := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, Bool.and_eq_true, mr_iff] at hok
  obtain ⟨⟨hd, hd0⟩, hx, hx0⟩ := hok
  have c0 : C[q]? = some (.srli d x 3) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  have c1 : C[q + 1]? = some (.slli d d 3) := by simpa [NTm.j] using hJ 1 (by simp [NTm.j])
  have vx : v.x x = st.x x := hag.x x (by omega) (mapped_lt hx) (fun hD => by simpa [NTm.reads] using hrd x hD)
  have a0 : A[h]? = some (ArmEnc.movz 16 3) := by simpa [NTm.a] using hA 0 (by simp [NTm.alen, NTm.a])
  have a1 : A[h + 1]? = some (ArmEnc.rr (ArmEnc.aluC 7) (armReg d) (armReg x) 16) := by
    simpa [NTm.a, ArmEnc.aluC] using hA 1 (by simp [NTm.alen, NTm.a])
  have a2 : A[h + 2]? = some (ArmEnc.rr (ArmEnc.aluC 6) (armReg d) (armReg d) 16) := by
    simpa [NTm.a, ArmEnc.aluC] using hA 2 (by simp [NTm.alen, NTm.a])
  cases hrun with
  | head hS hs hrest =>
  simp only [SafeX, c0] at hS
  simp only [CallProbe.step, c0, Option.some.injEq] at hs; subst hs
  cases hrest with
  | refl => exact absurd rfl (hz 1 (by decide) (by simp [NTm.j]))
  | head hS2 hs2 hrest2 =>
  simp only [SafeX, c1] at hS2
  simp only [CallProbe.step, c1, Option.some.injEq] at hs2; subst hs2
  obtain ⟨s1, r1, N1, x1⟩ := n_movzS S hM hB a0 (Or.inl rfl) (by decide)
  obtain ⟨s2, r2, N2, x2⟩ := n_alu16 S N1 hB a1 (by decide) (by decide) (by decide) hd hd0 hx hx0 x1
  obtain ⟨s3, r3, N3, x3⟩ := n_alu16 S N2 hB a2 (by decide) (by decide) (by decide) hd hd0 hd hd0 x2
  have e1 : CallProbe.aluf 7 (v.x x) (UInt64.ofNat 3) = st.x x >>> (3 : Nat).toUInt64 := by
    rw [vx]; simp [CallProbe.aluf]; rfl
  have ag1 := agree_wr2 hag d _ _ e1
  have e2 : CallProbe.aluf 6 ((CallProbe.wr v d (CallProbe.aluf 7 (v.x x) (UInt64.ofNat 3))).x d) (UInt64.ofNat 3) =
      (CallProbe.wr st d (st.x x >>> (3 : Nat).toUInt64)).x d <<< (3 : Nat).toUInt64 := by
    rw [wrS_same _ _ hd0, wrS_same _ _ hd0, e1]; simp [CallProbe.aluf]; rfl
  have ag2 := agree_wr2 ag1 d _ _ e2
  exact ⟨1, _, _, s3, by omega, hrest2, Runs.trans (Runs.trans r1 r2) r3,
    by rw [show π (q + 1 + 1) = _ from hft]; simpa [NTm.alen, NTm.a] using N3,
    ag2.mono (fun r hr => Or.inl ⟨hr.1.1, by simp only [NTm.writes, beq_eq_false_iff_ne]; exact fun e => hr.2 e.symm⟩),
    (CallProbe.wr_b _ _ _).trans (CallProbe.wr_b _ _ _), (CallProbe.wr_w _ _ _).trans (CallProbe.wr_w _ _ _), Or.inl rfl⟩

theorem asim_sb (S : A64SemN M X W) {x y : Nat} (hok : (NTm.sb x y).ok = true) : ASim M X W (NTm.sb x y) := by
  intro K C A s0 s v st z n π q h D hJ hA hB hL hM hag hrd hb hft hlo htg hlk hrun hz
  simp only [NTm.ok, Bool.and_eq_true, mr_iff] at hok
  obtain ⟨⟨hx, hx0⟩, hy, hy0⟩ := hok
  have c0 : C[q]? = some (.sb x y 0) := by simpa [NTm.j] using hJ 0 (by simp [NTm.j])
  cases hrun with
  | head hS hs hrest =>
  simp only [SafeX, c0] at hS
  obtain ⟨-, -, -, -, -, hsok⟩ := hS
  simp only [CallProbe.step, c0, Option.some.injEq] at hs; subst hs
  have vx : v.x x = st.x x := hag.x x (by omega) (mapped_lt hx) (fun hD => by simpa [NTm.reads] using hrd x hD)
  have vy : v.x y = st.x y := hag.x y (by omega) (mapped_lt hy) (fun hD => by simpa [NTm.reads] using hrd y hD)
  have a0 : A[h]? = some (ArmEnc.strb (armReg x) (armReg y) 0) := by
    simpa [NTm.a] using hA 0 (by simp [NTm.alen, NTm.a])
  have hs' : sok K (v.x y).toNat := by rw [vy]; simpa [CallProbe.ea] using hsok
  obtain ⟨s', r, N⟩ := n_strb (a := (v.x y).toNat) S hM hB a0 (armReg_lt hx hx0) (hM.x x (by omega) (mapped_lt hx))
    (armReg_lt hy hy0) (hM.x y (by omega) (mapped_lt hy)) (by decide) rfl hs'
  exact ⟨0, _, _, s', Nat.zero_le _, hrest, r,
    by rw [show π (q + 1) = _ from hft]; simpa [NTm.alen, NTm.a] using N,
    ⟨fun j h0 h32 hd => hag.x j h0 h32 (fun hD => hd (Or.inl ⟨hD, by simp [NTm.writes]⟩)),
     by show CallProbe.sbm v.m _ _ = CallProbe.sbm st.m _ _; rw [hag.m, vx, vy]; simp [CallProbe.ea], hag.x0⟩,
    rfl, rfl, Or.inl rfl⟩

end JT
