/- Safe retrofit, part 1 (Opus box A): the leaf template runs as SAFE runs (`SimW.SStar`), so the Sail lift
`SimW.sim_starW` applies.  Spec: for each leaf run lemma `X_run` (Expr / Heap / Call / CallA / Templates) a twin
`X_srun` with the same hypotheses plus exactly the `SimW.Safe` side conditions of the instructions it executes:
  * addi: the sum does not wrap (follows from the run lemma's own bounds where it can);
  * ld / sd: the effective address is a work cell (`wok K a`: lo ≤ a, a + 8 ≤ hi, 8-aligned);
  * lbu: the aligned cell containing the byte is a work cell (input bytes live in the work region);
  * jal: the target is inside the code (< |C|);  jalr: the target is base + 4j;
  * registers < 32, branch offsets 2, ALU op 1..8 with rd ≠ 0 (structural, discharged here).
Tool: `sstar_of_run` — a deterministic run whose every intermediate state is `Safe` is an `SStar`. -/
import Nano.V2Self.Proof.SimW
import Nano.V2Self.Proof.Expr
import Nano.V2Self.Proof.Templates
import Nano.V2Self.Proof.CallA
namespace SafeRun
open CallProbe SimW

theorem _root_.SimW.SStar.trans {K : LayW} {C : List J} {a b c : Nat × St} (h1 : SStar K C a b) (h2 : SStar K C b c) : SStar K C a c := by
  induction h1 with
  | refl => exact h2
  | head hs st _ ih => exact .head hs st (ih h2)

theorem _root_.SimW.SStar.one {K : LayW} {C : List J} {a b : Nat × St} (hs : Safe K C a) (st : step C a = some b) : SStar K C a b :=
  .head hs st (.refl b)

/-- a deterministic run whose every intermediate state is safe -/
theorem sstar_of_run {K : LayW} {C : List J} : ∀ {k : Nat} {a b : Nat × St}, run C k a = some b →
    (∀ j, j < k → ∀ c, run C j a = some c → Safe K C c) → SStar K C a b
  | 0, a, b, h, _ => by simp [run] at h; subst h; exact .refl _
  | k + 1, a, b, h, hs => by
    simp only [run] at h
    cases e : step C a with
    | none => simp [e] at h
    | some c =>
      simp [e] at h
      refine .head (hs 0 (by omega) a rfl) e (sstar_of_run h fun j hj d hd => hs (j + 1) (by omega) d ?_)
      simp [run, e, hd]

theorem _root_.SimW.SStar.star {K : LayW} {C : List J} {a b : Nat × St} (h : SStar K C a b) : Star C a b := by
  induction h with
  | refl => exact .refl _
  | head _ st _ ih => exact (Star.one st).trans ih

/-! ## push -/

theorem push_srun {K : LayW} {C pc s r oom} (hC : At C pc (push r oom)) (hr : r ≠ 31) (hr0 : r ≠ 0) (hr32 : r < 32)
    (hh : (s.x 30).toNat + 8 ≤ (s.x 31).toNat) (hw : wok K ((s.x 31).toNat - 8)) :
    SStar K C (pc, s) (pc + 4, ⟨upd s.x 31 (UInt64.ofNat ((s.x 31).toNat - 8)),
                                 upd s.m ((s.x 31).toNat - 8) (s.x r), s.b⟩) := by
  refine sstar_of_run (push_run hC hr hr0 hh) fun j hj c hc => ?_
  have h0 := hC.at 0 (by simp [push]); have h1 := hC.at 1 (by simp [push])
  have h3 := hC.at 3 (by simp [push])
  simp only [push, Nat.add_zero] at h0 h1 h3
  simp at h0 h1 h3
  have lt : (s.x 31).toNat < 2 ^ 64 := (s.x 31).toNat_lt
  have e : ea (s.x 31) (-8) = (s.x 31).toNat - 8 := by simp [ea]; omega
  have t6' : (UInt64.ofNat ((s.x 31).toNat - 8)).toNat = (s.x 31).toNat - 8 := by simp [UInt64.toNat_ofNat]; omega
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · simp [run] at hc; subst hc; simp [Safe, h0]; omega
  · simp [run, step, h0] at hc; subst hc; simp [Safe, h1]
  · have c2 : (s.x 30).toNat ≤ (s.x 31).toNat - 8 := by omega
    simp [run, step, h0, h1, wr, e, upd_same, upd_other _ _ (show (30:Nat) ≠ 31 by decide), t6', c2,
      show ((pc : Int) + 1 + 2).toNat = pc + 3 by omega] at hc
    subst hc
    simp [Safe, h3, hr32, ea, upd_same, t6']; exact hw

theorem len_srun {K : LayW} {C pc tgt} (s : St) (hC : At C pc (lenT tgt pc)) (hh : (s.x 30).toNat + 8 ≤ (s.x 31).toNat)
    (hw : wok K ((s.x 31).toNat - 8)) :
    SStar K C (pc, s) (pc + 4, ⟨upd s.x 31 (UInt64.ofNat ((s.x 31).toNat - 8)), upd s.m ((s.x 31).toNat - 8) (s.x 29), s.b⟩) :=
  push_srun (by simpa [lenT, pushA] using hC) (by decide) (by decide) (by decide) hh hw

/-! ## BIN -/

theorem bin_srun {K : LayW} {C pc op} (s : St) (hC : At C pc (binT op)) (hlt : (s.x 31).toNat + 16 < 2 ^ 63)
    (hop : 1 ≤ op ∧ op ≤ 8) (w0 : wok K (s.x 31).toNat) (w8 : wok K ((s.x 31).toNat + 8)) :
    SStar K C (pc, s) (pc + 5,
      ⟨upd (upd (upd (upd s.x 6 (s.m (s.x 31).toNat)) 5 (s.m ((s.x 31).toNat + 8))) 31 (UInt64.ofNat ((s.x 31).toNat + 8))) 5
          (aluf op (s.m ((s.x 31).toNat + 8)) (s.m (s.x 31).toNat)),
       upd s.m ((s.x 31).toNat + 8) (aluf op (s.m ((s.x 31).toNat + 8)) (s.m (s.x 31).toNat)), s.b⟩) := by
  refine sstar_of_run (bin_run s hC hlt) fun j hj c hc => ?_
  have h0 := hC.at 0 (by simp [binT]); have h1 := hC.at 1 (by simp [binT]); have h2 := hC.at 2 (by simp [binT])
  have h3 := hC.at 3 (by simp [binT]); have h4 := hC.at 4 (by simp [binT])
  simp [binT] at h0 h1 h2 h3 h4
  have e0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have e8 : ea (s.x 31) 8 = (s.x 31).toNat + 8 := by simp [ea]; omega
  have t8' : (s.x 31 + 8).toNat = (s.x 31).toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have e8'' : ea (s.x 31 + 8) 0 = (s.x 31).toNat + 8 := by simp only [ea, t8']; omega
  have t8 : (UInt64.ofNat ((s.x 31).toNat + 8)).toNat = (s.x 31).toNat + 8 := by simp only [UInt64.toNat_ofNat']; omega
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl
  · simp [run] at hc; subst hc; simp [Safe, h0, e0]; exact w0
  · simp [run, step, h0, wr, upd_other _ _ (show (31:Nat) ≠ 6 by decide)] at hc; subst hc
    simp [Safe, h1, upd_other _ _ (show (31:Nat) ≠ 6 by decide), e8]; exact ⟨by omega, w8⟩
  · simp [run, step, h0, h1, wr, upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide)] at hc
    subst hc
    simp [Safe, h2, upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide)]; omega
  · simp [run, step, h0, h1, h2, wr] at hc; subst hc; simp [Safe, h3]; omega
  · simp [run, step, h0, h1, h2, h3, wr, e0, e8, upd_same, upd_other _ _ (show (31:Nat) ≠ 6 by decide),
      upd_other _ _ (show (31:Nat) ≠ 5 by decide)] at hc
    subst hc
    simp [Safe, h4, upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_same, ea, t8]
    refine ⟨by omega, ?_⟩
    have : ((((s.x 31).toNat : Int) + 8) % 18446744073709551616).toNat = (s.x 31).toNat + 8 := by omega
    rw [this]; exact w8

/-! ## BSIZE -/

theorem bsize_srun {K : LayW} {C pc} (s : St) (hC : At C pc bsizeT) (w0 : wok K (s.x 31).toNat)
    (w1 : wok K (s.m (s.x 31).toNat).toNat) :
    SStar K C (pc, s) (pc + 3, ⟨upd s.x 5 (s.m (s.m (s.x 31).toNat).toNat), upd s.m (s.x 31).toNat (s.m (s.m (s.x 31).toNat).toNat), s.b⟩) := by
  refine sstar_of_run (bsize_run s hC) fun j hj c hc => ?_
  have h0 := hC.at 0 (by simp [bsizeT]); have h1 := hC.at 1 (by simp [bsizeT]); have h2 := hC.at 2 (by simp [bsizeT])
  simp [bsizeT] at h0 h1 h2
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · simp [run] at hc; subst hc; simp [Safe, h0, ea]; exact w0
  · simp [run, step, h0, wr] at hc; subst hc; simp [Safe, h1, ea, upd_same]; exact w1
  · simp [run, step, h0, h1, wr, upd_same] at hc; subst hc
    simp [Safe, h2, ea, upd_other _ _ (show (31:Nat) ≠ 5 by decide)]; exact w0

/-! ## li -/

theorem li_srun {K : LayW} {C pc d} {v : UInt64} (s : St) (hd : d ≠ 0) (hd32 : d < 32) (hx0 : s.x 0 = 0)
    (hC : At C pc (liT d v)) :
    ∃ s', SStar K C (pc, s) (pc + (liT d v).length, s') ∧ s'.x = upd s.x d v ∧ s'.m = s.m ∧ s'.b = s.b := by
  obtain ⟨s', hr, hx, hm, hb⟩ := li_run s hd hx0 hC
  refine ⟨s', sstar_of_run hr fun i hi c hc => ?_, hx, hm, hb⟩
  by_cases hv : v.toNat < 2048
  · have h0 := hC.at 0 (by simp [liT_len_small d v hv])
    simp [liT, hv] at h0
    rw [liT_len_small d v hv] at hi
    have : i = 0 := by omega
    subst this; simp [run] at hc; subst hc; simp [Safe, h0, hd32, hx0]; omega
  rw [liT_len_big d v hv] at hi
  have hC' : At C pc (.addi d 0 0 :: liB d v.toNat 8) := by simpa [liT, hv] using hC
  have hT : At C (pc + 1) (liB d v.toNat 8) := hC'.cons_tail
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have h0 := hC'.at 0 (by simp); simp at h0
    simp [run] at hc; subst hc; simp [Safe, h0, hd32, hx0]
  obtain ⟨j, hj⟩ : ∃ j, i = 1 + 2 * j ∨ i = 2 + 2 * j := ⟨(i - 1) / 2, by omega⟩
  have hj7 : j ≤ 7 := by omega
  have hA := liB_at hT (show j + 1 ≤ 8 by omega)
  have h0 : C[pc + 1 + 2 * j]? = some (.slli d d 8) := by
    have := hA.at (2 * j) (by simp [liB_len] <;> omega); simp [liB, liJ, liB_len] at this; exact this
  have h1 : C[pc + 1 + 2 * j + 1]? = some (.addi d d (((v.toNat / 2 ^ (56 - 8 * j)) % 256 : Nat) : Int)) := by
    have := hA.at (2 * j + 1) (by simp [liB_len] <;> omega)
    simp [liB, liJ, liB_len] at this; rw [← Nat.add_assoc] at this; exact this
  obtain ⟨sj, hrj, hxj, -, -⟩ := li_loop s hd hx0 hv hC j (by omega)
  rcases hj with rfl | rfl
  · rw [hrj] at hc; simp at hc; subst hc; simp [Safe, h0, hd32]
  · rw [show 2 + 2 * j = (1 + 2 * j) + 1 by omega, run_add hrj] at hc
    simp [run, step, h0, wr, hd] at hc; subst hc
    simp only [Safe, show pc + 1 + 2 * j + 1 = pc + 1 + 2 * j + 1 from rfl, h1, upd_same, hxj]
    have hAlt : v.toNat / 2 ^ (64 - 8 * j) < 2 ^ 56 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      calc v.toNat < 2 ^ 64 := v.toNat_lt
        _ ≤ 2 ^ 56 * 2 ^ (64 - 8 * j) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
    have hb : (v.toNat / 2 ^ (56 - 8 * j)) % 256 < 256 := Nat.mod_lt _ (by decide)
    have hs : (UInt64.ofNat (v.toNat / 2 ^ (64 - 8 * j)) <<< 8).toNat = v.toNat / 2 ^ (64 - 8 * j) * 256 := by
      simp [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    rw [hs]
    refine ⟨hd32, hd32, by omega, by omega, by omega, by omega⟩

/-! ## CONST -/

theorem const_srun {K : LayW} {C pc tgt} {v : UInt64} (s : St) (hx0 : s.x 0 = 0) (hC : At C pc (constT tgt pc v))
    (hh : (s.x 30).toNat + 8 ≤ (s.x 31).toNat) (hw : wok K ((s.x 31).toNat - 8)) :
    ∃ s', SStar K C (pc, s) (pc + (liT 5 v).length + 4, s') ∧
      s'.x = upd (upd s.x 5 v) 31 (UInt64.ofNat ((s.x 31).toNat - 8)) ∧
      s'.m = upd s.m ((s.x 31).toNat - 8) v ∧ s'.b = s.b := by
  obtain ⟨s1, hr1, hx1, hm1, hb1⟩ := li_srun (K := K) (d := 5) s (by decide) (by decide) hx0 hC.left
  have hP : At C (pc + (liT 5 v).length) (push 5 ((tgt : Int) - ((pc + (liT 5 v).length : Nat) + 2))) := by
    simpa [constT, pushA] using hC.right
  have e31 : s1.x 31 = s.x 31 := by rw [hx1]; exact upd_other _ _ (by decide)
  have e30 : s1.x 30 = s.x 30 := by rw [hx1]; exact upd_other _ _ (by decide)
  have e5 : s1.x 5 = v := by rw [hx1]; exact upd_same _ _ _
  have r2 := push_srun (K := K) (s := s1) hP (by decide) (by decide) (by decide) (by rw [e31, e30]; exact hh)
    (by rw [e31]; exact hw)
  refine ⟨_, hr1.trans r2, ?_, ?_, ?_⟩
  · simp only; rw [e31, hx1]
  · simp only; rw [e31, e5, hm1]
  · simp only; exact hb1

/-! ## LOCAL (w words: ld from the slot, checked push) -/

theorem local_srun {K : LayW} {C tgt p} : ∀ (w k pc : Nat) (st : St), At C pc (localT tgt p k pc w) →
    (st.x 8).toNat < 2 ^ 62 → p < 2 ^ 20 →
    (∀ i, i < w → (k + i < p ∨ 8 * (k + i - p + 1) ≤ (st.x 8).toNat) ∧ (st.x 31).toNat ≤ slotAddr p (k + i) (st.x 8).toNat) →
    (st.x 30).toNat + 8 * w ≤ (st.x 31).toNat →
    (∀ i, i < w → wok K (slotAddr p (k + i) (st.x 8).toNat) ∧ wok K ((st.x 31).toNat - 8 * (i + 1)) ∧
      -2048 ≤ offOf p (k + i) ∧ offOf p (k + i) < 2048) →
    ∀ b, run C (4 * w) (pc, st) = some b → SStar K C (pc, st) b
  | 0, k, pc, st, _, _, _, _, _, _, b, hb => by simp [run] at hb; subst hb; exact .refl _
  | w + 1, k, pc, st, hC, hs0, hp, hsl, hh, hw, b, hb => by
    have hA : At C pc ([.ld 5 8 (offOf p k)] ++ pushA tgt (pc + 1) 5 ++ localT tgt p (k + 1) (pc + 5) w) := hC
    have hL : At C pc [.ld 5 8 (offOf p k)] := hA.left.left
    have hP : At C (pc + 1) (pushA tgt (pc + 1) 5) := by simpa using hA.left.right
    have hR : At C (pc + 5) (localT tgt p (k + 1) (pc + 5) w) := by
      have := hA.right
      simpa [pushA, push] using this
    have l0 := hL.at 0 (by simp); simp at l0
    obtain ⟨hk0, hk1⟩ := hsl 0 (by omega)
    obtain ⟨w0, w1, o1, o2⟩ := hw 0 (by omega)
    simp only [Nat.add_zero] at hk0 hk1 w0 w1 o1 o2
    have ea0 : ea (st.x 8) (offOf p k) = slotAddr p k (st.x 8).toNat :=
      ea_slot p k _ hs0 hp hk0 _ rfl
    let v := st.m (slotAddr p k (st.x 8).toNat)
    let st1 : St := ⟨upd st.x 5 v, st.m, st.b⟩
    have s1 : step C (pc, st) = some (pc + 1, st1) := by simp [step, l0, wr, ea0, v, st1]
    have r1 : run C 1 (pc, st) = some (pc + 1, st1) := by simp [run, s1]
    have x31 : st1.x 31 = st.x 31 := by simp [st1, upd_ne]
    have x30 : st1.x 30 = st.x 30 := by simp [st1, upd_ne]
    have x8' : st1.x 8 = st.x 8 := by simp [st1, upd_ne]
    have hh1 : (st1.x 30).toNat + 8 ≤ (st1.x 31).toNat := by rw [x31, x30]; omega
    have r2 := push_run (s := st1) (by simpa [pushA] using hP) (by decide) (by decide) hh1
    have q2 := push_srun (K := K) (s := st1) (by simpa [pushA] using hP) (by decide) (by decide) (by decide) hh1
      (by rw [x31]; simpa using w1)
    have safe0 : Safe K C (pc, st) := by
      simp only [Safe, l0]
      refine ⟨by decide, by decide, o1, o2, ?_, ?_⟩
      · unfold offOf; split <;> omega
      · rw [ea0]; exact w0
    let st2 : St := ⟨upd st1.x 31 (UInt64.ofNat ((st1.x 31).toNat - 8)), upd st1.m ((st1.x 31).toNat - 8) (st1.x 5), st1.b⟩
    have sp1 : (st2.x 31).toNat = (st.x 31).toNat - 8 := by
      simp only [st2, upd_same, x31]; simp only [UInt64.toNat_ofNat']; have := (st.x 31).toNat_lt; omega
    have x8'' : st2.x 8 = st.x 8 := by simp [st2, upd_ne, x8']
    have x30'' : st2.x 30 = st.x 30 := by simp [st2, upd_ne, x30]
    have hsl2 : ∀ i, i < w → (k + 1 + i < p ∨ 8 * (k + 1 + i - p + 1) ≤ (st2.x 8).toNat) ∧
        (st2.x 31).toNat ≤ slotAddr p (k + 1 + i) (st2.x 8).toNat := by
      intro i hi
      obtain ⟨a1, a2⟩ := hsl (i + 1) (by omega)
      rw [x8'']; refine ⟨by rw [show k + 1 + i = k + (i + 1) by omega]; exact a1, ?_⟩
      rw [sp1]; rw [show k + 1 + i = k + (i + 1) by omega]; omega
    have hh2 : (st2.x 30).toNat + 8 * w ≤ (st2.x 31).toNat := by rw [x30'', sp1]; omega
    have hw2 : ∀ i, i < w → wok K (slotAddr p (k + 1 + i) (st2.x 8).toNat) ∧ wok K ((st2.x 31).toNat - 8 * (i + 1)) ∧
        -2048 ≤ offOf p (k + 1 + i) ∧ offOf p (k + 1 + i) < 2048 := by
      intro i hi
      obtain ⟨a1, a2, a3, a4⟩ := hw (i + 1) (by omega)
      rw [x8'', sp1, show k + 1 + i = k + (i + 1) by omega]
      refine ⟨a1, ?_, a3, a4⟩
      rw [show (st.x 31).toNat - 8 - 8 * (i + 1) = (st.x 31).toNat - 8 * (i + 1 + 1) by omega]; exact a2
    rw [show 4 * (w + 1) = 1 + (3 + 4 * w) by omega, run_add r1, run_add r2] at hb
    have ih := local_srun w (k + 1) (pc + 5) st2 hR (by rw [x8'']; exact hs0) hp hsl2 hh2 hw2 b hb
    exact (SStar.one safe0 s1).trans (q2.trans ih)

/-! ## popSlot / popN (LET, the epilogue's argument pops) -/

theorem popSlot_srun {K : LayW} {C : List J} {pc p k : Nat} (s : St) (hS : At C pc (Templates.popSlot p k))
    (hlt : (s.x 31).toNat + 8 < 2 ^ 64) (w0 : wok K (s.x 31).toNat)
    (o1 : -2048 ≤ Templates.slotOff p k) (o2 : Templates.slotOff p k < 2048)
    (hn : 0 ≤ ((s.x 8).toNat : Int) + Templates.slotOff p k) (ws : wok K (Templates.slotAddr p (s.x 8).toNat k)) :
    SStar K C (pc, s) (pc + 3, ⟨upd (upd s.x 5 (s.m (s.x 31).toNat)) 31 (UInt64.ofNat ((s.x 31).toNat + 8)),
      upd s.m (Templates.slotAddr p (s.x 8).toNat k) (s.m (s.x 31).toNat), s.b⟩) := by
  refine sstar_of_run (Templates.popSlot_run s hS hlt) fun j hj c hc => ?_
  have c0 := hS.at 0 (by simp [Templates.popSlot]); have c1 := hS.at 1 (by simp [Templates.popSlot])
  have c2 := hS.at 2 (by simp [Templates.popSlot])
  simp [Templates.popSlot] at c0 c1 c2
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · simp [run] at hc; subst hc; simp [Safe, c0, ea]; exact w0
  · simp [run, step, c0, wr] at hc; subst hc; simp [Safe, c1, upd]; omega
  · simp [run, step, c0, c1, wr] at hc; subst hc
    simp only [Safe, c2]
    refine ⟨by decide, by decide, o1, o2, by simpa [upd] using hn, ?_⟩
    simpa [ea, upd, Templates.slotAddr] using ws

/-- **pop w words into slots** (the slots and stack cells are work cells, offsets in range) -/
theorem popN_srun {K : LayW} {C : List J} {p k0 : Nat} : ∀ (w pc : Nat) (s : St), At C pc (Templates.popN p k0 w) →
    (s.x 31).toNat + 8 * w < 2 ^ 63 →
    (∀ j, j < w → wok K ((s.x 31).toNat + 8 * j) ∧ wok K (Templates.slotAddr p (s.x 8).toNat (k0 + j)) ∧
      -2048 ≤ Templates.slotOff p (k0 + j) ∧ Templates.slotOff p (k0 + j) < 2048 ∧
      0 ≤ ((s.x 8).toNat : Int) + Templates.slotOff p (k0 + j)) →
    ∀ b, run C (3 * w) (pc, s) = some b → SStar K C (pc, s) b
  | 0, pc, s, _, _, _, b, hb => by simp [run] at hb; subst hb; exact .refl _
  | w + 1, pc, s, hC, hlt, hw, b, hb => by
    have hC' : At C pc (Templates.popSlot p (k0 + w) ++ Templates.popN p k0 w) := hC
    have A1 : At C pc (Templates.popSlot p (k0 + w)) := hC'.left
    have A2 : At C (pc + 3) (Templates.popN p k0 w) := by have := hC'.right; simpa [Templates.popSlot] using this
    obtain ⟨a0, -, -, -, -⟩ := hw 0 (by omega)
    obtain ⟨-, a1, a2, a3, a4⟩ := hw w (by omega)
    have r1 := Templates.popSlot_run (k := k0 + w) s A1 (by omega)
    have q1 := popSlot_srun (K := K) (k := k0 + w) s A1 (by omega) (by simpa using a0) a2 a3 a4 a1
    generalize hs1 : (⟨upd (upd s.x 5 (s.m (s.x 31).toNat)) 31 (UInt64.ofNat ((s.x 31).toNat + 8)),
      upd s.m (Templates.slotAddr p (s.x 8).toNat (k0 + w)) (s.m (s.x 31).toNat), s.b⟩ : St) = s1 at r1 q1
    have t1 : (s1.x 31).toNat = (s.x 31).toNat + 8 := by subst hs1; simp [upd]; omega
    have x81 : s1.x 8 = s.x 8 := by subst hs1; simp [upd]
    rw [show 3 * (w + 1) = 3 + 3 * w by omega, run_add r1] at hb
    refine q1.trans (popN_srun w (pc + 3) s1 A2 (by omega) (fun j hj => ?_) b hb)
    obtain ⟨b0, b1, b2, b3, b4⟩ := hw (j + 1) (by omega)
    obtain ⟨-, c1, c2, c3, c4⟩ := hw j (by omega)
    rw [t1, x81]
    exact ⟨by rw [show (s.x 31).toNat + 8 + 8 * j = (s.x 31).toNat + 8 * (j + 1) by omega]; exact b0, c1, c2, c3, c4⟩

end SafeRun
