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
import Nano.V2Self.Proof.Heap
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

/-- every state of the first k steps from a is safe -/
def SR (K : LayW) (C : List J) (k : Nat) (a : Nat × St) : Prop := ∀ j, j < k → ∀ c, run C j a = some c → Safe K C c

theorem SR.add {K : LayW} {C : List J} {k1 k2 : Nat} {a b : Nat × St} (h1 : SR K C k1 a) (hr : run C k1 a = some b)
    (h2 : SR K C k2 b) : SR K C (k1 + k2) a := fun j hj c hc => by
  by_cases hjk : j < k1
  · exact h1 j hjk c hc
  · have := run_add (l := j - k1) hr
    rw [show k1 + (j - k1) = j by omega, hc] at this
    exact h2 (j - k1) (by omega) c this.symm

theorem SR.one {K : LayW} {C : List J} {a : Nat × St} (h : Safe K C a) : SR K C 1 a := fun j hj c hc => by
  have : j = 0 := by omega
  subst this; simp [run] at hc; subst hc; exact h

theorem push_sr {K : LayW} {C pc s r oom} (hC : At C pc (push r oom)) (hr32 : r < 32)
    (hh : (s.x 30).toNat + 8 ≤ (s.x 31).toNat) (hw : wok K ((s.x 31).toNat - 8)) : SR K C 3 (pc, s) := by
  intro j hj c hc
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

theorem push_srun {K : LayW} {C pc s r oom} (hC : At C pc (push r oom)) (hr : r ≠ 31) (hr0 : r ≠ 0) (hr32 : r < 32)
    (hh : (s.x 30).toNat + 8 ≤ (s.x 31).toNat) (hw : wok K ((s.x 31).toNat - 8)) :
    SStar K C (pc, s) (pc + 4, ⟨upd s.x 31 (UInt64.ofNat ((s.x 31).toNat - 8)),
                                 upd s.m ((s.x 31).toNat - 8) (s.x r), s.b⟩) :=
  sstar_of_run (push_run hC hr hr0 hh) (push_sr hC hr32 hh hw)

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

theorem li_sr {K : LayW} {C pc d} {v : UInt64} (s : St) (hd : d ≠ 0) (hd32 : d < 32) (hx0 : s.x 0 = 0)
    (hC : At C pc (liT d v)) : SR K C (liT d v).length (pc, s) := by
  intro i hi c hc
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

theorem li_srun {K : LayW} {C pc d} {v : UInt64} (s : St) (hd : d ≠ 0) (hd32 : d < 32) (hx0 : s.x 0 = 0)
    (hC : At C pc (liT d v)) :
    ∃ s', SStar K C (pc, s) (pc + (liT d v).length, s') ∧ s'.x = upd s.x d v ∧ s'.m = s.m ∧ s'.b = s.b := by
  obtain ⟨s', hr, hx, hm, hb⟩ := li_run s hd hx0 hC
  exact ⟨s', sstar_of_run hr (li_sr s hd hd32 hx0 hC), hx, hm, hb⟩

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

/-! ## the prologue (proA): push ra, push s0, s0 := t6, t6 -= 8r, room check -/

theorem pro_srun {K : LayW} {C : List J} {f r tgt : Nat} {s : St} (hC : At C f (proA tgt f r))
    (hlt : (s.x 31).toNat < 2 ^ 63) (hh : (s.x 30).toNat + 16 + 8 * r ≤ (s.x 31).toNat) (hr : r ≤ 256)
    (w1 : wok K ((s.x 31).toNat - 8)) (w2 : wok K ((s.x 31).toNat - 16)) :
    ∃ s1, SStar K C (f, s) (f + 12, s1) ∧
      (s1.x 31).toNat = (s.x 31).toNat - 16 - 8 * r ∧ (s1.x 8).toNat = (s.x 31).toNat - 16 ∧
      (∀ i, i ≠ 31 → i ≠ 8 → s1.x i = s.x i) ∧
      s1.m = upd (upd s.m ((s.x 31).toNat - 8) (s.x 1)) ((s.x 31).toNat - 16) (s.x 8) := by
  obtain ⟨s1, hr9, p1, p2, p3, p4⟩ := pro_runA hC hlt hh
  refine ⟨s1, sstar_of_run hr9 ?_, p1, p2, p3, p4⟩
  have A1 : At C f (push 1 ((tgt : Int) - ((f : Int) + 2))) := hC.left
  have R1 : At C (f + 4) (push 8 ((tgt : Int) - (((f + 4 : Nat) : Int) + 2)) ++
      [.addi 8 31 0, .addi 31 31 (-8 * (r : Int)), .bgeu 31 30 2, .jal 0 ((tgt : Int) - ((f : Int) + 11))]) := by
    simpa [proA, pushA, push] using hC.right
  have A2 : At C (f + 4) (push 8 ((tgt : Int) - (((f + 4 : Nat) : Int) + 2))) := R1.left
  have A3 : At C (f + 8) [.addi 8 31 0, .addi 31 31 (-8 * (r : Int)), .bgeu 31 30 2, .jal 0 ((tgt : Int) - ((f : Int) + 11))] := by
    simpa [push] using R1.right
  have r1 := push_run (s := s) A1 (by decide) (by decide) (by omega)
  have q1 := push_sr (K := K) (s := s) A1 (by decide) (by omega) w1
  have lt : (s.x 31).toNat < 2 ^ 64 := (s.x 31).toNat_lt
  have t8 : (UInt64.ofNat ((s.x 31).toNat - 8)).toNat = (s.x 31).toNat - 8 := by simp; omega
  have t16' : (UInt64.ofNat ((s.x 31).toNat - 16)).toNat = (s.x 31).toNat - 16 := by simp; omega
  let sA : St := ⟨upd s.x 31 (UInt64.ofNat ((s.x 31).toNat - 8)), upd s.m ((s.x 31).toNat - 8) (s.x 1), s.b⟩
  have xA31 : (sA.x 31).toNat = (s.x 31).toNat - 8 := by simp [sA, upd_same, t8]
  have xA30 : sA.x 30 = s.x 30 := by simp [sA, upd_other _ _ (show (30:Nat) ≠ 31 by decide)]
  have r2 := push_run (s := sA) A2 (by decide) (by decide) (by rw [xA30, xA31]; omega)
  have q2 := push_sr (K := K) (s := sA) A2 (by decide) (by rw [xA30, xA31]; omega)
    (by rw [xA31, show (s.x 31).toNat - 8 - 8 = (s.x 31).toNat - 16 by omega]; exact w2)
  have b0 := A3.at 0 (by simp); have b1 := A3.at 1 (by simp); have b2 := A3.at 2 (by simp)
  simp at b0 b1 b2
  let sB : St := ⟨upd sA.x 31 (UInt64.ofNat ((sA.x 31).toNat - 8)), upd sA.m ((sA.x 31).toNat - 8) (sA.x 8), sA.b⟩
  have xB31 : (sB.x 31).toNat = (s.x 31).toNat - 16 := by simp [sB, upd_same, xA31]; omega
  have q3 : SR K C 3 (f + 8, sB) := by
    intro j hj c hc
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · simp [run] at hc; subst hc; simp [Safe, b0]; omega
    · simp [run, step, b0] at hc; subst hc
      simp [Safe, b1, wr]
      rw [upd_other _ _ (show (31:Nat) ≠ 8 by decide), xB31]
      have := (s.x 31).toNat_lt
      omega
    · simp [run, step, b0, b1] at hc; subst hc; simp [Safe, b2]
  have hsum := (q1.add r1 (q2.add r2 q3))
  exact hsum

/-! ## the epilogue (epi): ld a4/a5, copy the q result words up, t6 := s0 + 8p + 16 − 8q, s0 := a5, jalr a4 -/

theorem copy_sr {K : LayW} {C pc p q} (s : St) (hq : ∀ k, k ≤ q → At C pc (copy p q k))
    (hD : (s.x 31).toNat + 8 * q ≤ (s.x 8).toNat + 8 * p + 16) (hp : 8 * p + 16 < 2048) (hqb : 8 * q < 2048)
    (hw : ∀ k, k < q → wok K ((s.x 31).toNat + 8 * (q - 1 - k)) ∧ wok K ((s.x 8).toNat + 8 * p + 16 - 8 * (k + 1))) :
    ∀ k, k ≤ q → SR K C (2 * k) (pc, s)
  | 0, _ => fun j hj => absurd hj (by omega)
  | k + 1, hk => by
    have ih := copy_sr s hq hD hp hqb hw k (by omega)
    obtain ⟨s', hr, hx, -, -⟩ := copy_run s hq hD k (by omega)
    have hA := hq (k + 1) hk
    have h0 : C[pc + 2 * k]? = some (.ld 5 31 (8 * ((q - 1 - k : Nat) : Int))) := by
      have := hA.at (2 * k) (by simp only [copy_len]; omega); simp [copy, copy_len, copyJ] at this; exact this
    have h1 : C[pc + 2 * k + 1]? = some (.sd 5 8 (8 * (p : Int) + 16 - 8 * ((k + 1 : Nat) : Int))) := by
      have := hA.at (2 * k + 1) (by simp only [copy_len]; omega)
      simp [copy, copy_len, copyJ] at this; rw [← Nat.add_assoc] at this; exact this
    obtain ⟨w1, w2⟩ := hw k (by omega)
    have x31 : s'.x 31 = s.x 31 := hx 31 (by decide)
    have x8 : s'.x 8 = s.x 8 := hx 8 (by decide)
    have q2 : SR K C 2 (pc + 2 * k, s') := by
      intro j hj c hc
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · simp [run] at hc; subst hc
        simp only [Safe, h0, x31]
        refine ⟨by decide, by decide, by omega, by omega, by omega, ?_⟩
        have : ea (s.x 31) (8 * ((q - 1 - k : Nat) : Int)) = (s.x 31).toNat + 8 * (q - 1 - k) := by simp only [ea]; omega
        rw [this]; exact w1
      · simp [run, step, h0] at hc; subst hc
        simp only [Safe, h1, wr, show (5 : Nat) ≠ 0 by decide, if_false, upd_other _ _ (show (8:Nat) ≠ 5 by decide), x8]
        refine ⟨by decide, by decide, by omega, by omega, by omega, ?_⟩
        have : ea (s.x 8) (8 * (p : Int) + 16 - 8 * ((k + 1 : Nat) : Int)) = (s.x 8).toNat + 8 * p + 16 - 8 * (k + 1) := by
          simp only [ea]; omega
        rw [this]; exact w2
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    exact ih.add hr q2

theorem epi_srun {K : LayW} {C e p q} (s : St) (hC : At C e (epi p q))
    (hD : (s.x 31).toNat + 8 * q ≤ (s.x 8).toNat + 8 * p + 16) (hlt : (s.x 8).toNat + 8 * p + 16 < 2 ^ 63)
    (hp : 8 * p + 16 < 2048) (hqb : 8 * q < 2048) (wa : wok K ((s.x 8).toNat + 8)) (wb : wok K (s.x 8).toNat)
    (hw : ∀ k, k < q → wok K ((s.x 31).toNat + 8 * (q - 1 - k)) ∧ wok K ((s.x 8).toNat + 8 * p + 16 - 8 * (k + 1)))
    (hra : ∃ j, (s.m ((s.x 8).toNat + 8)).toNat = K.base + 4 * j) :
    ∃ s3, SStar K C (e, s) (((s.m ((s.x 8).toNat + 8)).toNat - s.b) / 4, s3) ∧ s3.b = s.b ∧
      (s3.x 31).toNat = (s.x 8).toNat + 8 * p + 16 - 8 * q ∧ s3.x 8 = s.m (s.x 8).toNat ∧
      (∀ i, i ≠ 31 → i ≠ 8 → i ≠ 5 → i ≠ 14 → i ≠ 15 → s3.x i = s.x i) ∧
      s3.m = Mc s.m (s.x 31).toNat ((s.x 8).toNat + 8 * p + 16) q q := by
  obtain ⟨s3, hr, p1, p2, p3, p4, p5⟩ := epi_run s hC hD hlt
  refine ⟨s3, sstar_of_run hr ?_, p1, p2, p3, p4, p5⟩
  have a0 := hC.at 0 (by simp [epi]); have a1 := hC.at 1 (by simp [epi])
  simp [epi] at a0 a1
  have R : At C (e + 2) (copy p q q ++ [.addi 31 8 (8 * (p : Int) + 16 - 8 * (q : Int)), .addi 8 15 0, .jalr 0 14]) := by
    simpa [epi] using hC.right (l1 := [.ld 14 8 8, .ld 15 8 0])
  have T3 := R.right
  rw [copy_len] at T3
  have c0 := T3.at 0 (by simp); have c1 := T3.at 1 (by simp); have c2 := T3.at 2 (by simp)
  simp at c0 c1 c2
  have e8 : ea (s.x 8) 8 = (s.x 8).toNat + 8 := by simp [ea]; omega
  have e0 : ea (s.x 8) 0 = (s.x 8).toNat := by simp [ea]
  let s' : St := ⟨upd (upd s.x 14 (s.m ((s.x 8).toNat + 8))) 15 (s.m (s.x 8).toNat), s.m, s.b⟩
  have r2 : run C 2 (e, s) = some (e + 2, s') := by
    simp [run, step, a0, a1, wr, e8, e0, upd_other _ _ (show (8:Nat) ≠ 14 by decide), s']
  have q1 : SR K C 2 (e, s) := by
    intro j hj c hc
    rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
    · simp [run] at hc; subst hc; simp only [Safe, a0, e8]; exact ⟨by decide, by decide, by decide, by decide, by omega, wa⟩
    · simp [run, step, a0, wr, e8] at hc; subst hc
      simp [Safe, a1, upd_other _ _ (show (8:Nat) ≠ 14 by decide), e0]; exact wb
  have x31 : s'.x 31 = s.x 31 := by simp [s', upd]
  have x8 : s'.x 8 = s.x 8 := by simp [s', upd]
  have hD' : (s'.x 31).toNat + 8 * q ≤ (s'.x 8).toNat + 8 * p + 16 := by rw [x31, x8]; exact hD
  obtain ⟨s'', hr', hx, -, hbb⟩ := copy_run (C := C) (pc := e + 2) (p := p) (q := q) s'
    (fun k hk => copy_at R.left hk) hD' q (Nat.le_refl _)
  have q2 := copy_sr (K := K) (C := C) (pc := e + 2) (p := p) (q := q) s' (fun k hk => copy_at R.left hk) hD' hp hqb
    (fun k hk => by rw [x31, x8]; exact hw k hk) q (Nat.le_refl _)
  have y8 : s''.x 8 = s.x 8 := by rw [hx 8 (by decide), x8]
  have y14 : s''.x 14 = s.m ((s.x 8).toNat + 8) := by rw [hx 14 (by decide)]; simp [s', upd]
  have q3 : SR K C 3 (e + 2 + 2 * q, s'') := by
    intro j hj c hc
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · simp [run] at hc; subst hc; simp only [Safe, c0, y8]
      refine ⟨by decide, by decide, by omega, by omega, by omega, by omega⟩
    · simp [run, step, c0] at hc; subst hc; simp [Safe, c1]
      generalize (wr s'' 31 _).x 15 = z
      have := z.toNat_lt; omega
    · simp [run, step, c0, c1] at hc; subst hc
      simp only [Safe, c2, wr, show (31 : Nat) ≠ 0 by decide, show (8 : Nat) ≠ 0 by decide, if_false,
        upd_other _ _ (show (14:Nat) ≠ 8 by decide), upd_other _ _ (show (14:Nat) ≠ 31 by decide), y14]
      exact ⟨trivial, by decide, hra⟩
  rw [show 2 + 2 * q + 3 = 2 + (2 * q + 3) by omega]
  exact q1.add r2 (q2.add hr' q3)

/-! ## BPUSH -/

theorem bpush_srun {K : LayW} {C : List J} {pc tgt : Nat} (s : St) (hC : At C pc (bpushT tgt pc)) (hx0 : s.x 0 = 0)
    (hsp : (s.x 31).toNat + 16 < 2 ^ 63)
    (hlen : (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat < (s.m ((s.m ((s.x 31).toNat + 8)).toNat + 8)).toNat)
    (hb : (s.m ((s.x 31).toNat + 8)).toNat + 16 + 8 * (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat < 2 ^ 62)
    (w0 : wok K (s.x 31).toNat) (w1 : wok K ((s.x 31).toNat + 8)) (w2 : wok K (s.m ((s.x 31).toNat + 8)).toNat)
    (w3 : wok K ((s.m ((s.x 31).toNat + 8)).toNat + 8))
    (w4 : wok K ((s.m ((s.x 31).toNat + 8)).toNat + 16 + 8 * (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat)) :
    ∃ s', SStar K C (pc, s) (pc + 12, s') ∧
      s'.m = upd (upd s.m ((s.m ((s.x 31).toNat + 8)).toNat + 16 + 8 * (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat)
                  (s.m (s.x 31).toNat))
              (s.m ((s.x 31).toNat + 8)).toNat ((s.m (s.m ((s.x 31).toNat + 8)).toNat) + 1) ∧
      (s'.x 31).toNat = (s.x 31).toNat + 8 ∧ s'.b = s.b ∧
      (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 15 → r ≠ 31 → s'.x r = s.x r) := by
  obtain ⟨s', hr, rest⟩ := bpush_runK s hC hx0 hsp hlen hb
  refine ⟨s', sstar_of_run hr ?_, rest⟩
  intro j hj c hc

  have hs : ∀ i, i < 12 → C[pc + i]? = (bpushT tgt pc)[i]? := fun i hi => hC i (by simp [bpushT]; omega)
  have h0 := hs 0 (by omega); have h1 := hs 1 (by omega); have h2 := hs 2 (by omega); have h3 := hs 3 (by omega)
  have h4 := hs 4 (by omega); have h5 := hs 5 (by omega); have h7 := hs 7 (by omega); have h8 := hs 8 (by omega)
  have h9 := hs 9 (by omega); have h10 := hs 10 (by omega); have h11 := hs 11 (by omega)
  simp [bpushT] at h0 h1 h2 h3 h4 h5 h7 h8 h9 h10 h11
  have lt := (s.x 31).toNat_lt
  have e0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have e8 : ea (s.x 31) 8 = (s.x 31).toNat + 8 := by simp [ea]; omega
  have t8 : (s.x 31 + 8).toNat = (s.x 31).toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have eb0 : ∀ b : UInt64, ea b 0 = b.toNat := fun b => by simp [ea]
  have eb8 : ∀ b : UInt64, b.toNat + 8 < 2 ^ 64 → ea b 8 = b.toNat + 8 := fun b h => by simp [ea]; omega
  have blt := (s.m ((s.x 31).toNat + 8)).toNat_lt
  have sh : ((s.m (s.m ((s.x 31).toNat + 8)).toNat) <<< 3).toNat = 8 * (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat := by
    have := (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat_lt
    simp [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have sa : ((s.m (s.m ((s.x 31).toNat + 8)).toNat <<< 3) + s.m ((s.x 31).toNat + 8)).toNat
      = 8 * (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat + (s.m ((s.x 31).toNat + 8)).toNat := by
    rw [UInt64.toNat_add, sh]; simp; omega
  have ea16 : ea ((s.m (s.m ((s.x 31).toNat + 8)).toNat <<< 3) + s.m ((s.x 31).toNat + 8)) 16
      = (s.m ((s.x 31).toNat + 8)).toNat + 16 + 8 * (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat := by
    simp only [ea, sa]; omega
  have hlt' : (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat < (s.m ((s.m ((s.x 31).toNat + 8)).toNat + 8)).toNat := hlen
  have ebuf8 : ea (s.m ((s.x 31).toNat + 8)) 8 = (s.m ((s.x 31).toNat + 8)).toNat + 8 := eb8 _ (by omega)
  have eL : UInt64.ofNat (ea (s.m (s.m ((s.x 31).toNat + 8)).toNat) 1) = s.m (s.m ((s.x 31).toNat + 8)).toNat + 1 := by
    have := (s.m ((s.m ((s.x 31).toNat + 8)).toNat + 8)).toNat_lt
    apply UInt64.toNat.inj; simp [ea, UInt64.toNat_add]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [run] at hc; subst hc; simp [Safe, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt'] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
  · simp [run, step, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 2).toNat = pc + 7 by omega] at hc; subst hc
    simp [Safe, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt'] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
  · simp [run, step, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 2).toNat = pc + 7 by omega] at hc; subst hc
    simp [Safe, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt'] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
  · simp [run, step, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 2).toNat = pc + 7 by omega] at hc; subst hc
    simp [Safe, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt'] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
  · simp [run, step, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 2).toNat = pc + 7 by omega] at hc; subst hc
    simp [Safe, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt'] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
  · simp [run, step, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 2).toNat = pc + 7 by omega] at hc; subst hc
    simp [Safe, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt'] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
  · simp [run, step, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 2).toNat = pc + 7 by omega] at hc; subst hc
    simp [Safe, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt'] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
  · simp [run, step, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 2).toNat = pc + 7 by omega] at hc; subst hc
    simp [Safe, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt'] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
  · simp [run, step, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 2).toNat = pc + 7 by omega] at hc; subst hc
    simp [Safe, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt'] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
  · simp [run, step, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 2).toNat = pc + 7 by omega] at hc; subst hc
    simp [Safe, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt'] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
  · simp [run, step, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 2).toNat = pc + 7 by omega] at hc; subst hc
    simp [Safe, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16, upd_same, upd_upd, upd_ne, hlt'] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩

/-! ## BSET -/

theorem bset_srun {K : LayW} {C : List J} {pc : Nat} (s : St) (hC : At C pc bsetT) (hx0 : s.x 0 = 0)
    (hsp : (s.x 31).toNat + 24 < 2 ^ 62)
    (hb : (s.m (s.m ((s.x 31).toNat + 16)).toNat).toNat > (s.m ((s.x 31).toNat + 8)).toNat →
      (s.m ((s.x 31).toNat + 16)).toNat + 16 + 8 * (s.m ((s.x 31).toNat + 8)).toNat < 2 ^ 62)
    (w0 : wok K (s.x 31).toNat) (w1 : wok K ((s.x 31).toNat + 8)) (w2 : wok K ((s.x 31).toNat + 16))
    (w3 : wok K (s.m ((s.x 31).toNat + 16)).toNat)
    (w4 : (s.m ((s.x 31).toNat + 8)).toNat < (s.m (s.m ((s.x 31).toNat + 16)).toNat).toNat →
      wok K ((s.m ((s.x 31).toNat + 16)).toNat + 16 + 8 * (s.m ((s.x 31).toNat + 8)).toNat)) :
    ∃ s', SStar K C (pc, s) (pc + 9, s') ∧
      s'.m = (if (s.m ((s.x 31).toNat + 8)).toNat < (s.m (s.m ((s.x 31).toNat + 16)).toNat).toNat
              then upd s.m ((s.m ((s.x 31).toNat + 16)).toNat + 16 + 8 * (s.m ((s.x 31).toNat + 8)).toNat) (s.m (s.x 31).toNat)
              else s.m) ∧
      (s'.x 31).toNat = (s.x 31).toNat + 16 ∧ s'.b = s.b ∧
      (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 31 → s'.x r = s.x r) := by
  obtain ⟨s', hr, rest⟩ := bset_runK s hC hx0 hsp hb
  refine ⟨s', sstar_of_run hr ?_, rest⟩
  intro j hj c hc

  have hs : ∀ i, i < 9 → C[pc + i]? = bsetT[i]? := fun i hi => hC i (by simp [bsetT]; omega)
  have h0 := hs 0 (by omega); have h1 := hs 1 (by omega); have h2 := hs 2 (by omega); have h3 := hs 3 (by omega)
  have h4 := hs 4 (by omega); have h5 := hs 5 (by omega); have h6 := hs 6 (by omega); have h7 := hs 7 (by omega)
  have h8 := hs 8 (by omega)
  simp [bsetT] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  have lt := (s.x 31).toNat_lt
  have e0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have e8 : ea (s.x 31) 8 = (s.x 31).toNat + 8 := by simp [ea]; omega
  have e16 : ea (s.x 31) 16 = (s.x 31).toNat + 16 := by simp [ea]; omega
  have t16 : (s.x 31 + 16).toNat = (s.x 31).toNat + 16 := by rw [UInt64.toNat_add]; simp; omega
  have eb0 : ∀ b : UInt64, ea b 0 = b.toNat := fun b => by simp [ea]
  by_cases hi : (s.m ((s.x 31).toNat + 8)).toNat < (s.m (s.m ((s.x 31).toNat + 16)).toNat).toNat
  · have hb' := hb hi
    have w4' := w4 hi
    have sh : ((s.m ((s.x 31).toNat + 8)) <<< 3).toNat = 8 * (s.m ((s.x 31).toNat + 8)).toNat := by
      have := (s.m ((s.x 31).toNat + 8)).toNat_lt
      simp [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have sa : ((s.m ((s.x 31).toNat + 16)) + (s.m ((s.x 31).toNat + 8)) <<< 3).toNat
        = (s.m ((s.x 31).toNat + 16)).toNat + 8 * (s.m ((s.x 31).toNat + 8)).toNat := by
      rw [UInt64.toNat_add, sh]; simp; omega
    have ea16 : ea ((s.m ((s.x 31).toNat + 16)) + (s.m ((s.x 31).toNat + 8)) <<< 3) 16
        = (s.m ((s.x 31).toNat + 16)).toNat + 16 + 8 * (s.m ((s.x 31).toNat + 8)).toNat := by
      simp only [ea, sa]; omega
    have hcc : ¬ (s.m (s.m ((s.x 31).toNat + 16)).toNat).toNat ≤ (s.m ((s.x 31).toNat + 8)).toNat := by omega
    simp only [if_pos hi] at hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [run] at hc; subst hc; simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hcc, hi, upd_ne, upd_same] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
  · have hcc : (s.m (s.m ((s.x 31).toNat + 16)).toNat).toNat ≤ (s.m ((s.x 31).toNat + 8)).toNat := by omega
    simp only [if_neg hi] at hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl
    · simp [run] at hc; subst hc; simp [Safe, h0, h1, h2, h3, h4, h5, wr, e0, e8, e16, t16, eb0, hcc, hi, upd_ne, upd_same] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, wr, e0, e8, e16, t16, eb0, hcc, hi, upd_ne, upd_same] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, wr, e0, e8, e16, t16, eb0, hcc, hi, upd_ne, upd_same] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, wr, e0, e8, e16, t16, eb0, hcc, hi, upd_ne, upd_same] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, wr, e0, e8, e16, t16, eb0, hcc, hi, upd_ne, upd_same] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, wr, e0, e8, e16, t16, eb0, hcc, hi, upd_ne, upd_same] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, wr, e0, e8, e16, t16, eb0, hcc, hi, upd_ne, upd_same] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, wr, e0, e8, e16, t16, eb0, hcc, hi, upd_ne, upd_same] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, wr, e0, e8, e16, t16, eb0, hcc, hi, upd_ne, upd_same] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, wr, e0, e8, e16, t16, eb0, hcc, hi, upd_ne, upd_same] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, wr, e0, e8, e16, t16, eb0, hcc, hi, upd_ne, upd_same] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩

/-! ## BGET -/

theorem bget_srun {K : LayW} {C pc} (s : St) (hC : At C pc bgetT) (hx0 : s.x 0 = 0) (hlt : (s.x 31).toNat + 16 < 2 ^ 63)
    (hb : (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat > (s.m (s.x 31).toNat).toNat →
      (s.m ((s.x 31).toNat + 8)).toNat + 16 + 8 * (s.m (s.x 31).toNat).toNat < 2 ^ 63)
    (w0 : wok K (s.x 31).toNat) (w1 : wok K ((s.x 31).toNat + 8)) (w2 : wok K (s.m ((s.x 31).toNat + 8)).toNat)
    (w3 : (s.m (s.x 31).toNat).toNat < (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat →
      wok K ((s.m ((s.x 31).toNat + 8)).toNat + 16 + 8 * (s.m (s.x 31).toNat).toNat)) :
    ∃ s', SStar K C (pc, s) (pc + 10, s') ∧
      s'.m = upd s.m ((s.x 31).toNat + 8)
        (if (s.m (s.x 31).toNat).toNat < (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat
         then s.m ((s.m ((s.x 31).toNat + 8)).toNat + 16 + 8 * (s.m (s.x 31).toNat).toNat) else 0) ∧
      s'.x 31 = UInt64.ofNat ((s.x 31).toNat + 8) ∧
      ∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 31 → s'.x r = s.x r := by
  obtain ⟨s', hr, rest⟩ := bget_runK s hC hx0 hlt hb
  refine ⟨s', sstar_of_run hr ?_, rest⟩
  intro j hj c hc
  have h0 := hC.at 0 (by simp [bgetT]); have h1 := hC.at 1 (by simp [bgetT]); have h2 := hC.at 2 (by simp [bgetT])
  have h3 := hC.at 3 (by simp [bgetT]); have h4 := hC.at 4 (by simp [bgetT]); have h5 := hC.at 5 (by simp [bgetT])
  have h6 := hC.at 6 (by simp [bgetT]); have h7 := hC.at 7 (by simp [bgetT]); have h8 := hC.at 8 (by simp [bgetT])
  have h9 := hC.at 9 (by simp [bgetT])
  simp [bgetT] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have lt : (s.x 31).toNat < 2 ^ 64 := (s.x 31).toNat_lt
  have e0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have e8 : ea (s.x 31) 8 = (s.x 31).toNat + 8 := by simp [ea]; omega
  have t8 : (UInt64.ofNat ((s.x 31).toNat + 8)).toNat = (s.x 31).toNat + 8 := by simp only [UInt64.toNat_ofNat']; omega
  have t8' : (s.x 31 + 8).toNat = (s.x 31).toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have e8'' : ea (s.x 31 + 8) 0 = (s.x 31).toNat + 8 := by simp only [ea, t8']; omega
  have e1 : ∀ b : UInt64, ea b 0 = b.toNat := by intro b; simp [ea]
  by_cases hi : (s.m (s.x 31).toNat).toNat < (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat
  · have hb' := hb hi
    have w3' := w3 hi
    simp only [if_pos hi] at hj
    have s3 : (s.m (s.x 31).toNat <<< 3).toNat = 8 * (s.m (s.x 31).toNat).toNat := by
      simp [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have hcc : ¬ (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat ≤ (s.m (s.x 31).toNat).toNat := by omega
    have sa : (s.m ((s.x 31).toNat + 8) + s.m (s.x 31).toNat <<< 3).toNat
        = (s.m ((s.x 31).toNat + 8)).toNat + 8 * (s.m (s.x 31).toNat).toNat := by
      rw [UInt64.toNat_add, s3]; simp; omega
    have ea16 : ea (s.m ((s.x 31).toNat + 8) + s.m (s.x 31).toNat <<< 3) 16
        = (s.m ((s.x 31).toNat + 8)).toNat + 16 + 8 * (s.m (s.x 31).toNat).toNat := by
      simp only [ea, sa]; omega
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [run] at hc; subst hc; simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', s3, ea16] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
  · simp only [if_neg hi] at hj
    have hcc : (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat ≤ (s.m (s.x 31).toNat).toNat := by omega
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [run] at hc; subst hc; simp [Safe, h0, h1, h2, h3, h4, h5, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 4).toNat = pc + 9 by omega] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 4).toNat = pc + 9 by omega] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 4).toNat = pc + 9 by omega] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 4).toNat = pc + 9 by omega] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 4).toNat = pc + 9 by omega] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 4).toNat = pc + 9 by omega] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 4).toNat = pc + 9 by omega] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 4).toNat = pc + 9 by omega] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 4).toNat = pc + 9 by omega] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 4).toNat = pc + 9 by omega] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 4).toNat = pc + 9 by omega] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 4).toNat = pc + 9 by omega] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, h9, wr, e0, e8, e8'', e1, hx0, aluf, upd_same, upd_upd, upd_ne, hi, hcc, t8, t8', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 4).toNat = pc + 9 by omega] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩

/-! ## RD -/

theorem rd_srun {K : LayW} {C pc} (s : St) (hC : At C pc rdT) (hx0 : s.x 0 = 0) (hb : (s.x 28).toNat + (s.x 29).toNat < 2 ^ 63)
    (w0 : wok K (s.x 31).toNat)
    (w1 : (s.m (s.x 31).toNat).toNat < (s.x 29).toNat →
      bok K ((s.x 28).toNat + (s.m (s.x 31).toNat).toNat)) :
    SStar K C (pc, s) (pc + 6,
      ⟨upd (upd s.x 6 (s.m (s.x 31).toNat)) 5
          (if (s.m (s.x 31).toNat).toNat < (s.x 29).toNat then lbm s.m ((s.x 28).toNat + (s.m (s.x 31).toNat).toNat) else 0),
       upd s.m (s.x 31).toNat
          (if (s.m (s.x 31).toNat).toNat < (s.x 29).toNat then lbm s.m ((s.x 28).toNat + (s.m (s.x 31).toNat).toNat) else 0), s.b⟩) := by
  refine sstar_of_run (rd_runK s hC hx0 hb) ?_
  intro j hj c hc
  have h0 := hC.at 0 (by simp [rdT]); have h1 := hC.at 1 (by simp [rdT]); have h2 := hC.at 2 (by simp [rdT])
  have h3 := hC.at 3 (by simp [rdT]); have h4 := hC.at 4 (by simp [rdT]); have h5 := hC.at 5 (by simp [rdT])
  simp [rdT] at h0 h1 h2 h3 h4 h5
  have e0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have e1 : ∀ b : UInt64, ea b 0 = b.toNat := by intro b; simp [ea]
  by_cases hi : (s.m (s.x 31).toNat).toNat < (s.x 29).toNat
  · simp only [if_pos hi] at hj
    have w1' := w1 hi
    have hs : (s.x 28 + s.m (s.x 31).toNat).toNat = (s.x 28).toNat + (s.m (s.x 31).toNat).toNat := by
      rw [UInt64.toNat_add]; simp; omega
    have hcc : ¬ (s.x 29).toNat ≤ (s.m (s.x 31).toNat).toNat := by omega
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [run] at hc; subst hc; simp [Safe, h0, h1, h2, h3, h4, h5, wr, e0, e1, hcc, hs, hi, hx0, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (28:Nat) ≠ 5 by decide), upd_other _ _ (show (28:Nat) ≠ 6 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide)] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, wr, e0, e1, hcc, hs, hi, hx0, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (28:Nat) ≠ 5 by decide), upd_other _ _ (show (28:Nat) ≠ 6 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide)] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, wr, e0, e1, hcc, hs, hi, hx0, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (28:Nat) ≠ 5 by decide), upd_other _ _ (show (28:Nat) ≠ 6 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide)] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, wr, e0, e1, hcc, hs, hi, hx0, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (28:Nat) ≠ 5 by decide), upd_other _ _ (show (28:Nat) ≠ 6 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide)] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, wr, e0, e1, hcc, hs, hi, hx0, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (28:Nat) ≠ 5 by decide), upd_other _ _ (show (28:Nat) ≠ 6 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide)] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, wr, e0, e1, hcc, hs, hi, hx0, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (28:Nat) ≠ 5 by decide), upd_other _ _ (show (28:Nat) ≠ 6 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide)] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, wr, e0, e1, hcc, hs, hi, hx0, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (28:Nat) ≠ 5 by decide), upd_other _ _ (show (28:Nat) ≠ 6 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide)] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, wr, e0, e1, hcc, hs, hi, hx0, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (28:Nat) ≠ 5 by decide), upd_other _ _ (show (28:Nat) ≠ 6 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide)] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, wr, e0, e1, hcc, hs, hi, hx0, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (28:Nat) ≠ 5 by decide), upd_other _ _ (show (28:Nat) ≠ 6 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide)] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h3, h4, h5, wr, e0, e1, hcc, hs, hi, hx0, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (28:Nat) ≠ 5 by decide), upd_other _ _ (show (28:Nat) ≠ 6 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide)] at hc; subst hc
      simp [Safe, h0, h1, h2, h3, h4, h5, wr, e0, e1, hcc, hs, hi, hx0, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (28:Nat) ≠ 5 by decide), upd_other _ _ (show (28:Nat) ≠ 6 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide)] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
  · simp only [if_neg hi] at hj
    have hcc : (s.x 29).toNat ≤ (s.m (s.x 31).toNat).toNat := by omega
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · simp [run] at hc; subst hc; simp [Safe, h0, h1, h2, h5, wr, e0, e1, hcc, hi, hx0, ea, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), show ((pc : Int) + 1 + 1 + 3).toNat = pc + 5 by omega] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h5, wr, e0, e1, hcc, hi, hx0, ea, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), show ((pc : Int) + 1 + 1 + 3).toNat = pc + 5 by omega] at hc; subst hc
      simp [Safe, h0, h1, h2, h5, wr, e0, e1, hcc, hi, hx0, ea, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), show ((pc : Int) + 1 + 1 + 3).toNat = pc + 5 by omega] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h5, wr, e0, e1, hcc, hi, hx0, ea, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), show ((pc : Int) + 1 + 1 + 3).toNat = pc + 5 by omega] at hc; subst hc
      simp [Safe, h0, h1, h2, h5, wr, e0, e1, hcc, hi, hx0, ea, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), show ((pc : Int) + 1 + 1 + 3).toNat = pc + 5 by omega] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩
    · simp [run, step, h0, h1, h2, h5, wr, e0, e1, hcc, hi, hx0, ea, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), show ((pc : Int) + 1 + 1 + 3).toNat = pc + 5 by omega] at hc; subst hc
      simp [Safe, h0, h1, h2, h5, wr, e0, e1, hcc, hi, hx0, ea, aluf, upd_same, upd_upd, upd_other _ _ (show (0:Nat) ≠ 6 by decide), upd_other _ _ (show (0:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 5 by decide), upd_other _ _ (show (31:Nat) ≠ 6 by decide), upd_other _ _ (show (29:Nat) ≠ 6 by decide), upd_other _ _ (show (29:Nat) ≠ 5 by decide), upd_other _ _ (show (6:Nat) ≠ 5 by decide), show ((pc : Int) + 1 + 1 + 3).toNat = pc + 5 by omega] <;> first | omega | assumption | exact ⟨by omega, by assumption⟩

/-! ## BNEW -/

theorem bnew_srun {L : LayW} {C : List J} {pc tgt κ : Nat} (s : St) (hC : At C pc (bnewT tgt pc κ)) (hx0 : s.x 0 = 0)
    (hκ : κ < 2 ^ 40) (hsp : (s.x 31).toNat < 2 ^ 62)
    (hroom : (s.x 30).toNat + 8 * (κ + 2) + 8 ≤ (s.x 31).toNat)
    (w0 : wok L (s.x 30).toNat) (w1 : wok L ((s.x 30).toNat + 8)) (w2 : wok L ((s.x 31).toNat - 8)) :
    ∃ s', SStar L C (pc, s) (pc + (bnewT tgt pc κ).length, s') ∧
      (s'.x 31).toNat = (s.x 31).toNat - 8 ∧ (s'.x 30).toNat = (s.x 30).toNat + 8 * (κ + 2) ∧ s'.x 5 = s.x 30 ∧
      s'.m = upd (upd (upd s.m (s.x 30).toNat 0) ((s.x 30).toNat + 8) (UInt64.ofNat κ)) ((s.x 31).toNat - 8) (s.x 30) ∧
      s'.b = s.b ∧ (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 30 → r ≠ 31 → s'.x r = s.x r) := by
  obtain ⟨s', hr, rest⟩ := bnew_runK s hC hx0 hκ hsp hroom
  refine ⟨s', sstar_of_run hr ?_, rest⟩

  have lt31 := (s.x 31).toNat_lt
  have lt30 := (s.x 30).toNat_lt
  have hC' : At C pc ([.addi 5 30 0] ++ (liT 6 (UInt64.ofNat ((κ + 2) * 8)) ++ ([.alu 1 6 6 30, .bgeu 31 6 2,
      .jal 0 ((tgt : Int) - ((pc + 1 + (liT 6 (UInt64.ofNat ((κ + 2) * 8))).length + 2 : Nat) : Int))] ++
      (liT 7 (UInt64.ofNat κ) ++ ([.sd 0 5 0, .sd 7 5 8, .addi 30 6 0] ++
      pushA tgt (pc + 1 + (liT 6 (UInt64.ofNat ((κ + 2) * 8))).length + 3 + (liT 7 (UInt64.ofNat κ)).length + 3) 5))))) := hC
  generalize hW : UInt64.ofNat ((κ + 2) * 8) = W at *
  generalize hK : UInt64.ofNat κ = K at *
  have hWn : W.toNat = (κ + 2) * 8 := by rw [← hW]; simp only [UInt64.toNat_ofNat']; omega
  have hKn : K.toNat = κ := by rw [← hK]; simp only [UInt64.toNat_ofNat']; omega
  have p1 := hC'.left
  have R1 : At C (pc + 1) (liT 6 W ++ ([.alu 1 6 6 30, .bgeu 31 6 2,
      .jal 0 ((tgt : Int) - ((pc + 1 + (liT 6 W).length + 2 : Nat) : Int))] ++
      (liT 7 K ++ ([.sd 0 5 0, .sd 7 5 8, .addi 30 6 0] ++ pushA tgt (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3) 5)))) := by
    simpa using hC'.right
  have p2 := R1.left
  have R2 : At C (pc + 1 + (liT 6 W).length) ([.alu 1 6 6 30, .bgeu 31 6 2,
      .jal 0 ((tgt : Int) - ((pc + 1 + (liT 6 W).length + 2 : Nat) : Int))] ++
      (liT 7 K ++ ([.sd 0 5 0, .sd 7 5 8, .addi 30 6 0] ++ pushA tgt (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3) 5))) := R1.right
  have p3 := R2.left
  have R3 : At C (pc + 1 + (liT 6 W).length + 3) (liT 7 K ++ ([.sd 0 5 0, .sd 7 5 8, .addi 30 6 0] ++
      pushA tgt (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3) 5)) := by simpa using R2.right
  have p4 := R3.left
  have R4 : At C (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length) ([.sd 0 5 0, .sd 7 5 8, .addi 30 6 0] ++
      pushA tgt (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3) 5) := R3.right
  have p5 := R4.left
  have p6 : At C (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3)
      (pushA tgt (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3) 5) := by simpa using R4.right
  have e30 : UInt64.ofNat (s.x 30).toNat = s.x 30 := by simp
  -- 1: t0 := t5
  have h1 := p1.at 0 (by simp); simp at h1
  let s1 : St := ⟨upd s.x 5 (s.x 30), s.m, s.b⟩
  have r1 : run C 1 (pc, s) = some (pc + 1, s1) := by
    simp [run, step, h1, wr, ea, e30, s1]
  have z1 : s1.x 0 = 0 := by simp [s1, upd_ne, hx0]
  -- 2: li t1 W
  obtain ⟨s2, r2, hx2, hm2, hb2⟩ := li_run (d := 6) s1 (by decide) z1 p2
  have a30 : s2.x 30 = s.x 30 := by rw [hx2]; simp [s1, upd_ne]
  have a31 : s2.x 31 = s.x 31 := by rw [hx2]; simp [s1, upd_ne]
  have a6 : s2.x 6 = W := by rw [hx2]; simp [upd_same]
  have a5 : s2.x 5 = s.x 30 := by rw [hx2]; simp [s1, upd_ne, upd_same]
  have a0 : s2.x 0 = 0 := by rw [hx2]; simp [s1, upd_ne, hx0]
  have mm2 : s2.m = s.m := hm2
  -- 3: t1 := t1 + t5
  have h3 := p3.at 0 (by simp); simp at h3
  let s3 : St := ⟨upd s2.x 6 (W + s.x 30), s2.m, s2.b⟩
  have r3 : run C 1 (pc + 1 + (liT 6 W).length, s2) = some (pc + 1 + (liT 6 W).length + 1, s3) := by
    simp [run, step, h3, wr, aluf, a6, a30, s3]
  -- 4: bgeu taken
  have h4 := p3.at 1 (by simp); simp at h4
  have hsum : (W + s.x 30).toNat = (κ + 2) * 8 + (s.x 30).toNat := by
    rw [UInt64.toNat_add, hWn]; simp; omega
  have r4 : step C (pc + 1 + (liT 6 W).length + 1, s3) = some (pc + 1 + (liT 6 W).length + 3, s3) := by
    have : (s3.x 6).toNat ≤ (s3.x 31).toNat := by
      simp [s3, upd_same, upd_ne, a31, hsum]; omega
    rw [s_bgeu_t h4 (by simpa using this)]
    first | rfl | (congr 1; congr 1; omega) | (congr 1; omega)
  -- 5: li t2 K
  have z3 : s3.x 0 = 0 := by simp [s3, upd_ne, a0]
  obtain ⟨s5, r5, hx5, hm5, hb5⟩ := li_run (d := 7) s3 (by decide) z3 p4
  have b30 : s5.x 30 = s.x 30 := by rw [hx5]; simp [s3, upd_ne, a30]
  have b31 : s5.x 31 = s.x 31 := by rw [hx5]; simp [s3, upd_ne, a31]
  have b6 : s5.x 6 = W + s.x 30 := by rw [hx5]; simp [s3, upd_ne, upd_same]
  have b5 : s5.x 5 = s.x 30 := by rw [hx5]; simp [s3, upd_ne, a5]
  have b7 : s5.x 7 = K := by rw [hx5]; simp [upd_same]
  have b0 : s5.x 0 = 0 := by rw [hx5]; simp [s3, upd_ne, a0]
  have mm5 : s5.m = s.m := by rw [hm5]; exact mm2
  -- 6, 7, 8: len := 0; cap := κ; t5 := t1
  have h6 := p5.at 0 (by simp); have h7 := p5.at 1 (by simp); have h8 := p5.at 2 (by simp)
  simp at h6 h7 h8
  have eT0 : ea (s5.x 5) 0 = (s.x 30).toNat := by simp [ea, b5]
  have eT8 : ea (s5.x 5) 8 = (s.x 30).toNat + 8 := by simp [ea, b5]; omega
  let s8 : St := ⟨upd s5.x 30 (W + s.x 30), upd (upd s5.m (s.x 30).toNat 0) ((s.x 30).toNat + 8) K, s5.b⟩
  have ea0 : ∀ b : UInt64, ea b 0 = b.toNat := fun b => by simp [ea]
  have e6 : UInt64.ofNat (ea (W + s.x 30) 0) = W + s.x 30 := by rw [ea0]; exact UInt64.ofNat_toNat
  have r678 : run C 3 (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length, s5) =
      some (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3, s8) := by
    simp [run, step, h6, h7, h8, wr, eT0, eT8, b0, b7, e6, b6, s8]
  have y30 : s8.x 30 = W + s.x 30 := by simp [s8, upd_same]
  have y31 : s8.x 31 = s.x 31 := by simp [s8, upd_ne, b31]
  have y5 : s8.x 5 = s.x 30 := by simp [s8, upd_ne, b5]
  have hh8 : (s8.x 30).toNat + 8 ≤ (s8.x 31).toNat := by
    rw [y30, y31, hsum]; omega
  have r4' : run C 1 (pc + 1 + (liT 6 W).length + 1, s3) = some (pc + 1 + (liT 6 W).length + 3, s3) := by simp [run, r4]
  have r9 := push_run (s := s8) (by simpa [pushA] using p6) (by decide) (by decide) hh8
  have q1 : SR L C 1 (pc, s) := SR.one (by simp [Safe, h1]; have := (s.x 30).toNat_lt; omega)
  have q2 := li_sr (K := L) (d := 6) (v := W) s1 (by decide) (by decide) z1 p2
  have q3 : SR L C 1 (pc + 1 + (liT 6 W).length, s2) := SR.one (by simp [Safe, h3])
  have q4 : SR L C 1 (pc + 1 + (liT 6 W).length + 1, s3) := SR.one (by simp [Safe, h4])
  have q5 := li_sr (K := L) (d := 7) (v := K) s3 (by decide) (by decide) z3 p4
  have q6 : SR L C 3 (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length, s5) := by
    intro j hj c hc
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · simp [run] at hc; subst hc; simp only [Safe, h6, eT0]; exact ⟨by decide, by decide, by decide, by decide, by omega, w0⟩
    · simp [run, step, h6, eT0] at hc; subst hc; simp only [Safe, h7, eT8]; exact ⟨by decide, by decide, by decide, by decide, by omega, w1⟩
    · simp [run, step, h6, h7, eT0, eT8] at hc; subst hc
      simp only [Safe, h8, b6]
      refine ⟨by decide, by decide, by decide, by decide, by omega, ?_⟩
      rw [hsum]; omega
  have q9 := push_sr (K := L) (s := s8) (by simpa [pushA] using p6) (by decide) hh8 (by rw [y31]; exact w2)
  exact q1.add r1 (q2.add r2 (q3.add r3 (q4.add r4' (q5.add r5 (q6.add r678 q9)))))

end SafeRun
