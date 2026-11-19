/- Heap prims on the abstract machine J: BNEW (g32 p = 5) — the buffer header write and the bump of t5 — with its
capacity exit.  A buffer is [len][cap][κ words]; BNEW returns its address (the old t5). -/
import Nano.V2Self.Proof.Expr
namespace CallProbe

/-- BNEW with cap κ: t0 := t5; t1 := t0 + 8(κ+2); if t6 < t1 → stub; len := 0; cap := κ; t5 := t1; push t0 (checked against the NEW t5) -/
def bnewT (tgt q κ : Nat) : List J :=
  let W : UInt64 := UInt64.ofNat ((κ + 2) * 8)
  let L := (liT 6 W).length
  let L' := (liT 7 (UInt64.ofNat κ)).length
  [.addi 5 30 0] ++ (liT 6 W ++ ([.alu 1 6 6 30, .bgeu 31 6 2, .jal 0 ((tgt : Int) - ((q + 1 + L + 2 : Nat) : Int))] ++
    (liT 7 (UInt64.ofNat κ) ++ ([.sd 0 5 0, .sd 7 5 8, .addi 30 6 0] ++ pushA tgt (q + 1 + L + 3 + L' + 3) 5))))

theorem pushA_len' (tgt q r : Nat) : (pushA tgt q r).length = 4 := rfl

theorem bnewT_len (tgt q κ : Nat) : (bnewT tgt q κ).length =
    1 + (liT 6 (UInt64.ofNat ((κ + 2) * 8))).length + 3 + (liT 7 (UInt64.ofNat κ)).length + 3 + 4 := by
  unfold bnewT
  simp only [List.length_append, pushA_len', List.length_cons, List.length_nil]
  omega

/-- BNEW with its exact step count -/
theorem bnew_runK {C : List J} {pc tgt κ : Nat} (s : St) (hC : At C pc (bnewT tgt pc κ)) (hx0 : s.x 0 = 0)
    (hκ : κ < 2 ^ 40) (hsp : (s.x 31).toNat < 2 ^ 62)
    (hroom : (s.x 30).toNat + 8 * (κ + 2) + 8 ≤ (s.x 31).toNat) :
    ∃ s', run C (1 + ((liT 6 (UInt64.ofNat ((κ + 2) * 8))).length + (1 + (1 + ((liT 7 (UInt64.ofNat κ)).length + (3 + 3)))))) (pc, s)
      = some (pc + (bnewT tgt pc κ).length, s') ∧
      (s'.x 31).toNat = (s.x 31).toNat - 8 ∧ (s'.x 30).toNat = (s.x 30).toNat + 8 * (κ + 2) ∧ s'.x 5 = s.x 30 ∧
      s'.m = upd (upd (upd s.m (s.x 30).toNat 0) ((s.x 30).toNat + 8) (UInt64.ofNat κ)) ((s.x 31).toNat - 8) (s.x 30) ∧
      s'.b = s.b ∧ (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 30 → r ≠ 31 → s'.x r = s.x r) := by
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
  refine ⟨⟨upd s8.x 31 (UInt64.ofNat ((s8.x 31).toNat - 8)), upd s8.m ((s8.x 31).toNat - 8) (s8.x 5), s8.b⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_add r1, run_add r2, run_add r3, run_add r4', run_add r5, run_add r678, r9]
    have : (bnewT tgt pc κ).length = 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3 + 4 := by
      rw [bnewT_len, hW, hK]
    rw [this]; congr 2; omega
  · simp only [upd_same, UInt64.toNat_ofNat', y31]; omega
  · dsimp only
    rw [upd_ne _ _ (by decide : (30:Nat) ≠ 31), y30, hsum]; omega
  · dsimp only
    rw [upd_ne _ _ (by decide : (5:Nat) ≠ 31), y5]
  · dsimp only
    rw [y31, y5]; simp only [s8]; rw [mm5]
  · dsimp only
    simp [s8, hb5, s3, hb2, s1]
  · intro r h5 h6 h7 h30 h31
    dsimp only
    rw [upd_ne _ _ h31]; simp [s8, upd_ne, h30, hx5, s3, h5, h6, h7, hx2, s1]


/-- BNEW at the capacity exit: not enough room for the buffer plus the pushed address.  Control reaches the stub `tgt`;
s0, x0 and every stack cell at or above the entry t6 are untouched (the header writes are below it). -/
theorem bnew_run {C : List J} {pc tgt κ : Nat} (s : St) (hC : At C pc (bnewT tgt pc κ)) (hx0 : s.x 0 = 0)
    (hκ : κ < 2 ^ 40) (hsp : (s.x 31).toNat < 2 ^ 62)
    (hroom : (s.x 30).toNat + 8 * (κ + 2) + 8 ≤ (s.x 31).toNat) :
    ∃ k s', run C k (pc, s) = some (pc + (bnewT tgt pc κ).length, s') ∧
      (s'.x 31).toNat = (s.x 31).toNat - 8 ∧ (s'.x 30).toNat = (s.x 30).toNat + 8 * (κ + 2) ∧ s'.x 5 = s.x 30 ∧
      s'.m = upd (upd (upd s.m (s.x 30).toNat 0) ((s.x 30).toNat + 8) (UInt64.ofNat κ)) ((s.x 31).toNat - 8) (s.x 30) ∧
      s'.b = s.b ∧ (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 30 → r ≠ 31 → s'.x r = s.x r) := by
  obtain ⟨s', h, r⟩ := bnew_runK s hC hx0 hκ hsp hroom
  exact ⟨_, s', h, r⟩

theorem bnew_oom {C : List J} {pc tgt κ : Nat} (s : St) (hC : At C pc (bnewT tgt pc κ)) (hx0 : s.x 0 = 0)
    (hκ : κ < 2 ^ 40) (hsp : (s.x 31).toNat < 2 ^ 62) (hT : (s.x 30).toNat < 2 ^ 62) (h8 : 8 ≤ (s.x 31).toNat)
    (hroom : (s.x 31).toNat < (s.x 30).toNat + 8 * (κ + 2) + 8) :
    ∃ k s', run C k (pc, s) = some (tgt, s') ∧ s'.x 8 = s.x 8 ∧ s'.x 0 = 0 ∧ s'.x 28 = s.x 28 ∧ s'.x 29 = s.x 29 ∧
      (∀ a, (s.x 31).toNat ≤ a → s'.m a = s.m a) := by
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
  have h4 := p3.at 1 (by simp); simp at h4
  have hsum : (W + s.x 30).toNat = (κ + 2) * 8 + (s.x 30).toNat := by
    rw [UInt64.toNat_add, hWn]; simp; omega
  by_cases hb : (s.x 30).toNat + 8 * (κ + 2) ≤ (s.x 31).toNat
  · -- the buffer fits, the push does not
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
    have r4' : run C 1 (pc + 1 + (liT 6 W).length + 1, s3) = some (pc + 1 + (liT 6 W).length + 3, s3) := by simp [run, r4]
    have hlt8 : ¬ (s8.x 30).toNat + 8 ≤ (s8.x 31).toNat := by
      rw [y30, y31, hsum]; omega
    have r9 := push_oom (s := s8) (by simpa [pushA] using p6) (by rw [y31]; omega) (by rw [y30, y31, hsum]; omega)
    have r9' : run C 3 (pc + 1 + (liT 6 W).length + 3 + (liT 7 K).length + 3, s8) =
        some (tgt, ⟨upd s8.x 31 (UInt64.ofNat ((s8.x 31).toNat - 8)), s8.m, s8.b⟩) := by
      rw [r9]; congr 2; omega
    have fr : ∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 30 → r ≠ 31 → s8.x r = s.x r := by
      intro r h5 h6 h7 h30 h31
      simp [s8, upd_ne, h30, hx5, s3, h5, h6, h7, hx2, s1]
    refine ⟨1 + ((liT 6 W).length + (1 + (1 + ((liT 7 K).length + (3 + 3))))), ⟨upd s8.x 31 (UInt64.ofNat ((s8.x 31).toNat - 8)), s8.m, s8.b⟩,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [run_add r1, run_add r2, run_add r3, run_add r4', run_add r5, run_add r678, r9']
    · dsimp only; rw [upd_ne _ _ (by decide : (8:Nat) ≠ 31), fr 8 (by decide) (by decide) (by decide) (by decide) (by decide)]
    · dsimp only; rw [upd_ne _ _ (by decide : (0:Nat) ≠ 31), fr 0 (by decide) (by decide) (by decide) (by decide) (by decide), hx0]
    · dsimp only; rw [upd_ne _ _ (by decide : (28:Nat) ≠ 31), fr 28 (by decide) (by decide) (by decide) (by decide) (by decide)]
    · dsimp only; rw [upd_ne _ _ (by decide : (29:Nat) ≠ 31), fr 29 (by decide) (by decide) (by decide) (by decide) (by decide)]
    · intro a ha
      dsimp only
      simp only [s8]; rw [mm5]
      rw [upd_other _ _ (by omega), upd_other _ _ (by omega)]
  · -- the buffer does not fit: bgeu falls through into the jal
    have hc : ¬ (s3.x 6).toNat ≤ (s3.x 31).toNat := by
      simp [s3, upd_same, upd_ne, a31, hsum]; omega
    have h5j := p3.at 2 (by simp); simp at h5j
    have rn : run C 2 (pc + 1 + (liT 6 W).length + 1, s3) = some (tgt, s3) := by
      have hb4 : step C (pc + 1 + (liT 6 W).length + 1, s3) = some (pc + 1 + (liT 6 W).length + 1 + 1, s3) := s_bgeu_f h4 (by simpa using hc)
      have hj : step C (pc + 1 + (liT 6 W).length + 1 + 1, s3) = some (tgt, s3) := by
        rw [s_jal (by simpa [Nat.add_assoc] using h5j)]
        simp [wr]; omega
      simp [run, hb4, hj]
    have fr3 : ∀ r, r ≠ 5 → r ≠ 6 → s3.x r = s.x r := by
      intro r h5 h6; simp [s3, upd_ne, h6, hx2, s1, h5]
    refine ⟨1 + ((liT 6 W).length + (1 + 2)), s3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [run_add r1, run_add r2, run_add r3, rn]
    · rw [fr3 8 (by decide) (by decide)]
    · rw [fr3 0 (by decide) (by decide), hx0]
    · rw [fr3 28 (by decide) (by decide)]
    · rw [fr3 29 (by decide) (by decide)]
    · intro a ha; simp [s3, mm2]

/-! ## BPUSH (g32 else; PUT is the same code): pops v and the buffer, appends v, leaves the buffer on top -/
def bpushT (tgt q : Nat) : List J :=
  [.ld 6 31 0, .ld 5 31 8, .addi 31 31 8, .ld 7 5 0, .ld 14 5 8, .bltu 7 14 2, .jal 0 ((tgt : Int) - ((q + 6 : Nat) : Int)),
   .slli 15 7 3, .alu 1 15 15 5, .sd 6 15 16, .addi 7 7 1, .sd 7 5 0]

/-- BPUSH with its exact step count -/
theorem bpush_runK {C : List J} {pc tgt : Nat} (s : St) (hC : At C pc (bpushT tgt pc)) (hx0 : s.x 0 = 0)
    (hsp : (s.x 31).toNat + 16 < 2 ^ 63)
    (hlen : (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat < (s.m ((s.m ((s.x 31).toNat + 8)).toNat + 8)).toNat)
    (hb : (s.m ((s.x 31).toNat + 8)).toNat + 16 + 8 * (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat < 2 ^ 62) :
    ∃ s', run C 11 (pc, s) = some (pc + 12, s') ∧
      s'.m = upd (upd s.m ((s.m ((s.x 31).toNat + 8)).toNat + 16 + 8 * (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat)
                  (s.m (s.x 31).toNat))
              (s.m ((s.x 31).toNat + 8)).toNat ((s.m (s.m ((s.x 31).toNat + 8)).toNat) + 1) ∧
      (s'.x 31).toNat = (s.x 31).toNat + 8 ∧ s'.b = s.b ∧
      (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 15 → r ≠ 31 → s'.x r = s.x r) := by
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
  simp [run, step, h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, wr, e0, e8, eb0, ebuf8, t8, eL, hx0, aluf, ea16,
    upd_same, upd_upd, upd_ne, hlt', show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 2).toNat = pc + 7 by omega]
  intro r h5 h6 h7 h14 h15 h31
  simp [upd, h5, h6, h7, h14, h15, h31]

/-- BPUSH on a full buffer: the capacity exit (word `tgt`); memory is untouched -/
theorem bpush_run {C : List J} {pc tgt : Nat} (s : St) (hC : At C pc (bpushT tgt pc)) (hx0 : s.x 0 = 0)
    (hsp : (s.x 31).toNat + 16 < 2 ^ 63)
    (hlen : (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat < (s.m ((s.m ((s.x 31).toNat + 8)).toNat + 8)).toNat)
    (hb : (s.m ((s.x 31).toNat + 8)).toNat + 16 + 8 * (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat < 2 ^ 62) :
    ∃ k s', run C k (pc, s) = some (pc + 12, s') ∧
      s'.m = upd (upd s.m ((s.m ((s.x 31).toNat + 8)).toNat + 16 + 8 * (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat)
                  (s.m (s.x 31).toNat))
              (s.m ((s.x 31).toNat + 8)).toNat ((s.m (s.m ((s.x 31).toNat + 8)).toNat) + 1) ∧
      (s'.x 31).toNat = (s.x 31).toNat + 8 ∧ s'.b = s.b ∧
      (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 15 → r ≠ 31 → s'.x r = s.x r) := by
  obtain ⟨s', h, r⟩ := bpush_runK s hC hx0 hsp hlen hb
  exact ⟨_, s', h, r⟩

theorem bpush_cap {C : List J} {pc tgt : Nat} (s : St) (hC : At C pc (bpushT tgt pc)) (hx0 : s.x 0 = 0)
    (hsp : (s.x 31).toNat + 16 < 2 ^ 62)
    (hlen : (s.m ((s.m ((s.x 31).toNat + 8)).toNat + 8)).toNat ≤ (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat)
    (hb : (s.m ((s.x 31).toNat + 8)).toNat + 16 < 2 ^ 62) :
    ∃ k s', run C k (pc, s) = some (tgt, s') ∧ s'.m = s.m ∧ s'.x 8 = s.x 8 ∧ s'.x 0 = 0 ∧ s'.x 28 = s.x 28 ∧ s'.x 29 = s.x 29 := by
  have hs : ∀ i, i < 12 → C[pc + i]? = (bpushT tgt pc)[i]? := fun i hi => hC i (by simp [bpushT]; omega)
  have h0 := hs 0 (by omega); have h1 := hs 1 (by omega); have h2 := hs 2 (by omega); have h3 := hs 3 (by omega)
  have h4 := hs 4 (by omega); have h5 := hs 5 (by omega); have h6 := hs 6 (by omega)
  simp [bpushT] at h0 h1 h2 h3 h4 h5 h6
  have lt := (s.x 31).toNat_lt
  have e0 : ea (s.x 31) 0 = (s.x 31).toNat := by simp [ea]
  have e8 : ea (s.x 31) 8 = (s.x 31).toNat + 8 := by simp [ea]; omega
  have eb0 : ∀ b : UInt64, ea b 0 = b.toNat := fun b => by simp [ea]
  have blt := (s.m ((s.x 31).toNat + 8)).toNat_lt
  have ebuf8 : ea (s.m ((s.x 31).toNat + 8)) 8 = (s.m ((s.x 31).toNat + 8)).toNat + 8 := by simp [ea]; omega
  have hc : ¬ (s.m (s.m ((s.x 31).toNat + 8)).toNat).toNat < (s.m ((s.m ((s.x 31).toNat + 8)).toNat + 8)).toNat := by omega
  refine ⟨7, ?_⟩
  simp [run, step, h0, h1, h2, h3, h4, h5, h6, wr, e0, e8, eb0, ebuf8, hc, upd_ne, upd_same,
    show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 1 + (tgt - (pc + 6 : Nat))).toNat = tgt by omega]
  refine ⟨_, ⟨by omega, rfl⟩, ?_⟩
  simp [upd_ne, hx0]

/-! ## BSET (g32 p = 8): pops v, i, buf; stores v at word i if i < len; the buffer stays on top -/
def bsetT : List J :=
  [.ld 14 31 0, .ld 6 31 8, .ld 5 31 16, .addi 31 31 16, .ld 7 5 0, .bgeu 6 7 4, .slli 6 6 3, .alu 1 6 5 6, .sd 14 6 16]

/-- BSET with its exact step count (9 in range, 6 out of range) -/
theorem bset_runK {C : List J} {pc : Nat} (s : St) (hC : At C pc bsetT) (hx0 : s.x 0 = 0)
    (hsp : (s.x 31).toNat + 24 < 2 ^ 62)
    (hb : (s.m (s.m ((s.x 31).toNat + 16)).toNat).toNat > (s.m ((s.x 31).toNat + 8)).toNat →
      (s.m ((s.x 31).toNat + 16)).toNat + 16 + 8 * (s.m ((s.x 31).toNat + 8)).toNat < 2 ^ 62) :
    ∃ s', run C (if (s.m ((s.x 31).toNat + 8)).toNat < (s.m (s.m ((s.x 31).toNat + 16)).toNat).toNat then 9 else 6) (pc, s)
      = some (pc + 9, s') ∧
      s'.m = (if (s.m ((s.x 31).toNat + 8)).toNat < (s.m (s.m ((s.x 31).toNat + 16)).toNat).toNat
              then upd s.m ((s.m ((s.x 31).toNat + 16)).toNat + 16 + 8 * (s.m ((s.x 31).toNat + 8)).toNat) (s.m (s.x 31).toNat)
              else s.m) ∧
      (s'.x 31).toNat = (s.x 31).toNat + 16 ∧ s'.b = s.b ∧
      (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 31 → s'.x r = s.x r) := by
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
    have sh : ((s.m ((s.x 31).toNat + 8)) <<< 3).toNat = 8 * (s.m ((s.x 31).toNat + 8)).toNat := by
      have := (s.m ((s.x 31).toNat + 8)).toNat_lt
      simp [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have sa : ((s.m ((s.x 31).toNat + 16)) + (s.m ((s.x 31).toNat + 8)) <<< 3).toNat
        = (s.m ((s.x 31).toNat + 16)).toNat + 8 * (s.m ((s.x 31).toNat + 8)).toNat := by
      rw [UInt64.toNat_add, sh]; simp; omega
    have ea16 : ea ((s.m ((s.x 31).toNat + 16)) + (s.m ((s.x 31).toNat + 8)) <<< 3) 16
        = (s.m ((s.x 31).toNat + 16)).toNat + 16 + 8 * (s.m ((s.x 31).toNat + 8)).toNat := by
      simp only [ea, sa]; omega
    simp only [if_pos hi]
    have hc : ¬ (s.m (s.m ((s.x 31).toNat + 16)).toNat).toNat ≤ (s.m ((s.x 31).toNat + 8)).toNat := by omega
    simp [run, step, h0, h1, h2, h3, h4, h5, h6, h7, h8, wr, e0, e8, e16, t16, eb0, aluf, ea16, hc, hi, upd_ne, upd_same]
    intro r h5 h6 h7 h14 h31
    simp [upd, h5, h6, h7, h14, h31]
  · simp only [if_neg hi]
    have hc : (s.m (s.m ((s.x 31).toNat + 16)).toNat).toNat ≤ (s.m ((s.x 31).toNat + 8)).toNat := by omega
    simp [run, step, h0, h1, h2, h3, h4, h5, wr, e0, e8, e16, t16, eb0, hc, hi, upd_ne, upd_same,
      show ((pc : Int) + 1 + 1 + 1 + 1 + 1 + 4).toNat = pc + 9 by omega]
    intro r h5 h6 h7 h14 h31
    simp [upd, h5, h6, h7, h14, h31]


theorem bset_run {C : List J} {pc : Nat} (s : St) (hC : At C pc bsetT) (hx0 : s.x 0 = 0)
    (hsp : (s.x 31).toNat + 24 < 2 ^ 62)
    (hb : (s.m (s.m ((s.x 31).toNat + 16)).toNat).toNat > (s.m ((s.x 31).toNat + 8)).toNat →
      (s.m ((s.x 31).toNat + 16)).toNat + 16 + 8 * (s.m ((s.x 31).toNat + 8)).toNat < 2 ^ 62) :
    ∃ k s', run C k (pc, s) = some (pc + 9, s') ∧
      s'.m = (if (s.m ((s.x 31).toNat + 8)).toNat < (s.m (s.m ((s.x 31).toNat + 16)).toNat).toNat
              then upd s.m ((s.m ((s.x 31).toNat + 16)).toNat + 16 + 8 * (s.m ((s.x 31).toNat + 8)).toNat) (s.m (s.x 31).toNat)
              else s.m) ∧
      (s'.x 31).toNat = (s.x 31).toNat + 16 ∧ s'.b = s.b ∧
      (∀ r, r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 14 → r ≠ 31 → s'.x r = s.x r) := by
  obtain ⟨s', h, r⟩ := bset_runK s hC hx0 hsp hb
  exact ⟨_, s', h, r⟩

end CallProbe
