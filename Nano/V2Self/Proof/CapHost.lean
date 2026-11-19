/- Opus box E: the capacity stub on Sail.  `sim_addiN`: addi with the hardware's (wrapping) sum; `stub_sail`: from
the cap stub (word 6) with ra / s0 saved at a2, five Sail steps return to ra with a0 = −2, a1 = 0, s0 restored. -/
import Nano.V2Self.Proof.HostMain
namespace SimW
open Proven Nano.V2B

/-- **addi**, any sum: the J register gets the hardware's value `x[a] + imm` -/
theorem sim_addiN {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {rd a : Nat} {imm : Int} (hC : K.W[pc]? = some (I.i .addi rd a imm).enc) (hrd : rd < 32) (ha : a < 32)
    (hi1 : -2048 ≤ imm) (hi2 : imm < 2048) :
    ∃ t', Retires t t' ∧ RelW K (pc + 1, CallProbe.wr s rd (s.x a + UInt64.ofInt imm)) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let RD : Fin 32 := ⟨rd, hrd⟩
  let A : Fin 32 := ⟨a, ha⟩
  have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (Proven.encI 0 (BitVec.ofNat 12 (bits imm 12)).toNat RD A) := by
    rw [imm12_toNat]; exact hi
  obtain ⟨t', hN⟩ := G.step_addi hR.cfg hR.pc hok RD A _ hi'
  have hv : getX t A + (BitVec.ofNat 12 (bits imm 12)).signExtend 64 = (s.x a + UInt64.ofInt imm).toBitVec := by
    rw [hR.x A, sext_bits imm hi1 hi2, UInt64.toBitVec_add, ofInt_bv]
  rw [hv] at hN
  exact ⟨t', hN.ret, rel_regW hR RD _ hN⟩

theorem steps_one {a b : Proven.St} (h : Retires a b) : Steps 1 a b := ⟨b, h, rfl⟩

/-- **the cap stub on Sail** -/
theorem stub_sail {K : LayW} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (6, s) t)
    (hW6 : K.W[6]? = some (I.i .addi 10 0 (-2)).enc) (hW7 : K.W[7]? = some (I.i .addi 11 0 0).enc)
    (hW8 : K.W[8]? = some (I.ld 1 12 0).enc) (hW9 : K.W[9]? = some (I.ld 8 12 8).enc)
    (hW10 : K.W[10]? = some (C.g2 C.g_103 0 0 (UInt64.ofNat 1) 0).toNat)
    (hz : s.x 0 = 0) (w0 : wok K (s.x 12).toNat) (w8 : wok K ((s.x 12).toNat + 8))
    (hra : (s.m (s.x 12).toNat).toNat % 2 = 0) :
    ∃ n t', Steps n t t' ∧ t'.regs.get? .PC = some (s.m (s.x 12).toNat).toBitVec ∧ Cfg t' ∧
      getX t' 10 = (UInt64.ofInt (-2)).toBitVec ∧ getX t' 11 = 0 ∧ getX t' 8 = (s.m ((s.x 12).toNat + 8)).toBitVec ∧
      (∀ j : Fin 32, j.val ≠ 1 → j.val ≠ 8 → j.val ≠ 10 → j.val ≠ 11 → getX t' j = (s.x j.val).toBitVec) ∧
      (∀ a, ¬ wok K (a - a % 8) → ¬ outB K a → t'.mem[a]? = K.m0 a) := by
  have wx : ∀ (u : CallProbe.St) (r j : Nat) (v : UInt64), j ≠ r → (CallProbe.wr u r v).x j = u.x j := by
    intro u r j v h; unfold CallProbe.wr; split
    · rfl
    · simp [CallProbe.upd, h]
  have wxs : ∀ (u : CallProbe.St) (r : Nat) (v : UInt64), r ≠ 0 → (CallProbe.wr u r v).x r = v := by
    intro u r v h; simp [CallProbe.wr, h, CallProbe.upd]
  have wm : ∀ (u : CallProbe.St) (r : Nat) (v : UInt64), (CallProbe.wr u r v).m = u.m := by
    intro u r v; unfold CallProbe.wr; split <;> rfl
  have lt12 := (s.x 12).toNat_lt
  have h8 : (s.x 12).toNat + 8 < 2 ^ 64 := by unfold wok at w8; have := hK.whi; omega
  obtain ⟨t1, r1, R1⟩ := sim_addiN hK hR hW6 (by decide) (by decide) (by decide) (by decide)
  generalize hs1 : CallProbe.wr s 10 (s.x 0 + UInt64.ofInt (-2)) = s1 at R1
  have a1 : s1.x 12 = s.x 12 := by rw [← hs1, wx _ _ _ _ (by decide)]
  have m1 : s1.m = s.m := by rw [← hs1, wm]
  have z1 : s1.x 0 = 0 := by rw [← hs1, wx _ _ _ _ (by decide), hz]
  obtain ⟨t2, r2, R2⟩ := sim_addiN hK R1 hW7 (by decide) (by decide) (by decide) (by decide)
  generalize hs2 : CallProbe.wr s1 11 (s1.x 0 + UInt64.ofInt 0) = s2 at R2
  have a2 : s2.x 12 = s.x 12 := by rw [← hs2, wx _ _ _ _ (by decide), a1]
  have m2 : s2.m = s.m := by rw [← hs2, wm, m1]
  have e0 : CallProbe.ea (s2.x 12) 0 = (s.x 12).toNat := by rw [a2]; simp [CallProbe.ea]
  obtain ⟨t3, r3, R3⟩ := sim_ld hK R2 hW8 (by decide) (by decide) (by decide) (by decide)
    (by rw [a2]; omega) (by rw [e0]; exact w0)
  generalize hs3 : CallProbe.wr s2 1 (s2.m (CallProbe.ea (s2.x 12) 0)) = s3 at R3
  have a3 : s3.x 12 = s.x 12 := by rw [← hs3, wx _ _ _ _ (by decide), a2]
  have m3 : s3.m = s.m := by rw [← hs3, wm, m2]
  have e8 : CallProbe.ea (s3.x 12) 8 = (s.x 12).toNat + 8 := by rw [a3]; simp [CallProbe.ea]; omega
  obtain ⟨t4, r4, R4⟩ := sim_ld hK R3 hW9 (by decide) (by decide) (by decide) (by decide)
    (by rw [a3]; omega) (by rw [e8]; exact w8)
  generalize hs4 : CallProbe.wr s3 8 (s3.m (CallProbe.ea (s3.x 12) 8)) = s4 at R4
  have x1 : s4.x 1 = s.m (s.x 12).toNat := by
    rw [← hs4, wx _ _ _ _ (by decide), ← hs3, wxs _ _ _ (by decide), m2, e0]
  have x8 : s4.x 8 = s.m ((s.x 12).toNat + 8) := by rw [← hs4, wxs _ _ _ (by decide), m3, e8]
  have x10 : s4.x 10 = UInt64.ofInt (-2) := by
    rw [← hs4, wx _ _ _ _ (by decide), ← hs3, wx _ _ _ _ (by decide), ← hs2, wx _ _ _ _ (by decide), ← hs1,
      wxs _ _ _ (by decide), hz]; rfl
  have x11 : s4.x 11 = 0 := by
    rw [← hs4, wx _ _ _ _ (by decide), ← hs3, wx _ _ _ _ (by decide), ← hs2, wxs _ _ _ (by decide), z1]; rfl
  have xo : ∀ j, j ≠ 1 → j ≠ 8 → j ≠ 10 → j ≠ 11 → s4.x j = s.x j := by
    intro j j1 j8 j10 j11
    rw [← hs4, wx _ _ _ _ j8, ← hs3, wx _ _ _ _ j1, ← hs2, wx _ _ _ _ j11, ← hs1, wx _ _ _ _ j10]
  obtain ⟨t5, v, hN⟩ := sim_ret hK R4 (by decide) hW10 (by rw [x1]; exact hra)
  have gx : ∀ j : Fin 32, getX t5 j = (s4.x j.val).toBitVec := fun j => by
    rw [hN.x j]; simp only [show ¬ (j = 0 ∧ j ≠ 0) from fun h => h.2 h.1, if_false]; exact R4.x j
  refine ⟨5, t5, ⟨t1, r1, t2, r2, t3, r3, t4, r4, steps_one hN.ret⟩, by rw [hN.pc, x1], hN.cfg,
    by rw [gx 10]; show (s4.x 10).toBitVec = _; rw [x10], by rw [gx 11]; show (s4.x 11).toBitVec = _; rw [x11]; rfl,
    by rw [gx 8]; show (s4.x 8).toBitVec = _; rw [x8], fun j j1 j8 j10 j11 => by
      rw [gx j, xo j j1 j8 j10 j11], fun a h1 h2 => by rw [hN.mem]; exact R4.fr a h1 h2⟩

end SimW
