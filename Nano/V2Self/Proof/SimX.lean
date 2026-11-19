/- Machine bridge (Opus box E): Sail sims of the start code's extra instructions (srli, beq +28, bne +16, sb), in the
form of SimW's sims (a J step on a matching word is one retired Sail instruction keeping `RelW`).  Wiring them into
`SimW.Safe` / `encJ` / `sim_stepW` is a shared edit (A's Safe retrofit), proposed separately. -/
import Nano.V2Self.Proof.SimW
namespace SimW
open Proven Nano.V2B

/-- **srli rd, a, sh** -/
theorem sim_srliW {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {rd a sh : Nat} (hC : K.W[pc]? = some (I.i .srli rd a (sh : Int)).enc) (hrd : rd < 32) (ha : a < 32) (hsh : sh < 64) :
    ∃ t', Retires t t' ∧ RelW K (pc + 1, CallProbe.wr s rd (s.x a >>> sh.toUInt64)) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let RD : Fin 32 := ⟨rd, hrd⟩
  let A : Fin 32 := ⟨a, ha⟩
  have xa : getX t A = (s.x a).toBitVec := hR.x A
  have hn : (sh : Int).toNat < 64 := by simpa using hsh
  have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (Proven.encI 5 (0 <<< 6 ||| (BitVec.ofNat 6 (sh : Int).toNat).toNat) RD A) := by
    rw [show 0 <<< 6 ||| (BitVec.ofNat 6 (sh : Int).toNat).toNat = bits (sh : Int) 12 by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; unfold bits; simp; omega]; exact hi
  obtain ⟨t', hN⟩ := G.step_srli hR.cfg hR.pc hok RD A _ hi'
  rw [xa, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, ← shrK_bv _ _ hn] at hN
  exact ⟨t', hN.ret, by simpa using rel_regW hR RD _ hN⟩

set_option maxRecDepth 100000 in
theorem encBt28_eq (f3 : Nat) (hf : f3 < 8) (rs1 rs2 : Fin 32) :
    BitVec.ofNat 32 (encBt f3 rs1.val rs2.val 28) = wB (BitVec.ofNat 3 f3) (.ofFin rs1) (.ofFin rs2) 14#12 := by
  unfold encBt; rw [show bits (28 : Int) 13 = 28 from rfl]; encbits

theorem boff28 : boff (14#12) = 28#64 := by decide
theorem pc_plus28 (b pc : Nat) : BitVec.ofNat 64 (b + 4 * pc) + 28#64 = BitVec.ofNat 64 (b + 4 * (pc + 7)) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

/-- **beq a, b, +28** (the start code's copy-loop exit) -/
theorem sim_beq28 {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {a b : Nat} (hC : K.W[pc]? = some (I.br .beq a b 28).enc) (ha : a < 32) (hb : b < 32) :
    ∃ t', Retires t t' ∧ RelW K (if s.x a = s.x b then ((pc : Int) + 7).toNat else pc + 1, s) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let A : Fin 32 := ⟨a, ha⟩
  let B : Fin 32 := ⟨b, hb⟩
  have xa : getX t A = (s.x a).toBitVec := hR.x A
  have xb : getX t B = (s.x b).toBitVec := hR.x B
  have e := encBt28_eq 0 (by decide) A B
  have hi2 : instrAt t _ (BitVec.ofNat 32 (encBt 0 A.val B.val 28)) := hi
  rw [e] at hi2
  have w0 : CallProbe.wr s (0 : Fin 32).val (0 : UInt64) = s := by simp [CallProbe.wr]
  by_cases hc : s.x a = s.x b
  · obtain ⟨t', hN⟩ := G.beq_t hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb, hc])
    rw [boff28, pc_plus28] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0] at this
    rw [if_pos hc, show ((pc : Int) + 7).toNat = pc + 7 by omega]; exact ⟨t', hN.ret, this⟩
  · obtain ⟨t', hN⟩ := G.beq_n hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact fun h => hc (UInt64.toBitVec_inj.1 h))
    rw [ofNat_pc4] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0] at this; rw [if_neg hc]; exact ⟨t', hN.ret, this⟩

/-- **bne a, b, +16** (the start code's empty-buffer check) -/
theorem sim_bne16 {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {a b : Nat} (hC : K.W[pc]? = some (I.br .bne a b 16).enc) (ha : a < 32) (hb : b < 32) :
    ∃ t', Retires t t' ∧ RelW K (if s.x a ≠ s.x b then ((pc : Int) + 4).toNat else pc + 1, s) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let A : Fin 32 := ⟨a, ha⟩
  let B : Fin 32 := ⟨b, hb⟩
  have xa : getX t A = (s.x a).toBitVec := hR.x A
  have xb : getX t B = (s.x b).toBitVec := hR.x B
  have e := encBt16_eq 1 (by decide) A B
  have hi2 : instrAt t _ (BitVec.ofNat 32 (encBt 1 A.val B.val 16)) := hi
  rw [e] at hi2
  have w0 : CallProbe.wr s (0 : Fin 32).val (0 : UInt64) = s := by simp [CallProbe.wr]
  by_cases hc : s.x a = s.x b
  · obtain ⟨t', hN⟩ := G.bne_n hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb, hc])
    rw [ofNat_pc4] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0] at this; rw [if_neg (by simpa using hc)]; exact ⟨t', hN.ret, this⟩
  · obtain ⟨t', hN⟩ := G.bne_t hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact fun h => hc (UInt64.toBitVec_inj.1 h))
    rw [boff16, pc_plus16] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0] at this
    rw [if_pos hc, show ((pc : Int) + 4).toNat = pc + 4 by omega]; exact ⟨t', hN.ret, this⟩

end SimW
