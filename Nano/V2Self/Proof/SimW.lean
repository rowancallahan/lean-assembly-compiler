/- Bridge part 2 (Astra-11): the abstract machine of the codegen templates (`CallProbe.J`, Nano/V2Self/Proof/Call.lean)
against the Sail model.  `RelW`: J state ↔ Sail state, code = a list of 32-bit words at `base` (C's output), x0 = 0,
the work block's 8-aligned cells as 8 LE bytes.  One J step on a word that is the matching encoding = one retired
Sail instruction, keeping `RelW`.  Immediates are in range and address arithmetic does not wrap (side conditions the
template proofs discharge). -/
import Nano.V2.Sim
import Nano.V2Self.Proof.Call

namespace SimW
open Proven Nano.V2B

structure LayW where
  base : Nat
  W : List Nat
  lo : Nat
  hi : Nat

structure LayW.Ok (K : LayW) : Prop where
  b4 : K.base % 4 = 0
  blo : 0x80000000 ≤ K.base
  bhi : K.base + 4 * K.W.length + 4 ≤ 0x100000000
  wlo : 0x80000000 ≤ K.lo
  whi : K.hi ≤ 0x100000000
  cw : K.base + 4 * K.W.length ≤ K.lo ∨ K.hi ≤ K.base

def wok (K : LayW) (a : Nat) : Prop := K.lo ≤ a ∧ a + 8 ≤ K.hi ∧ a % 8 = 0

structure RelW (K : LayW) (p : Nat × CallProbe.St) (t : Proven.St) : Prop where
  cfg : Proven.Cfg t
  pc : t.regs.get? .PC = some (BitVec.ofNat 64 (K.base + 4 * p.1))
  code : ∀ i (h : i < K.W.length), instrAt t (BitVec.ofNat 64 (K.base + 4 * i)) (BitVec.ofNat 32 K.W[i])
  x0 : p.2.x 0 = 0
  x : ∀ j : Fin 32, getX t j = (p.2.x j.val).toBitVec
  w : ∀ a, wok K a → ∀ k < 8, t.mem[a + k]? = some ((p.2.m a).toBitVec.extractLsb' (8 * k) 8)

theorem pcOKW {K : LayW} (hK : K.Ok) {pc : Nat} (h : pc < K.W.length) : pcOK (BitVec.ofNat 64 (K.base + 4 * pc)) := by
  have := hK.bhi; have := hK.blo; have := hK.b4
  have hlt : K.base + 4 * pc < 2 ^ 64 := by omega
  simp only [pcOK, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; omega

theorem codeW {K : LayW} {p : Nat × CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K p t) {w : Nat}
    (hC : K.W[p.1]? = some w) :
    instrAt t (BitVec.ofNat 64 (K.base + 4 * p.1)) (BitVec.ofNat 32 w) ∧ pcOK (BitVec.ofNat 64 (K.base + 4 * p.1)) := by
  obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 hC
  exact ⟨h2 ▸ hR.code _ h1, pcOKW hK h1⟩

/-- a retired instruction that writes `rd` (J's `wr`) and steps the pc -/
theorem rel_regW {K : LayW} {pc : Nat} {s : CallProbe.St} {t t' : Proven.St} (hR : RelW K (pc, s) t) (rd : Fin 32)
    (v : UInt64) (hN : Next t t' (BitVec.ofNat 64 (K.base + 4 * pc) + 4) rd v.toBitVec t.mem) :
    RelW K (pc + 1, CallProbe.wr s rd.val v) t' where
  cfg := hN.cfg
  pc := by rw [hN.pc, ofNat_pc4]
  code := fun i h => by have := hR.code i h; unfold instrAt at this ⊢; rw [hN.mem]; exact this
  x0 := by
    unfold CallProbe.wr; split
    · exact hR.x0
    · rename_i h; have : (0 : Nat) ≠ rd.val := fun e => h e.symm
      simp [CallProbe.upd, this]; exact hR.x0
  x := fun j => by
    rw [hN.x j]
    by_cases hj : j = rd
    · subst hj
      by_cases h0 : j = 0
      · subst h0; simp [CallProbe.wr]; have := hR.x 0; simpa using this
      · have : j.val ≠ 0 := fun e => h0 (Fin.ext e)
        simp [h0, CallProbe.wr, this, CallProbe.upd]
    · have : j.val ≠ rd.val := fun e => hj (Fin.ext e)
      simp only [hj, false_and, if_false]; rw [hR.x j]; unfold CallProbe.wr; split <;> simp [CallProbe.upd, this]
  w := fun a ha k hk => by
    rw [hN.mem]; have := hR.w a ha k hk; unfold CallProbe.wr; split <;> simpa using this

/-- J's addi value is the hardware's when the sum does not wrap -/
theorem addi_val (b : UInt64) (imm : Int) (h0 : 0 ≤ (b.toNat : Int) + imm) (h1 : (b.toNat : Int) + imm < 2 ^ 64) :
    UInt64.ofNat (CallProbe.ea b imm) = b + UInt64.ofInt imm := by
  apply UInt64.toBitVec_inj.mp
  rw [UInt64.toBitVec_add, ofInt_bv]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofInt]
  simp [CallProbe.ea]
  omega

/-- **addi** -/
theorem sim_addi {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {rd a : Nat} {imm : Int} (hC : K.W[pc]? = some (I.i .addi rd a imm).enc) (hrd : rd < 32) (ha : a < 32)
    (hi1 : -2048 ≤ imm) (hi2 : imm < 2048)
    (h0 : 0 ≤ ((s.x a).toNat : Int) + imm) (h1 : ((s.x a).toNat : Int) + imm < 2 ^ 64) :
    ∃ t', Retires t t' ∧ RelW K (pc + 1, CallProbe.wr s rd (UInt64.ofNat (CallProbe.ea (s.x a) imm))) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let RD : Fin 32 := ⟨rd, hrd⟩
  let A : Fin 32 := ⟨a, ha⟩
  have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (Proven.encI 0 (BitVec.ofNat 12 (bits imm 12)).toNat RD A) := by
    rw [imm12_toNat]; exact hi
  obtain ⟨t', hN⟩ := G.step_addi hR.cfg hR.pc hok RD A _ hi'
  have hv : getX t A + (BitVec.ofNat 12 (bits imm 12)).signExtend 64 = (UInt64.ofNat (CallProbe.ea (s.x a) imm)).toBitVec := by
    rw [hR.x A, sext_bits imm hi1 hi2, addi_val _ _ h0 h1, UInt64.toBitVec_add]
  rw [hv] at hN
  exact ⟨t', hN.ret, rel_regW hR RD _ hN⟩

end SimW
