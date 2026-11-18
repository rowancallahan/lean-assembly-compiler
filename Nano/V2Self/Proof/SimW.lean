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

/-- the hardware effective address is J's `ea` when it does not wrap -/
theorem eaW {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hR : RelW K (pc, s) t) (A : Fin 32) (off : Int)
    (h1 : -2048 ≤ off) (h2 : off < 2048) (h0 : 0 ≤ ((s.x A.val).toNat : Int) + off)
    (hl : ((s.x A.val).toNat : Int) + off < 2 ^ 64) :
    getX t A + (BitVec.ofNat 12 (bits off 12)).signExtend 64 = BitVec.ofNat 64 (CallProbe.ea (s.x A.val) off) := by
  rw [hR.x A, sext_bits off h1 h2, ← UInt64.toBitVec_add, ← addi_val _ _ h0 hl]; rfl

/-- **ld** (the address is a work cell) -/
theorem sim_ld {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {rd a : Nat} {off : Int} (hC : K.W[pc]? = some (I.ld rd a off).enc) (hrd : rd < 32) (ha : a < 32)
    (hi1 : -2048 ≤ off) (hi2 : off < 2048) (h0 : 0 ≤ ((s.x a).toNat : Int) + off)
    (hw : wok K (CallProbe.ea (s.x a) off)) :
    ∃ t', Retires t t' ∧ RelW K (pc + 1, CallProbe.wr s rd (s.m (CallProbe.ea (s.x a) off))) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let RD : Fin 32 := ⟨rd, hrd⟩
  let A : Fin 32 := ⟨a, ha⟩
  have hW := hK.wlo; have hH := hK.whi
  have hlt : CallProbe.ea (s.x a) off < 2 ^ 64 := by unfold wok at hw; omega
  have hea := eaW hR A off hi1 hi2 h0 (by show ((s.x a).toNat : Int) + off < 2 ^ 64; unfold CallProbe.ea at hlt; omega)
  have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (G.encL 3 (BitVec.ofNat 12 (bits off 12)) RD A) := by
    unfold G.encL; rw [imm12_toNat]; exact hi
  have hb := fun k (hk : k < 8) => hR.w _ hw k hk
  obtain ⟨t', hN⟩ := G.step_ld hR.cfg hR.pc hok RD A _ hi' hea (by rw [toNat_lt64 hlt]; unfold wok at hw; omega)
    (by rw [toNat_lt64 hlt]; exact hw.2.2)
    (by rw [toNat_lt64 hlt]; exact hb 0 (by decide)) (by rw [toNat_lt64 hlt]; exact hb 1 (by decide))
    (by rw [toNat_lt64 hlt]; exact hb 2 (by decide)) (by rw [toNat_lt64 hlt]; exact hb 3 (by decide))
    (by rw [toNat_lt64 hlt]; exact hb 4 (by decide)) (by rw [toNat_lt64 hlt]; exact hb 5 (by decide))
    (by rw [toNat_lt64 hlt]; exact hb 6 (by decide)) (by rw [toNat_lt64 hlt]; exact hb 7 (by decide))
  rw [cat8_extract] at hN
  exact ⟨t', hN.ret, rel_regW hR RD _ hN⟩

/-- **sd** (the address is a work cell; code and other cells unchanged) -/
theorem sim_sd {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {b a : Nat} {off : Int} (hC : K.W[pc]? = some (I.sd b a off).enc) (hb : b < 32) (ha : a < 32)
    (hi1 : -2048 ≤ off) (hi2 : off < 2048) (h0 : 0 ≤ ((s.x a).toNat : Int) + off)
    (hw : wok K (CallProbe.ea (s.x a) off)) :
    ∃ t', Retires t t' ∧
      RelW K (pc + 1, { s with m := CallProbe.upd s.m (CallProbe.ea (s.x a) off) (s.x b) }) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let B : Fin 32 := ⟨b, hb⟩
  let A : Fin 32 := ⟨a, ha⟩
  have hW := hK.wlo; have hH := hK.whi
  have hlt : CallProbe.ea (s.x a) off < 2 ^ 64 := by unfold wok at hw; omega
  have hea := eaW hR A off hi1 hi2 h0 (by show ((s.x a).toNat : Int) + off < 2 ^ 64; unfold CallProbe.ea at hlt; omega)
  have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (G.encS 3 (BitVec.ofNat 12 (bits off 12)) B A) := by
    have hi2 : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc))
        (BitVec.ofNat 32 (encSt 3 B.val A.val ((bits off 12 : Nat) : Int))) := by rw [← encSt_bits]; exact hi
    rw [encSt_eq 3 (by decide) B A _ (bits_lt off 12)] at hi2; exact hi2
  obtain ⟨t', hN⟩ := G.step_sd hR.cfg hR.pc hok B A _ hi' hea (by rw [toNat_lt64 hlt]; unfold wok at hw; omega)
    (by rw [toNat_lt64 hlt]; exact hw.2.2)
  rw [toNat_lt64 hlt, hR.x B] at hN
  refine ⟨t', hN.ret, ?_⟩
  exact {
    cfg := hN.cfg
    pc := by rw [hN.pc, ofNat_pc4]
    code := fun i h => by
      have hc := hR.code i h
      have hl : K.base + 4 * i < 2 ^ 64 := by have := hK.bhi; omega
      unfold instrAt at hc ⊢; rw [hN.mem]; rw [toNat_lt64 hl] at hc ⊢
      have hd := hK.cw; unfold wok at hw
      obtain ⟨c0, c1, c2, c3⟩ := hc
      exact ⟨by rw [store8_out _ _ _ _ (by omega)]; exact c0, by rw [store8_out _ _ _ _ (by omega)]; exact c1,
        by rw [store8_out _ _ _ _ (by omega)]; exact c2, by rw [store8_out _ _ _ _ (by omega)]; exact c3⟩
    x0 := hR.x0
    x := fun j => by
      rw [hN.x j]; simp only [show ¬ (j = 0 ∧ j ≠ 0) from fun h => h.2 h.1, if_false]; exact hR.x j
    w := fun c hc k hk => by
      rw [hN.mem]
      by_cases e : c = CallProbe.ea (s.x a) off
      · subst e; rw [store8_in _ _ _ k hk]; simp [CallProbe.upd]; rfl
      · unfold wok at hc hw
        rw [store8_out _ _ _ _ (by omega)]
        have := hR.w c hc k hk; simp [CallProbe.upd, e]; exact this }

end SimW
