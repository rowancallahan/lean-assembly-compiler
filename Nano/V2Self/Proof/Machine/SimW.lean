/- Bridge part 2 (Astra-11): the abstract machine of the codegen templates (`CallProbe.J`, Nano/V2Self/Proof/Machine/Call.lean)
against the Sail model.  `RelW`: J state ↔ Sail state, code = a list of 32-bit words at `base` (C's output), x0 = 0,
the work block's 8-aligned cells as 8 LE bytes.  One J step on a word that is the matching encoding = one retired
Sail instruction, keeping `RelW`.  Immediates are in range and address arithmetic does not wrap (side conditions the
template proofs discharge). -/
import Nano.V2.Sim
import Nano.V2Self.Proof.Machine.Call
import Nano.V2Self.Proof.Machine.Bridge

namespace SimW
open Proven Nano.V2B

structure LayW where
  base : Nat
  W : List Nat
  lo : Nat
  hi : Nat
  /-- input bytes `[ib, ib + il)` (read by lbu) and output bytes `[ob, ob + ol)` (written by sb) -/
  ib : Nat := 0
  il : Nat := 0
  ob : Nat := 0
  ol : Nat := 0
  /-- the Sail memory at the start: bytes outside the work cells and the output bytes keep it -/
  m0 : Nat → Option (BitVec 8) := fun _ => none

structure LayW.Ok (K : LayW) : Prop where
  b4 : K.base % 4 = 0
  blo : 0x80000000 ≤ K.base
  bhi : K.base + 4 * K.W.length ≤ 0x100000000
  wlo : 0x80000000 ≤ K.lo
  whi : K.hi ≤ 0x100000000
  cw : K.base + 4 * K.W.length ≤ K.lo ∨ K.hi ≤ K.base
  ibl : 0x80000000 ≤ K.ib
  ibh : K.ib + K.il ≤ 0x100000000
  obl : 0x80000000 ≤ K.ob
  obh : K.ob + K.ol ≤ 0x100000000
  oc : K.ob + K.ol ≤ K.base ∨ K.base + 4 * K.W.length ≤ K.ob

def wok (K : LayW) (a : Nat) : Prop := K.lo ≤ a ∧ a + 8 ≤ K.hi ∧ a % 8 = 0

/-- an output byte -/
def outB (K : LayW) (a : Nat) : Prop := K.ob ≤ a ∧ a < K.ob + K.ol
/-- an input or output byte -/
def io (K : LayW) (a : Nat) : Prop := (K.ib ≤ a ∧ a < K.ib + K.il) ∨ outB K a
/-- a byte lbu may read: in a work cell, or an input/output byte -/
def bok (K : LayW) (a : Nat) : Prop := wok K (a - a % 8) ∨ io K a
/-- a byte sb may write: in a work cell, or an output byte -/
def sok (K : LayW) (a : Nat) : Prop := wok K (a - a % 8) ∨ outB K a

structure RelW (K : LayW) (p : Nat × CallProbe.St) (t : Proven.St) : Prop where
  cfg : Proven.Cfg t
  pc : t.regs.get? .PC = some (BitVec.ofNat 64 (K.base + 4 * p.1))
  code : ∀ i (h : i < K.W.length), instrAt t (BitVec.ofNat 64 (K.base + 4 * i)) (BitVec.ofNat 32 K.W[i])
  x0 : p.2.x 0 = 0
  bb : p.2.b = K.base
  x : ∀ j : Fin 32, getX t j = (p.2.x j.val).toBitVec
  w : ∀ a, wok K a → ∀ k < 8, t.mem[a + k]? = some ((p.2.m a).toBitVec.extractLsb' (8 * k) 8)
  bw : ∀ a, io K a → t.mem[a]? = some ((p.2.m (a - a % 8)).toBitVec.extractLsb' (8 * (a % 8)) 8)
  fr : ∀ a, ¬ wok K (a - a % 8) → ¬ outB K a → t.mem[a]? = K.m0 a

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
  bb := by rw [CallProbe.wr_b]; exact hR.bb
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
  bw := fun a ha => by
    rw [hN.mem]; have := hR.bw a ha; unfold CallProbe.wr; split <;> simpa using this
  fr := fun a h1 h2 => by rw [hN.mem]; exact hR.fr a h1 h2

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
    bb := hR.bb
    x := fun j => by
      rw [hN.x j]; simp only [show ¬ (j = 0 ∧ j ≠ 0) from fun h => h.2 h.1, if_false]; exact hR.x j
    w := fun c hc k hk => by
      rw [hN.mem]
      by_cases e : c = CallProbe.ea (s.x a) off
      · subst e; rw [store8_in _ _ _ k hk]; simp [CallProbe.upd]; rfl
      · unfold wok at hc hw
        rw [store8_out _ _ _ _ (by omega)]
        have := hR.w c hc k hk; simp [CallProbe.upd, e]; exact this
    bw := fun c hc => by
      rw [hN.mem]
      have hw' := hw; unfold wok at hw'
      by_cases e : c - c % 8 = CallProbe.ea (s.x a) off
      · have h8 := Nat.mod_lt c (show 8 > 0 by omega)
        rw [show c = CallProbe.ea (s.x a) off + c % 8 by omega, store8_in _ _ _ _ h8]
        simp only [Nat.add_mod, hw'.2.2, Nat.zero_add, Nat.mod_mod]
        rw [show CallProbe.ea (s.x a) off + c % 8 - c % 8 = CallProbe.ea (s.x a) off by omega]
        simp [CallProbe.upd]; rfl
      · rw [store8_out _ _ _ _ (by omega)]
        have := hR.bw c hc; simp [CallProbe.upd, e]; exact this
    fr := fun c h1 h2 => by
      rw [hN.mem]
      have hw' := hw; unfold wok at hw'
      by_cases e : c - c % 8 = CallProbe.ea (s.x a) off
      · exact absurd (e ▸ hw) h1
      · rw [store8_out _ _ _ _ (by omega)]; exact hR.fr c h1 h2 }

/-- a retired control transfer that changes only the pc (and possibly writes `rd` with `v`) -/
theorem rel_jumpW {K : LayW} {pc pc' : Nat} {s : CallProbe.St} {t t' : Proven.St} (hR : RelW K (pc, s) t)
    (rd : Fin 32) (v : UInt64) (hN : Next t t' (BitVec.ofNat 64 (K.base + 4 * pc')) rd v.toBitVec t.mem) :
    RelW K (pc', CallProbe.wr s rd.val v) t' where
  cfg := hN.cfg
  bb := by rw [CallProbe.wr_b]; exact hR.bb
  pc := hN.pc
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
  bw := fun a ha => by
    rw [hN.mem]; have := hR.bw a ha; unfold CallProbe.wr; split <;> simpa using this
  fr := fun a h1 h2 => by rw [hN.mem]; exact hR.fr a h1 h2

/-- **bgeu a, b, +8** (C's checked push: skip the OOM `jal` when t6 ≥ t5); J's offset is 2 instructions -/
theorem sim_bgeu8 {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {a b : Nat} (hC : K.W[pc]? = some (I.br .bgeu a b 8).enc) (ha : a < 32) (hb : b < 32) :
    ∃ t', Retires t t' ∧
      RelW K (if (s.x b).toNat ≤ (s.x a).toNat then ((pc : Int) + 2).toNat else pc + 1, s) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let A : Fin 32 := ⟨a, ha⟩
  let B : Fin 32 := ⟨b, hb⟩
  have xa : getX t A = (s.x a).toBitVec := hR.x A
  have xb : getX t B = (s.x b).toBitVec := hR.x B
  have e := encBt8_eq 7 (by decide) A B
  have hi2 : instrAt t _ (BitVec.ofNat 32 (encBt 7 A.val B.val 8)) := hi
  rw [e] at hi2
  have w0 : CallProbe.wr s (0 : Fin 32).val (0 : UInt64) = s := by simp [CallProbe.wr]
  by_cases hc : (s.x a).toNat < (s.x b).toNat
  · obtain ⟨t', hN⟩ := G.bgeu_n hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact hc)
    rw [ofNat_pc4] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0, if_neg (by omega)] at *; exact ⟨t', hN.ret, this⟩
  · obtain ⟨t', hN⟩ := G.bgeu_t hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact hc)
    rw [boff8, pc_plus8] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0] at this
    rw [if_pos (by omega), show ((pc : Int) + 2).toNat = pc + 2 by omega]; exact ⟨t', hN.ret, this⟩

set_option maxRecDepth 100000 in
theorem encBt12_eq (f3 : Nat) (hf : f3 < 8) (rs1 rs2 : Fin 32) :
    BitVec.ofNat 32 (encBt f3 rs1.val rs2.val 12) = wB (BitVec.ofNat 3 f3) (.ofFin rs1) (.ofFin rs2) 6#12 := by
  unfold encBt; rw [show bits (12 : Int) 13 = 12 from rfl]; encbits

set_option maxRecDepth 100000 in
theorem encBt16_eq (f3 : Nat) (hf : f3 < 8) (rs1 rs2 : Fin 32) :
    BitVec.ofNat 32 (encBt f3 rs1.val rs2.val 16) = wB (BitVec.ofNat 3 f3) (.ofFin rs1) (.ofFin rs2) 8#12 := by
  unfold encBt; rw [show bits (16 : Int) 13 = 16 from rfl]; encbits

theorem boff12 : boff (6#12) = 12#64 := by decide
theorem boff16 : boff (8#12) = 16#64 := by decide
theorem pc_plus12 (b pc : Nat) : BitVec.ofNat 64 (b + 4 * pc) + 12#64 = BitVec.ofNat 64 (b + 4 * (pc + 3)) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
theorem pc_plus16 (b pc : Nat) : BitVec.ofNat 64 (b + 4 * pc) + 16#64 = BitVec.ofNat 64 (b + 4 * (pc + 4)) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

/-- **bgeu a, b, +12** (RD's range check) -/
theorem sim_bgeu12 {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {a b : Nat} (hC : K.W[pc]? = some (I.br .bgeu a b 12).enc) (ha : a < 32) (hb : b < 32) :
    ∃ t', Retires t t' ∧
      RelW K (if (s.x b).toNat ≤ (s.x a).toNat then ((pc : Int) + 3).toNat else pc + 1, s) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let A : Fin 32 := ⟨a, ha⟩
  let B : Fin 32 := ⟨b, hb⟩
  have xa : getX t A = (s.x a).toBitVec := hR.x A
  have xb : getX t B = (s.x b).toBitVec := hR.x B
  have e := encBt12_eq 7 (by decide) A B
  have hi2 : instrAt t _ (BitVec.ofNat 32 (encBt 7 A.val B.val 12)) := hi
  rw [e] at hi2
  have w0 : CallProbe.wr s (0 : Fin 32).val (0 : UInt64) = s := by simp [CallProbe.wr]
  by_cases hc : (s.x a).toNat < (s.x b).toNat
  · obtain ⟨t', hN⟩ := G.bgeu_n hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact hc)
    rw [ofNat_pc4] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0, if_neg (by omega)] at *; exact ⟨t', hN.ret, this⟩
  · obtain ⟨t', hN⟩ := G.bgeu_t hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact hc)
    rw [boff12, pc_plus12] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0] at this
    rw [if_pos (by omega), show ((pc : Int) + 3).toNat = pc + 3 by omega]; exact ⟨t', hN.ret, this⟩

/-- **bgeu a, b, +16** (BGET / BSET range checks) -/
theorem sim_bgeu16 {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {a b : Nat} (hC : K.W[pc]? = some (I.br .bgeu a b 16).enc) (ha : a < 32) (hb : b < 32) :
    ∃ t', Retires t t' ∧
      RelW K (if (s.x b).toNat ≤ (s.x a).toNat then ((pc : Int) + 4).toNat else pc + 1, s) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let A : Fin 32 := ⟨a, ha⟩
  let B : Fin 32 := ⟨b, hb⟩
  have xa : getX t A = (s.x a).toBitVec := hR.x A
  have xb : getX t B = (s.x b).toBitVec := hR.x B
  have e := encBt16_eq 7 (by decide) A B
  have hi2 : instrAt t _ (BitVec.ofNat 32 (encBt 7 A.val B.val 16)) := hi
  rw [e] at hi2
  have w0 : CallProbe.wr s (0 : Fin 32).val (0 : UInt64) = s := by simp [CallProbe.wr]
  by_cases hc : (s.x a).toNat < (s.x b).toNat
  · obtain ⟨t', hN⟩ := G.bgeu_n hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact hc)
    rw [ofNat_pc4] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0, if_neg (by omega)] at *; exact ⟨t', hN.ret, this⟩
  · obtain ⟨t', hN⟩ := G.bgeu_t hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact hc)
    rw [boff16, pc_plus16] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0] at this
    rw [if_pos (by omega), show ((pc : Int) + 4).toNat = pc + 4 by omega]; exact ⟨t', hN.ret, this⟩

/-- **beq a, b, +8** (IF on `==`) -/
theorem sim_beq8 {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {a b : Nat} (hC : K.W[pc]? = some (I.br .beq a b 8).enc) (ha : a < 32) (hb : b < 32) :
    ∃ t', Retires t t' ∧ RelW K (if s.x a = s.x b then ((pc : Int) + 2).toNat else pc + 1, s) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let A : Fin 32 := ⟨a, ha⟩
  let B : Fin 32 := ⟨b, hb⟩
  have xa : getX t A = (s.x a).toBitVec := hR.x A
  have xb : getX t B = (s.x b).toBitVec := hR.x B
  have e := encBt8_eq 0 (by decide) A B
  have hi2 : instrAt t _ (BitVec.ofNat 32 (encBt 0 A.val B.val 8)) := hi
  rw [e] at hi2
  have w0 : CallProbe.wr s (0 : Fin 32).val (0 : UInt64) = s := by simp [CallProbe.wr]
  by_cases hc : s.x a = s.x b
  · obtain ⟨t', hN⟩ := G.beq_t hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb, hc])
    rw [boff8, pc_plus8] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0] at this
    rw [if_pos hc, show ((pc : Int) + 2).toNat = pc + 2 by omega]; exact ⟨t', hN.ret, this⟩
  · obtain ⟨t', hN⟩ := G.beq_n hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact fun h => hc (UInt64.toBitVec_inj.1 h))
    rw [ofNat_pc4] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0] at this; rw [if_neg hc]; exact ⟨t', hN.ret, this⟩

/-- **bltu a, b, +8** (IF on `<`) -/
theorem sim_bltu8 {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {a b : Nat} (hC : K.W[pc]? = some (I.br .bltu a b 8).enc) (ha : a < 32) (hb : b < 32) :
    ∃ t', Retires t t' ∧ RelW K (if (s.x a).toNat < (s.x b).toNat then ((pc : Int) + 2).toNat else pc + 1, s) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let A : Fin 32 := ⟨a, ha⟩
  let B : Fin 32 := ⟨b, hb⟩
  have xa : getX t A = (s.x a).toBitVec := hR.x A
  have xb : getX t B = (s.x b).toBitVec := hR.x B
  have e := encBt8_eq 6 (by decide) A B
  have hi2 : instrAt t _ (BitVec.ofNat 32 (encBt 6 A.val B.val 8)) := hi
  rw [e] at hi2
  have w0 : CallProbe.wr s (0 : Fin 32).val (0 : UInt64) = s := by simp [CallProbe.wr]
  by_cases hc : (s.x a).toNat < (s.x b).toNat
  · obtain ⟨t', hN⟩ := G.bltu_t hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact hc)
    rw [boff8, pc_plus8] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0] at this
    rw [if_pos hc, show ((pc : Int) + 2).toNat = pc + 2 by omega]; exact ⟨t', hN.ret, this⟩
  · obtain ⟨t', hN⟩ := G.bltu_n hR.cfg hR.pc hok A B _ hi2 (by rw [xa, xb]; exact hc)
    rw [ofNat_pc4] at hN
    have := rel_jumpW hR 0 0 (by simpa using hN)
    rw [w0] at this; rw [if_neg hc]; exact ⟨t', hN.ret, this⟩

theorem ofInt_toNat64 (x : Int) : (UInt64.ofInt x).toNat = (x % 2 ^ 64).toNat := by
  rw [← UInt64.toNat_toBitVec, ofInt_bv, BitVec.toNat_ofInt]; simp

/-- **jal rd, off** (C's `g5 d (4·off)`; J offsets are in instructions): writes the byte return address -/
theorem sim_jal {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {d : Nat} {off : Int} (hd : d < 32) (hC : K.W[pc]? = some (C.g5 (UInt64.ofNat d) (UInt64.ofInt (4 * off))).toNat)
    (ho1 : -2 ^ 18 ≤ off) (ho2 : off < 2 ^ 18) (ht0 : 0 ≤ (pc : Int) + off) (ht1 : ((pc : Int) + off) < K.W.length) :
    ∃ t', Retires t t' ∧
      RelW K (((pc : Int) + off).toNat, CallProbe.wr s d (UInt64.ofNat (s.b + 4 * (pc + 1)))) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  have hdN : (UInt64.ofNat d).toNat = d := by simp; omega
  have hd' : (UInt64.ofNat d).toNat < 32 := by omega
  rw [Bridge.g5_wJ _ _ hd'] at hi
  let D : Fin 32 := ⟨(UInt64.ofNat d).toNat, hd'⟩
  obtain ⟨t', hN⟩ := G.step_jal hR.cfg hR.pc hok D _ hi
  have vt := ofInt_toNat64 (4 * off)
  have hv : ((UInt64.ofInt (4 * off)).toNat % 2097152) / 2 < 2 ^ 20 := by omega
  rw [joff_int _ hv (4 * off) (by omega) (by omega) (by unfold bits; rw [vt]; omega)] at hN
  have hb := hK.bhi; have hb0 := hK.blo
  have e1 : BitVec.ofNat 64 (K.base + 4 * pc) + BitVec.ofInt 64 (4 * off) =
      BitVec.ofNat 64 (K.base + 4 * ((pc : Int) + off).toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; omega
  have e2 : BitVec.ofNat 64 (K.base + 4 * pc) + 4 = (UInt64.ofNat (s.b + 4 * (pc + 1))).toBitVec := by
    rw [hR.bb]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
  rw [e1, e2] at hN
  have := rel_jumpW hR D _ hN
  simp only [D, hdN] at this
  exact ⟨t', hN.ret, this⟩

/-- **jalr x0, 0(rs)** (C's return `g2 103 0 0 a 0`): to the byte address in `rs`, which is `base + 4·j` -/
theorem sim_jalr {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {a j : Nat} (ha : a < 32) (hC : K.W[pc]? = some (C.g2 C.g_103 0 0 (UInt64.ofNat a) 0).toNat)
    (hra : (s.x a).toNat = K.base + 4 * j) :
    ∃ t', Retires t t' ∧ RelW K (j, s) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  have haN : (UInt64.ofNat a).toNat = a := by simp; omega
  rw [Bridge.g2_jalr _ (by omega), haN] at hi
  let A : Fin 32 := ⟨a, ha⟩
  have hb0 := hK.b4; have hbh := hK.bhi; have hbl := hK.blo
  have hra' : (s.x A.val).toNat = K.base + 4 * j := hra
  obtain ⟨t', hN⟩ := G.step_jalr hR.cfg hR.pc hok 0 A 0 (by simpa using hi)
    (by rw [hR.x A]; simp [hra']; omega)
  have e : getX t A + (0 : BitVec 12).signExtend 64 = BitVec.ofNat 64 (K.base + 4 * j) := by
    have := (s.x a).toNat_lt
    rw [hR.x A]; apply BitVec.eq_of_toNat_eq; simp [hra']; omega
  have hpc : (pc : Int) < K.W.length := by
    have := (List.getElem?_eq_some_iff.1 hC).1; omega
  have hv : BitVec.ofNat 64 (K.base + 4 * pc) + 4 = (UInt64.ofNat (K.base + 4 * pc + 4)).toBitVec := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega
  rw [e, hv] at hN
  have := rel_jumpW hR 0 _ hN
  simp [CallProbe.wr] at this
  exact ⟨t', hN.ret, this⟩

/-! ## ALU, slli, lbu (expression templates) -/

/-- J's ALU numbering (Gen's BIN: add 1 sub 2 mul 3 and 4 or 5 sll 6 srl 7 xor 8) as nano-v2's `ROp` -/
def ropOf (op : Nat) : ROp :=
  if op = 1 then .add else if op = 2 then .sub else if op = 3 then .mul else if op = 4 then .and
  else if op = 5 then .or else if op = 6 then .sll else if op = 7 then .srl else .xor

theorem shl_mod (a b : UInt64) : a <<< b = a <<< (b % 64) := by
  apply UInt64.toBitVec_inj.1; rw [shl_bv, UInt64.toBitVec_shiftLeft]; simp [BitVec.shiftLeft_eq', UInt64.toBitVec_mod]
theorem shr_mod (a b : UInt64) : a >>> b = a >>> (b % 64) := by
  apply UInt64.toBitVec_inj.1; rw [shr_bv, UInt64.toBitVec_shiftRight]; simp [BitVec.ushiftRight_eq', UInt64.toBitVec_mod]

theorem aluf_eval (op : Nat) (x y : UInt64) (h : 1 ≤ op ∧ op ≤ 8) : CallProbe.aluf op x y = (ropOf op).eval x y := by
  obtain ⟨h1, h2⟩ := h
  rcases (by omega : op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 ∨ op = 6 ∨ op = 7 ∨ op = 8) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [CallProbe.aluf, ropOf, ROp.eval]
  · exact shl_mod x y
  · exact shr_mod x y

/-- **R-type** (any `ROp`; `add`/`or` with rd = 0 decode as hints, so rd ≠ 0 there) -/
theorem sim_rW {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {f : ROp} {rd a b : Nat} (hC : K.W[pc]? = some (I.r f rd a b).enc) (hrd : rd < 32) (ha : a < 32) (hb : b < 32)
    (hadd : (f = .add ∨ f = .or) → rd ≠ 0) :
    ∃ t', Retires t t' ∧ RelW K (pc + 1, CallProbe.wr s rd (f.eval (s.x a) (s.x b))) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let RD : Fin 32 := ⟨rd, hrd⟩
  let A : Fin 32 := ⟨a, ha⟩
  let B : Fin 32 := ⟨b, hb⟩
  have xa : getX t A = (s.x a).toBitVec := hR.x A
  have xb : getX t B = (s.x b).toBitVec := hR.x B
  have hrd0 : f = .add ∨ f = .or → RD ≠ 0 := fun h e => hadd h (by simpa [RD] using congrArg Fin.val e)
  cases f with
  | add =>
    obtain ⟨t', hN⟩ := G.step_add hR.cfg hR.pc hok RD A B (hrd0 (Or.inl rfl)) hi
    rw [xa, xb, ← UInt64.toBitVec_add] at hN; exact ⟨t', hN.ret, rel_regW hR RD _ hN⟩
  | sub =>
    obtain ⟨t', hN⟩ := G.step_sub hR.cfg hR.pc hok RD A B hi
    rw [xa, xb, ← UInt64.toBitVec_sub] at hN; exact ⟨t', hN.ret, rel_regW hR RD _ hN⟩
  | mul =>
    obtain ⟨t', hN⟩ := G.step_mul hR.cfg hR.pc hok RD A B hi
    rw [xa, xb, ← UInt64.toBitVec_mul] at hN; exact ⟨t', hN.ret, rel_regW hR RD _ hN⟩
  | and =>
    obtain ⟨t', hN⟩ := G.step_and hR.cfg hR.pc hok RD A B hi
    rw [xa, xb, ← UInt64.toBitVec_and] at hN; exact ⟨t', hN.ret, rel_regW hR RD _ hN⟩
  | or =>
    obtain ⟨t', hN⟩ := G.step_or hR.cfg hR.pc hok RD A B hi
    rw [xa, xb, ← UInt64.toBitVec_or] at hN; exact ⟨t', hN.ret, rel_regW hR RD _ hN⟩
  | xor =>
    obtain ⟨t', hN⟩ := G.step_xor hR.cfg hR.pc hok RD A B hi
    rw [xa, xb, ← UInt64.toBitVec_xor] at hN; exact ⟨t', hN.ret, rel_regW hR RD _ hN⟩
  | sll =>
    obtain ⟨t', hN⟩ := G.step_sll hR.cfg hR.pc hok RD A B hi
    rw [xa, xb, ← shl_bv] at hN; exact ⟨t', hN.ret, rel_regW hR RD _ hN⟩
  | srl =>
    obtain ⟨t', hN⟩ := G.step_srl hR.cfg hR.pc hok RD A B hi
    rw [xa, xb, ← shr_bv] at hN; exact ⟨t', hN.ret, rel_regW hR RD _ hN⟩
  | sltu =>
    obtain ⟨t', hN⟩ := G.step_sltu hR.cfg hR.pc hok RD A B hi
    rw [xa, xb, ← sltu_bv] at hN; exact ⟨t', hN.ret, rel_regW hR RD _ hN⟩

/-- **alu** (Gen's BIN numbering 1..8) -/
theorem sim_aluW {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {op rd a b : Nat} (hC : K.W[pc]? = some (I.r (ropOf op) rd a b).enc) (hrd : rd < 32) (ha : a < 32) (hb : b < 32)
    (hop : 1 ≤ op ∧ op ≤ 8) (hrd0 : rd ≠ 0) :
    ∃ t', Retires t t' ∧ RelW K (pc + 1, CallProbe.wr s rd (CallProbe.aluf op (s.x a) (s.x b))) t' := by
  rw [aluf_eval op _ _ hop]; exact sim_rW hK hR hC hrd ha hb (fun _ => hrd0)

/-- **slli** -/
theorem sim_slliW {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {rd a sh : Nat} (hC : K.W[pc]? = some (I.i .slli rd a (sh : Int)).enc) (hrd : rd < 32) (ha : a < 32) (hsh : sh < 64) :
    ∃ t', Retires t t' ∧ RelW K (pc + 1, CallProbe.wr s rd (s.x a <<< sh.toUInt64)) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let RD : Fin 32 := ⟨rd, hrd⟩
  let A : Fin 32 := ⟨a, ha⟩
  have xa : getX t A = (s.x a).toBitVec := hR.x A
  have hn : (sh : Int).toNat < 64 := by simpa using hsh
  have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (Proven.encI 1 (0 <<< 6 ||| (BitVec.ofNat 6 (sh : Int).toNat).toNat) RD A) := by
    rw [show 0 <<< 6 ||| (BitVec.ofNat 6 (sh : Int).toNat).toNat = bits (sh : Int) 12 by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; unfold bits; simp; omega]; exact hi
  obtain ⟨t', hN⟩ := G.step_slli hR.cfg hR.pc hok RD A _ hi'
  rw [xa, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, ← shlK_bv _ _ hn] at hN
  exact ⟨t', hN.ret, by simpa using rel_regW hR RD _ hN⟩

theorem lbm_bv (m : UInt64) (k : Nat) (hk : k < 8) :
    (m.toBitVec.extractLsb' (8 * k) 8).setWidth 64 = ((m >>> (8 * k).toUInt64) &&& 255).toBitVec := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, UInt64.toNat_toBitVec, UInt64.toNat_and,
    UInt64.toNat_shiftRight]
  have h8 : (8 * k).toUInt64.toNat % 64 = 8 * k := by simp [Nat.toUInt64]; omega
  rw [h8, Nat.shiftRight_eq_div_pow]
  have h255 : (255 : UInt64).toNat = 255 := rfl
  rw [h255, show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt (by omega : m.toNat / 2 ^ (8 * k) % 2 ^ 8 < 2 ^ 64)

/-- **lbu**: the byte at the effective address, from the aligned cell that contains it (a work cell) -/
theorem sim_lbuW {K : LayW} {pc : Nat} {s : CallProbe.St} {t : Proven.St} (hK : K.Ok) (hR : RelW K (pc, s) t)
    {rd a : Nat} {off : Int} (hC : K.W[pc]? = some (I.lbu rd a off).enc) (hrd : rd < 32) (ha : a < 32)
    (hi1 : -2048 ≤ off) (hi2 : off < 2048) (h0 : 0 ≤ ((s.x a).toNat : Int) + off)
    (hw : bok K (CallProbe.ea (s.x a) off)) :
    ∃ t', Retires t t' ∧ RelW K (pc + 1, CallProbe.wr s rd (CallProbe.lbm s.m (CallProbe.ea (s.x a) off))) t' := by
  obtain ⟨hi, hok⟩ := codeW hK hR hC
  let RD : Fin 32 := ⟨rd, hrd⟩
  let A : Fin 32 := ⟨a, ha⟩
  have hW := hK.wlo; have hH := hK.whi; have := hK.ibh; have := hK.obh; have := hK.ibl; have := hK.obl
  have hk : CallProbe.ea (s.x a) off % 8 < 8 := Nat.mod_lt _ (by decide)
  have hrng : 0x80000000 ≤ CallProbe.ea (s.x a) off ∧ CallProbe.ea (s.x a) off + 1 ≤ 0x100000000 := by
    rcases hw with hw | hw | hw <;> (try simp only [wok, outB] at hw) <;> omega
  have hlt : CallProbe.ea (s.x a) off < 2 ^ 64 := by omega
  have hea := eaW hR A off hi1 hi2 h0 (by show ((s.x a).toNat : Int) + off < 2 ^ 64; unfold CallProbe.ea at hlt; omega)
  have hi' : instrAt t (BitVec.ofNat 64 (K.base + 4 * pc)) (G.encL 4 (BitVec.ofNat 12 (bits off 12)) RD A) := by
    unfold G.encL; rw [imm12_toNat]; exact hi
  have hb : t.mem[CallProbe.ea (s.x a) off]? = some ((s.m (CallProbe.ea (s.x a) off - CallProbe.ea (s.x a) off % 8)).toBitVec.extractLsb' (8 * (CallProbe.ea (s.x a) off % 8)) 8) := by
    rcases hw with hw | hw
    · have hb := hR.w _ hw (CallProbe.ea (s.x a) off % 8) hk
      rwa [show CallProbe.ea (s.x a) off - CallProbe.ea (s.x a) off % 8 + CallProbe.ea (s.x a) off % 8 = CallProbe.ea (s.x a) off by omega] at hb
    · exact hR.bw _ hw
  obtain ⟨t', hN⟩ := G.step_lbu hR.cfg hR.pc hok RD A _ hi' hea (by rw [toNat_lt64 hlt]; omega)
    (by rw [toNat_lt64 hlt]; exact hb)
  have := lbm_bv (s.m (CallProbe.ea (s.x a) off - CallProbe.ea (s.x a) off % 8)) (CallProbe.ea (s.x a) off % 8) hk
  rw [this] at hN
  have e8 : (8 * (CallProbe.ea (s.x a) off % 8)).toUInt64 = (8 * (CallProbe.ea (s.x a) off % 8) : Nat).toUInt64 := rfl
  exact ⟨t', hN.ret, rel_regW hR RD _ (by unfold CallProbe.lbm; exact hN)⟩


/-! ## whole runs: a J run on code whose words are the J instructions' encodings is a Sail run -/

/-- the word C emits for a J instruction (branches only as `bgeu a b +2 instructions`, returns only `jalr x0`) -/
def encJ : CallProbe.J → Nat
  | .addi rd rs imm => (I.i .addi rd rs imm).enc
  | .ld rd rs off => (I.ld rd rs off).enc
  | .sd b a off => (I.sd b a off).enc
  | .bgeu a b o => (I.br .bgeu a b (4 * o)).enc
  | .beq a b _ => (I.br .beq a b 8).enc
  | .bltu a b _ => (I.br .bltu a b 8).enc
  | .jal rd off => (C.g5 (UInt64.ofNat rd) (UInt64.ofInt (4 * off))).toNat
  | .jalr _ rs => (C.g2 C.g_103 0 0 (UInt64.ofNat rs) 0).toNat
  | .alu op rd a b => (I.r (ropOf op) rd a b).enc
  | .slli rd rs sh => (I.i .slli rd rs (sh : Int)).enc
  | .lbu rd rs off => (I.lbu rd rs off).enc
  | .srli rd rs sh => (C.g2 C.g_19 5 (UInt64.ofNat rd) (UInt64.ofNat rs) (UInt64.ofNat sh)).toNat
  | .bne a b off => (C.g4 1 (UInt64.ofNat a) (UInt64.ofNat b) (UInt64.ofInt (4 * off))).toNat
  | .sb r2 r1 off => (C.g3 0 (UInt64.ofNat r2) (UInt64.ofNat r1) (UInt64.ofInt off)).toNat

/-- the side conditions of one J step that the Sail step needs (ranges, no wrap, work cells, aligned return) -/
def Safe (K : LayW) (C : List CallProbe.J) : Nat × CallProbe.St → Prop
  | (pc, s) => match C[pc]? with
    | some (.addi rd rs imm) => rd < 32 ∧ rs < 32 ∧ -2048 ≤ imm ∧ imm < 2048 ∧
        0 ≤ ((s.x rs).toNat : Int) + imm ∧ ((s.x rs).toNat : Int) + imm < 2 ^ 64
    | some (.ld rd rs off) => rd < 32 ∧ rs < 32 ∧ -2048 ≤ off ∧ off < 2048 ∧
        0 ≤ ((s.x rs).toNat : Int) + off ∧ wok K (CallProbe.ea (s.x rs) off)
    | some (.sd b a off) => b < 32 ∧ a < 32 ∧ -2048 ≤ off ∧ off < 2048 ∧
        0 ≤ ((s.x a).toNat : Int) + off ∧ wok K (CallProbe.ea (s.x a) off)
    | some (.bgeu a b o) => a < 32 ∧ b < 32 ∧ (o = 2 ∨ o = 3 ∨ o = 4)
    | some (.beq a b o) => a < 32 ∧ b < 32 ∧ o = 2
    | some (.bltu a b o) => a < 32 ∧ b < 32 ∧ o = 2
    | some (.jal rd off) => rd < 32 ∧ -2 ^ 18 ≤ off ∧ off < 2 ^ 18 ∧ 0 ≤ (pc : Int) + off ∧ (pc : Int) + off < C.length
    | some (.jalr rd rs) => rd = 0 ∧ rs < 32 ∧ ∃ j, (s.x rs).toNat = K.base + 4 * j
    | some (.alu op rd a b) => rd < 32 ∧ a < 32 ∧ b < 32 ∧ (1 ≤ op ∧ op ≤ 8) ∧ rd ≠ 0
    | some (.slli rd rs sh) => rd < 32 ∧ rs < 32 ∧ sh < 64
    | some (.lbu rd rs off) => rd < 32 ∧ rs < 32 ∧ -2048 ≤ off ∧ off < 2048 ∧ 0 ≤ ((s.x rs).toNat : Int) + off ∧
        bok K (CallProbe.ea (s.x rs) off)
    | _ => False

/-- **one step**: a safe J step on matching words is one retired Sail instruction, keeping `RelW` -/
theorem sim_stepW {K : LayW} {C : List CallProbe.J} (hK : K.Ok) (hW : K.W = C.map encJ)
    {a b : Nat × CallProbe.St} {t : Proven.St} (hR : RelW K a t) (hS : Safe K C a) (hs : CallProbe.step C a = some b) :
    ∃ t', Retires t t' ∧ RelW K b t' := by
  obtain ⟨pc, s⟩ := a
  have hWpc : ∀ i, C[pc]? = some i → K.W[pc]? = some (encJ i) := by intro i h; rw [hW]; simp [h]
  simp only [Safe] at hS
  simp only [CallProbe.step] at hs
  cases hc : C[pc]? with
  | none => rw [hc] at hS; exact hS.elim
  | some i =>
    rw [hc] at hS hs
    cases i with
    | addi rd rs imm =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs; exact sim_addi hK hR (hWpc _ hc) h1 h2 h3 h4 h5 h6
    | ld rd rs off =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs; exact sim_ld hK hR (hWpc _ hc) h1 h2 h3 h4 h5 h6
    | sd b' a' off =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs; exact sim_sd hK hR (hWpc _ hc) h1 h2 h3 h4 h5 h6
    | bgeu a' b' o =>
      obtain ⟨h1, h2, ho⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs
      rcases ho with rfl | rfl | rfl
      · exact sim_bgeu8 hK hR (hWpc _ hc) h1 h2
      · exact sim_bgeu12 hK hR (hWpc _ hc) h1 h2
      · exact sim_bgeu16 hK hR (hWpc _ hc) h1 h2
    | jal rd off =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hS
      have hl : C.length = K.W.length := by rw [hW]; simp
      simp only [Option.some.injEq] at hs; subst hs; exact sim_jal hK hR h1 (hWpc _ hc) h2 h3 h4 (by rw [← hl]; exact h5)
    | jalr rd rs =>
      obtain ⟨rfl, h2, j, hj⟩ := hS
      have hb : s.b = K.base := hR.bb
      simp only [Option.some.injEq] at hs; subst hs
      obtain ⟨t', ht, hr⟩ := sim_jalr hK hR h2 (hWpc _ hc) hj
      refine ⟨t', ht, ?_⟩
      have : ((s.x rs).toNat - s.b) / 4 = j := by rw [hj, hb]; omega
      simp [this, CallProbe.wr]; exact hr
    | beq a' b' o =>
      obtain ⟨h1, h2, rfl⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs; exact sim_beq8 hK hR (hWpc _ hc) h1 h2
    | bltu a' b' o =>
      obtain ⟨h1, h2, rfl⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs; exact sim_bltu8 hK hR (hWpc _ hc) h1 h2
    | alu op rd a' b' =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs; exact sim_aluW hK hR (hWpc _ hc) h1 h2 h3 h4 h5
    | slli rd rs sh =>
      obtain ⟨h1, h2, h3⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs; exact sim_slliW hK hR (hWpc _ hc) h1 h2 h3
    | lbu rd rs off =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
      simp only [Option.some.injEq] at hs; subst hs; exact sim_lbuW hK hR (hWpc _ hc) h1 h2 h3 h4 h5 h6
    | srli _ _ _ => exact hS.elim
    | bne _ _ _ => exact hS.elim
    | sb _ _ _ => exact hS.elim

/-- J runs whose every step is `Safe` -/
inductive SStar (K : LayW) (C : List CallProbe.J) : Nat × CallProbe.St → Nat × CallProbe.St → Prop
  | refl (a) : SStar K C a a
  | head {a b c} : Safe K C a → CallProbe.step C a = some b → SStar K C b c → SStar K C a c

/-- **runs**: a safe J run on C's words is a run of retired Sail instructions, keeping `RelW` -/
theorem sim_starW {K : LayW} {C : List CallProbe.J} (hK : K.Ok) (hW : K.W = C.map encJ)
    {a b : Nat × CallProbe.St} (h : SStar K C a b) :
    ∀ {t : Proven.St}, RelW K a t → ∃ n t', Steps n t t' ∧ RelW K b t' := by
  induction h with
  | refl a => intro t hR; exact ⟨0, t, rfl, hR⟩
  | head hS hs _ ih =>
    intro t hR
    obtain ⟨t1, hr, hR1⟩ := sim_stepW hK hW hR hS hs
    obtain ⟨n, t', hst, hR'⟩ := ih hR1
    exact ⟨n + 1, t', ⟨t1, hr, hst⟩, hR'⟩

end SimW
