/- The RISC-V adapter: `rvTarget` (one RV64 word per J instruction, `encJX`; J register = RV register) and its laws,
from the existing Sail-RV simulation (SimW/SimX `sim_*`, one per J instruction kind: `rvSteps`; RvStep `sim_ret` / `sim_addiN`) through one bridge `RelW ↔ Rel`. -/
import Nano.V2Self.Proof.Machine.Target
import Nano.V2Self.Proof.Machine.SimX
import Nano.V2Self.Proof.Machine.RvStep
import Nano.Base.Riscv.Back.LinkL
namespace JT
open Proven Proven.Top SimW CallProbe

/-- the RISC-V layout of a program at a generic layout: its words are the program's encodings -/
abbrev rvLay (K : LayW) (C : List J) : LayRv := ⟨K, C.map encJX⟩

noncomputable def rvTarget : JTarget where
  M := riscv
  blockLen := 1
  enc j := [BitVec.ofNat 32 (encJX j)]
  reg := id
  scratch := []
  lay K C := (rvLay K C).Ok
  m0 s a := s.mem[a]?
  inv K _ s := ∀ a, 2 ^ 64 ≤ a → s.mem[a]? = K.m0 a
  valid _ := True
  loader _ _ _ _ := True

theorem obs_mem (t : Proven.St) {a : Nat} (ha : a < 2 ^ 64) :
    (riscvObserve t).memory (UInt64.ofNat a) = (t.mem[a]?).map UInt8.ofBitVec := by
  simp [riscvObserve, UInt64.toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem rmem (t : Proven.St) {a : Nat} (ha : a < 2 ^ 64) :
    (rvTarget.M.observe t).memory (UInt64.ofNat a) = (t.mem[a]?).map UInt8.ofBitVec := obs_mem t ha

theorem rmemR (t : Proven.St) {a : Nat} (ha : a < 2 ^ 64) :
    (riscv.observe t).memory (UInt64.ofNat a) = (t.mem[a]?).map UInt8.ofBitVec := obs_mem t ha

theorem rreg {t : Proven.St} (h : Cfg t) (j : Fin 32) (h0 : j ≠ 0) :
    (rvTarget.M.observe t).register j.val = UInt64.ofBitVec (getX t j) := Top.obs_reg h j h0

theorem omap_inj {x y : Option (BitVec 8)} (h : x.map UInt8.ofBitVec = y.map UInt8.ofBitVec) : x = y := by
  cases x <;> cases y <;> simp_all

theorem cbyte_eq (v : UInt64) (k : Nat) (hk : k < 8) :
    UInt8.ofBitVec (v.toBitVec.extractLsb' (8 * k) 8) = cbyte v k := by
  apply UInt8.toNat_inj.1
  have : (8 * k) % 64 = 8 * k := Nat.mod_eq_of_lt (by omega)
  simp [cbyte, BitVec.extractLsb'_toNat, UInt64.toNat_shiftRight, UInt8.toNat_ofBitVec, this]

theorem reg_none (t : Proven.St) {r : Nat} (h : r = 0 ∨ 32 ≤ r) : (riscvObserve t).register r = 0 := by
  simp only [riscvObserve]
  have : riscvRegister t r = none := by
    unfold riscvRegister; split <;> first | rfl | omega
  rw [this]; rfl

theorem rnone (t : Proven.St) {r : Nat} (h : r = 0 ∨ 32 ≤ r) : (rvTarget.M.observe t).register r = 0 := reg_none t h

/-- `Rel` (generic, through `observe`) gives SimW's `RelW` -/
theorem relW_of {K : LayW} {C : List J} {s0 : Proven.St} {p : Nat × CallProbe.St} {t : Proven.St} (hl : rvTarget.lay K C)
    (h : rvTarget.Rel K C s0 p t) : RelW (rvLay K C) p t := by
  have hK : (rvLay K C).Ok := hl
  have hb : K.base + 4 * C.length ≤ 0x100000000 := by simpa using hK.bhi
  have hwh : K.hi ≤ 0x100000000 := hK.whi
  have hih : K.ib + K.il ≤ 0x100000000 := hK.ibh
  have hoh : K.ob + K.ol ≤ 0x100000000 := hK.obh
  refine ⟨h.cfg, ?_, ?_, h.x0, h.bb, h.ww, ?_, ?_, ?_, ?_⟩
  · have hp := h.pc
    have hs := Top.isSome_of_cfg h.cfg (register := .PC) (by simp)
    have := Top.register_of hs (by simpa [rvTarget, riscv, riscvObserve] using hp)
    rw [this]; congr 1; apply BitVec.eq_of_toNat_eq; simp [rvTarget, JTarget.addr]
  · intro i hi
    have hiC : i < C.length := by simpa using hi
    have hwi : (rvLay K C).W[i] = encJX C[i] := by simp
    show instrAt t (BitVec.ofNat 64 (K.base + 4 * i)) (BitVec.ofNat 32 (rvLay K C).W[i])
    have hc := fun b (hb' : b < 4) => h.code i hiC 0 (by simp [rvTarget]) b hb'
    simp only [rvTarget, JTarget.addr, List.getElem_cons_zero] at hc
    have ha : ∀ b, b < 4 → K.base + 4 * 1 * i + 4 * 0 + b < 2 ^ 64 := fun b hb' => by
      omega
    have e : ∀ b, b < 4 → t.mem[K.base + 4 * i + b]? = some ((BitVec.ofNat 32 (encJX C[i])).extractLsb' (8 * b) 8) := by
      intro b hb'
      have := hc b hb'; rw [rmemR t (ha b hb')] at this
      have e2 : K.base + 4 * 1 * i + 4 * 0 + b = K.base + 4 * i + b := by omega
      rw [e2] at this
      exact omap_inj (by rw [this]; rfl)
    have hpc : (BitVec.ofNat 64 (K.base + 4 * i)).toNat = K.base + 4 * i := by
      simp; omega
    unfold instrAt; rw [hpc, hwi]
    refine ⟨by simpa using e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)⟩
  · intro j
    by_cases h0 : j = 0
    · subst h0; simp [getX, xval, h.x0]
    · have hj : 0 < j.val := by have := Fin.val_ne_of_ne h0; omega
      have := h.x j.val hj j.isLt
      rw [show rvTarget.reg j.val = j.val from rfl, rreg h.cfg j h0] at this
      rw [← this]
  · intro a ha k hk
    replace ha : wok K a := ha
    have hlt : a + k < 2 ^ 64 := by unfold wok at ha; omega
    have := h.w a ha k hk; rw [rmem t hlt, ← cbyte_eq _ _ hk] at this
    exact omap_inj (by rw [this]; rfl)
  · intro a ha
    replace ha : io K a := ha
    have hlt : a < 2 ^ 64 := by unfold io outB at ha; omega
    have := h.bw a ha; rw [rmem t hlt, ← cbyte_eq _ _ (Nat.mod_lt _ (by omega))] at this
    exact omap_inj (by rw [this]; rfl)
  · intro a h1 h2
    by_cases hlt : a < 2 ^ 64
    · have := h.fr a hlt h1 h2; rw [rmem t hlt] at this; exact omap_inj this
    · exact h.inv a (by omega)

/-- SimW's `RelW` gives `Rel` (any entry state: RISC-V blocks clobber nothing outside x1..x31) -/
theorem rel_of {K : LayW} {C : List J} {s0 : Proven.St} {p : Nat × CallProbe.St} {t : Proven.St} (hl : rvTarget.lay K C)
    (h : RelW (rvLay K C) p t) : rvTarget.Rel K C s0 p t := by
  have hK : (rvLay K C).Ok := hl
  have hb : K.base + 4 * C.length ≤ 0x100000000 := by simpa using hK.bhi
  have hwh : K.hi ≤ 0x100000000 := hK.whi
  have hih : K.ib + K.il ≤ 0x100000000 := hK.ibh
  have hoh : K.ob + K.ol ≤ 0x100000000 := hK.obh
  refine ⟨h.cfg, ?_, ?_, h.x0, h.bb, h.ww, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ((t.regs.get? .PC).map UInt64.ofBitVec).getD 0 = UInt64.ofNat (K.base + 4 * 1 * p.1)
    rw [h.pc]; apply UInt64.toNat_inj.1
    simp only [Option.map_some, Option.getD_some, UInt64.toNat_ofBitVec, BitVec.toNat_ofNat, UInt64.toNat_ofNat']
  · intro i hiC k hk b hb'
    simp only [rvTarget, List.length_singleton] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    have hi : i < (rvLay K C).W.length := by simpa using hiC
    have hc : instrAt t (BitVec.ofNat 64 (K.base + 4 * i)) (BitVec.ofNat 32 (rvLay K C).W[i]) := h.code i hi
    have hwi : (rvLay K C).W[i] = encJX C[i] := by simp
    rw [hwi] at hc; unfold instrAt at hc
    have hpc : (BitVec.ofNat 64 (K.base + 4 * i)).toNat = K.base + 4 * i := by simp; omega
    rw [hpc] at hc
    simp only [rvTarget, JTarget.addr, List.getElem_cons_zero]
    have hlt : K.base + 4 * i + b < 2 ^ 64 := by omega
    rw [show K.base + 4 * 1 * i + 4 * 0 + b = K.base + 4 * i + b by omega, rmemR t hlt]
    obtain ⟨c0, c1, c2, c3⟩ := hc
    rcases (by omega : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3) with rfl | rfl | rfl | rfl
    · simp [c0, wbyte]
    · rw [c1]; rfl
    · rw [c2]; rfl
    · rw [c3]; rfl
  · intro j hj h32
    show (rvTarget.M.observe t).register (⟨j, h32⟩ : Fin 32).val = _
    rw [rreg h.cfg ⟨j, h32⟩ (by intro e; simp [Fin.ext_iff] at e; omega), h.x ⟨j, h32⟩]
  · intro r hr _
    have : r = 0 ∨ 32 ≤ r := Classical.byContradiction fun hc => hr r (by omega) (by omega) rfl
    rw [rnone t this, rnone s0 this]
  · intro a ha k hk
    have hlt : a + k < 2 ^ 64 := by unfold wok at ha; omega
    rw [rmem t hlt, h.w a ha k hk, ← cbyte_eq _ _ hk]; rfl
  · intro a ha
    have hlt : a < 2 ^ 64 := by unfold io outB at ha; omega
    rw [rmem t hlt, h.bw a ha, ← cbyte_eq _ _ (Nat.mod_lt _ (by omega))]; rfl
  · intro a hlt h1 h2
    rw [rmem t hlt, h.fr a h1 h2]
  · intro a ha
    exact h.fr a (show ¬ wok K (a - a % 8) by unfold wok; omega) (show ¬ outB K a by unfold outB; omega)

/-- a Sail-RV simulation lemma at the word of `j` gives the generic obligation for `j` (through `relW_of` / `rel_of`) -/
theorem rv_at {j : J}
    (h : ∀ {K : LayRv} {C : List J} {pc : Nat} {s : CallProbe.St} {t : Proven.St} {b : Nat × CallProbe.St},
      K.Ok → RelW K (pc, s) t → K.W[pc]? = some (encJX j) → C.length = K.W.length → SafeX K C (pc, s) →
      C[pc]? = some j → CallProbe.step C (pc, s) = some b → ∃ t', Retires t t' ∧ RelW K b t') :
    rvTarget.StepAt j := by
  intro K C s0 pc st s b hl hR hc hS hs
  obtain ⟨t', hr, hR'⟩ := h (K := rvLay K C) hl (relW_of hl hR) (by simp [hc]) (by simp) hS hc hs
  exact ⟨t', .step (Top.step_of_retires hr) .stop, rel_of hl hR'⟩

/-- **RISC-V, one J instruction kind at a time**: each is one retired Sail instruction (SimW/SimX's `sim_*`) -/
theorem rvSteps : rvTarget.StepLaws where
  addi rd rs imm := rv_at fun hK hR hw hl hS hc hs => by
    jcase; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS; exact sim_addi hK hR hw h1 h2 h3 h4 h5 h6
  ld rd rs off := rv_at fun hK hR hw hl hS hc hs => by
    jcase; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS; exact sim_ld hK hR hw h1 h2 h3 h4 h5 h6
  sd rs2 rs1 off := rv_at fun hK hR hw hl hS hc hs => by
    jcase; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS; exact sim_sd hK hR hw h1 h2 h3 h4 h5 h6
  jal rd off := rv_at fun hK hR hw hl hS hc hs => by
    jcase; obtain ⟨h1, h2, h3, h4, h5⟩ := hS
    exact sim_jal hK hR h1 hw h2 h3 h4 (by rw [← hl]; exact h5)
  jalr rd rs := rv_at fun {K C pc s t b} hK hR hw hl hS hc hs => by
    jcase; obtain ⟨rfl, h2, j, hj⟩ := hS
    have hb : s.b = K.base := hR.bb
    obtain ⟨t', ht, hr⟩ := sim_jalr hK hR h2 hw (by rw [hj, hR.w4])
    refine ⟨t', ht, ?_⟩
    have : ((s.x rs).toNat - s.b) / s.w = j := by rw [hj, hb, hR.w4]; omega
    simp [this, CallProbe.wr]; exact hr
  bgeu a b off := rv_at fun hK hR hw hl hS hc hs => by
    jcase; obtain ⟨h1, h2, ho⟩ := hS
    rcases ho with rfl | rfl | rfl
    · exact sim_bgeu8 hK hR hw h1 h2
    · exact sim_bgeu12 hK hR hw h1 h2
    · exact sim_bgeu16 hK hR hw h1 h2
  alu op rd a b := rv_at fun hK hR hw hl hS hc hs => by
    jcase; obtain ⟨h1, h2, h3, h4, h5⟩ := hS; exact sim_aluW hK hR hw h1 h2 h3 h4 h5
  slli rd rs sh := rv_at fun hK hR hw hl hS hc hs => by
    jcase; obtain ⟨h1, h2, h3⟩ := hS; exact sim_slliW hK hR hw h1 h2 h3
  lbu rd rs off := rv_at fun hK hR hw hl hS hc hs => by
    jcase; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS; exact sim_lbuW hK hR hw h1 h2 h3 h4 h5 h6
  beq a b off := rv_at fun hK hR hw hl hS hc hs => by
    jcase; obtain ⟨h1, h2, ho⟩ := hS
    rcases ho with rfl | rfl
    · exact sim_beq8 hK hR hw h1 h2
    · exact sim_beq28 hK hR hw h1 h2
  bltu a b off := rv_at fun hK hR hw hl hS hc hs => by
    jcase; obtain ⟨h1, h2, rfl⟩ := hS; exact sim_bltu8 hK hR hw h1 h2
  srli rd rs sh := rv_at fun hK hR hw hl hS hc hs => by
    jcase; obtain ⟨h1, h2, h3⟩ := hS
    simp only [encJX] at hw; rw [encJ_srli _ _ _ h1 h2 h3] at hw
    exact sim_srliW hK hR hw h1 h2 h3
  bne a b off := rv_at fun hK hR hw hl hS hc hs => by
    jcase; obtain ⟨h1, h2, rfl⟩ := hS
    simp only [encJX] at hw; rw [encJ_bne _ _ h1 h2] at hw
    exact sim_bne16 hK hR hw h1 h2
  sb rs2 rs1 off := rv_at fun hK hR hw hl hS hc hs => by
    jcase; obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
    simp only [encJX] at hw; rw [encJ_sb _ _ _ h1 h2 h3 h4] at hw
    exact sim_sbW hK hR hw h1 h2 h3 h4 h5 h6

theorem rvLaws : rvTarget.Laws where
  blk_pos := by decide
  enc_len _ := rfl
  reg_map := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  kept_map r hr := by
    left; refine ⟨r, ?_, ?_, rfl, ?_⟩ <;>
      simp [rvTarget, riscv, riscvMapping] at hr <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  ram := by simp [rvTarget, riscv]
  lay_init K C h _ := by
    have hn : 4 * rvTarget.blockLen * C.length = 4 * (rvLay K C).W.length := by simp [rvTarget]
    rw [hn] at h
    exact ⟨h.b4, h.blo, h.bhi, h.wlo, h.whi, h.cw, h.ibl, h.ibh, h.obl, h.obh, h.oc⟩
  m0_obs s a ha := obs_mem s ha
  inv_init K _ s _ _ _ _ _ _ _ h _ _ _ _ _ _ a _ := by rw [h]; rfl
  steps := rvSteps
  addi_ok := by
    intro K C s0 pc st s rd rs imm hl hR hC h1 h2 h3 h4
    have hWc : (rvLay K C).W[pc]? = some (encJ (.addi rd rs imm)) := by simp [hC, encJX]
    obtain ⟨t', hr, hR'⟩ := sim_addiN hl (relW_of hl hR) hWc h1 h2 h3 h4
    exact ⟨t', .step (Top.step_of_retires hr) .stop, rel_of hl hR'⟩
  ret_ok := by
    intro K C s0 pc st s hl hR hC h4
    have hW := relW_of hl hR
    have hWc : (rvLay K C).W[pc]? = some (_root_.C.g2 _root_.C.g_103 0 0 (UInt64.ofNat 1) 0).toNat := by
      simp [hC, encJX, encJ]
    obtain ⟨t', v, hN⟩ := sim_ret hl hW (a := 1) (by omega) hWc (by omega)
    refine ⟨t', .step (Top.step_of_retires hN.ret) .stop, ?_, ?_, ?_, hN.cfg⟩
    · show ((t'.regs.get? .PC).map UInt64.ofBitVec).getD 0 = st.x 1
      rw [hN.pc]; rfl
    · intro r
      by_cases hr : r = 0 ∨ 32 ≤ r
      · rw [rnone t' hr, rnone s hr]
      · have h32 : r < 32 := by omega
        have h0 : (⟨r, h32⟩ : Fin 32) ≠ 0 := by intro e; simp [Fin.ext_iff] at e; omega
        show (rvTarget.M.observe t').register (⟨r, h32⟩ : Fin 32).val = (rvTarget.M.observe s).register (⟨r, h32⟩ : Fin 32).val
        rw [rreg hN.cfg _ h0, rreg hR.cfg _ h0, hN.x]; simp
    · show (riscvObserve t').memory = (riscvObserve s).memory
      funext a; simp [riscvObserve, hN.mem]

end JT
