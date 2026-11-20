/- The RISC-V adapter: `rvTarget` (one RV64 word per J instruction, `encJX`; J register = RV register) and its laws,
from the existing Sail-RV simulation (SimW/SimX `sim_stepX`, RvStep `sim_ret` / `sim_addiN`) through one bridge `RelW ↔ Rel`. -/
import Nano.V2Self.Proof.Machine.Target
import Nano.V2Self.Proof.Machine.SimX
import Nano.V2Self.Proof.Machine.RvStep
import Riscv.Back.LinkL
namespace JT
open Proven Proven.Top SimW CallProbe

noncomputable def rvTarget : JTarget where
  M := riscv
  blockLen := 1
  enc j := [BitVec.ofNat 32 (encJX j)]
  reg := id
  scratch := []
  lay K C := K.Ok ∧ K.W = C.map encJX
  m0 s a := s.mem[a]?
  inv K s := ∀ a, 2 ^ 64 ≤ a → s.mem[a]? = K.m0 a
  words C := C.map encJX

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

theorem wbyte_eq (w : BitVec 32) (b : Nat) : UInt8.ofBitVec (w.extractLsb' (8 * b) 8) = wbyte w b := rfl

theorem reg_none (t : Proven.St) {r : Nat} (h : r = 0 ∨ 32 ≤ r) : (riscvObserve t).register r = 0 := by
  simp only [riscvObserve]
  have : riscvRegister t r = none := by
    unfold riscvRegister; split <;> first | rfl | omega
  rw [this]; rfl

theorem rnone (t : Proven.St) {r : Nat} (h : r = 0 ∨ 32 ≤ r) : (rvTarget.M.observe t).register r = 0 := reg_none t h

/-- `Rel` (generic, through `observe`) gives SimW's `RelW` -/
theorem relW_of {K : LayW} {C : List J} {s0 : Proven.St} {p : Nat × CallProbe.St} {t : Proven.St} (hl : rvTarget.lay K C)
    (h : rvTarget.Rel K C s0 p t) : RelW K p t := by
  obtain ⟨hK, hW⟩ := hl
  have hb := hK.bhi; have hwh := hK.whi; have hih := hK.ibh; have hoh := hK.obh
  refine ⟨h.cfg, ?_, ?_, h.x0, h.bb, ?_, ?_, ?_, ?_⟩
  · have hp := h.pc
    have hs := Top.isSome_of_cfg h.cfg (register := .PC) (by simp)
    have := Top.register_of hs (by simpa [rvTarget, riscv, riscvObserve] using hp)
    rw [this]; congr 1; apply BitVec.eq_of_toNat_eq; simp [rvTarget, JTarget.addr]
  · intro i hi
    have hiC : i < C.length := by rw [hW] at hi; simpa using hi
    have hwi : K.W[i] = encJX C[i] := by simp [hW]
    have hc := fun b (hb' : b < 4) => h.code i hiC 0 (by simp [rvTarget]) b hb'
    simp only [rvTarget, JTarget.addr, List.getElem_cons_zero] at hc
    have ha : ∀ b, b < 4 → K.base + 4 * 1 * i + 4 * 0 + b < 2 ^ 64 := fun b hb' => by
      have : i < K.W.length := hi; omega
    have e : ∀ b, b < 4 → t.mem[K.base + 4 * i + b]? = some ((BitVec.ofNat 32 (encJX C[i])).extractLsb' (8 * b) 8) := by
      intro b hb'
      have := hc b hb'; rw [rmemR t (ha b hb')] at this
      have e2 : K.base + 4 * 1 * i + 4 * 0 + b = K.base + 4 * i + b := by omega
      rw [e2] at this
      exact omap_inj (by rw [this]; rfl)
    have hpc : (BitVec.ofNat 64 (K.base + 4 * i)).toNat = K.base + 4 * i := by
      simp; have : i < K.W.length := hi; omega
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
    have hlt : a + k < 2 ^ 64 := by unfold wok at ha; omega
    have := h.w a ha k hk; rw [rmem t hlt, ← cbyte_eq _ _ hk] at this
    exact omap_inj (by rw [this]; rfl)
  · intro a ha
    have hlt : a < 2 ^ 64 := by unfold io outB at ha; omega
    have := h.bw a ha; rw [rmem t hlt, ← cbyte_eq _ _ (Nat.mod_lt _ (by omega))] at this
    exact omap_inj (by rw [this]; rfl)
  · intro a h1 h2
    by_cases hlt : a < 2 ^ 64
    · have := h.fr a hlt h1 h2; rw [rmem t hlt] at this; exact omap_inj this
    · exact h.inv a (by omega)

/-- SimW's `RelW` gives `Rel` (any entry state: RISC-V blocks clobber nothing outside x1..x31) -/
theorem rel_of {K : LayW} {C : List J} {s0 : Proven.St} {p : Nat × CallProbe.St} {t : Proven.St} (hl : rvTarget.lay K C)
    (h : RelW K p t) : rvTarget.Rel K C s0 p t := by
  obtain ⟨hK, hW⟩ := hl
  have hb := hK.bhi; have hwh := hK.whi; have hih := hK.ibh; have hoh := hK.obh
  refine ⟨h.cfg, ?_, ?_, h.x0, h.bb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ((t.regs.get? .PC).map UInt64.ofBitVec).getD 0 = UInt64.ofNat (K.base + 4 * 1 * p.1)
    rw [h.pc]; apply UInt64.toNat_inj.1
    simp only [Option.map_some, Option.getD_some, UInt64.toNat_ofBitVec, BitVec.toNat_ofNat, UInt64.toNat_ofNat']
  · intro i hiC k hk b hb'
    simp only [rvTarget, List.length_singleton] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    have hi : i < K.W.length := by rw [hW]; simpa using hiC
    have hc := h.code i hi
    have hwi : K.W[i] = encJX C[i] := by simp [hW]
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
    exact h.fr a (by unfold wok; omega) (by unfold outB; omega)

theorem rvLaws : rvTarget.Laws where
  enc_len _ := rfl
  reg_map := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  kept_map r hr := by
    left; refine ⟨r, ?_, ?_, rfl, ?_⟩ <;>
      simp [rvTarget, riscv, riscvMapping] at hr <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  ram := by simp [rvTarget, riscv]
  lay_init K C h hW := by
    have hn : 4 * rvTarget.blockLen * C.length = 4 * K.W.length := by
      rw [hW]; simp [rvTarget]
    rw [hn] at h
    exact ⟨⟨h.b4, h.blo, h.bhi, h.wlo, h.whi, h.cw, h.ibl, h.ibh, h.obl, h.obh, h.oc⟩, hW⟩
  m0_obs s a ha := obs_mem s ha
  inv_init K s h a _ := by rw [h]; rfl
  step_ok := by
    intro K C s0 a b s hl hR hS hs
    obtain ⟨t', hr, hR'⟩ := sim_stepX hl.1 hl.2 (relW_of hl hR) hS hs
    exact ⟨t', .step (Top.step_of_retires hr) .stop, rel_of hl hR'⟩
  addi_ok := by
    intro K C s0 pc st s rd rs imm hl hR hC h1 h2 h3 h4
    have hWc : K.W[pc]? = some (encJ (.addi rd rs imm)) := by rw [hl.2]; simp [hC, encJX]
    obtain ⟨t', hr, hR'⟩ := sim_addiN hl.1 (relW_of hl hR) hWc h1 h2 h3 h4
    exact ⟨t', .step (Top.step_of_retires hr) .stop, rel_of hl hR'⟩
  ret_ok := by
    intro K C s0 pc st s hl hR hC h4
    have hW := relW_of hl hR
    have hWc : K.W[pc]? = some (_root_.C.g2 _root_.C.g_103 0 0 (UInt64.ofNat 1) 0).toNat := by
      rw [hl.2]; simp [hC, encJX, encJ]
    obtain ⟨t', v, hN⟩ := sim_ret hl.1 hW (a := 1) (by omega) hWc (by omega)
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
