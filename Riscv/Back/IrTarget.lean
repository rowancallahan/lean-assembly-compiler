/- The RISC-V instance of the IR target interface (`Compiler/Ir/Target.lean`): `rvT`, assembled from the existing
step lemmas: the wide operations with a frame (`rvwF`, `Riscv/Back/OptB.lean`) and `getTop`
(`andi d, sp, -8; addi d, d, -8`, `Riscv/Back/MemRv.lean`).  New Sail reasoning: only the out-of-memory exit
`encXG` (`law_exitG`), which also restores the caller's `gp` from the stub's cell. -/
import Compiler.Ir.Emit
import Riscv.Back.OptB
import Riscv.Back.MemRv
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv
open Proven.Ir

theorem phys_ne2 : ∀ r : Reg, (2 : Fin 32) ≠ phys r := by decide


/-- the IR back end's out-of-memory exit: as `encK .exit`, and also the caller's frame register `gp` from the stub's
cell `top - 8`: `andi t0, sp, -8; ld ra, -16(t0); ld gp, -8(t0); addi a0, x0, -1; ret` -/
def encXG : List (BitVec 32) :=
  [encI 5 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) 5 2, encI 1 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) 5 5,
    G.encL 3 im16 1 5, G.encL 3 im8 3 5, encI 0 im1.toNat 10 0, iRet]

theorem law_exitG {s : St} {pc w v : BitVec 64} (hA : core.At s pc encXG) (h8 : 8 ≤ frameBase 0 (getX s 2))
    (hr : core.inRAM (frameBase 0 (getX s 2) - 8) 16) (hal : (frameBase 0 (getX s 2) - 8) % 8 = 0)
    (hb : bytes (core.mem s) (frameBase 0 (getX s 2) - 8) 8 = (le8 w).map some)
    (hg : bytes (core.mem s) (frameBase 0 (getX s 2)) 8 = (le8 v).map some) (hw : core.retOK w) :
    core.runsTo s fun s' => core.ok s' ∧ core.pcIs s' w ∧ core.get s' (avar 0) = BitVec.allOnes 64 ∧
      core.mem s' = core.mem s ∧ KC s s' ∧ getX s' 3 = v := by
  obtain ⟨h, hpc, hok, hi⟩ := first hA
  obtain ⟨s₀, hn₀⟩ := G.step_srli h hpc hok 5 2 3#6 hi
  have sp0 := Core.At.split _ (l₁ := [encI 5 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) 5 2])
    (l₂ := [encI 1 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) 5 5, G.encL 3 im16 1 5, G.encL 3 im8 3 5,
      encI 0 im1.toNat 10 0, iRet]) hA
  have hA₀ : core.At s₀ (next pc 1) [encI 1 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) 5 5, G.encL 3 im16 1 5,
      G.encL 3 im8 3 5, encI 0 im1.toNat 10 0, iRet] :=
    ⟨hn₀.cfg, hn₀.pc, core.codeAt_mem (memOf hn₀) sp0.2.1, sp0.2.2⟩
  obtain ⟨h0, hpc0, hok0, hi0⟩ := first hA₀
  obtain ⟨s₁, hn₁⟩ := G.step_slli h0 hpc0 hok0 5 5 3#6 hi0
  have sp1 := Core.At.split _ (l₁ := [encI 1 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) 5 5])
    (l₂ := [G.encL 3 im16 1 5, G.encL 3 im8 3 5, encI 0 im1.toNat 10 0, iRet]) hA₀
  have hA₁ : core.At s₁ (next (next pc 1) 1) [G.encL 3 im16 1 5, G.encL 3 im8 3 5, encI 0 im1.toNat 10 0, iRet] :=
    ⟨hn₁.cfg, hn₁.pc, core.codeAt_mem (memOf hn₁) sp1.2.1, sp1.2.2⟩
  have g5 : getX s₁ 5 = (getX s 2 >>> (3#6 : BitVec 6).toNat) <<< (3#6 : BitVec 6).toNat := by
    rw [hn₁.x, ite_pos ⟨rfl, by decide⟩, hn₀.x, ite_pos ⟨rfl, by decide⟩]
  obtain ⟨h1, hpc1, hok1, hi1⟩ := first hA₁
  have hfb : 8 ≤ (getX s 2).toNat / 8 * 8 - 8 := by unfold frameBase at h8; omega
  have hRam : core.ramHi = 0x100000000 := rfl
  have haddr : getX s₁ 5 + im16.signExtend 64 = BitVec.ofNat 64 (frameBase 0 (getX s 2) - 8) := by
    rw [g5, sx_im16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, shr_shl_toNat, BitVec.toNat_ofNat, frameBase]
    have := (getX s 2).isLt
    rw [BitVec.toNat_ofNat]
    omega
  have hA8 : (BitVec.ofNat 64 (frameBase 0 (getX s 2) - 8)).toNat = frameBase 0 (getX s 2) - 8 := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; unfold Base.inRAM at hr; omega
  have hr8 : core.inRAM (frameBase 0 (getX s 2) - 8) 8 := by unfold Base.inRAM at hr ⊢; omega
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := bytesAt_le8 (bytes_le8 hb)
  obtain ⟨s₂, hn₂⟩ := G.step_ld h1 hpc1 hok1 1 5 im16 hi1 haddr (by rw [hA8]; exact hr8) (by rw [hA8]; exact hal)
    (by rw [hn₁.mem, hn₀.mem, hA8]; exact b0) (by rw [hn₁.mem, hn₀.mem, hA8]; exact b1)
    (by rw [hn₁.mem, hn₀.mem, hA8]; exact b2) (by rw [hn₁.mem, hn₀.mem, hA8]; exact b3)
    (by rw [hn₁.mem, hn₀.mem, hA8]; exact b4) (by rw [hn₁.mem, hn₀.mem, hA8]; exact b5)
    (by rw [hn₁.mem, hn₀.mem, hA8]; exact b6) (by rw [hn₁.mem, hn₀.mem, hA8]; exact b7)
  rw [Proven.le8_cat] at hn₂
  have sp2 := Core.At.split _ (l₁ := [G.encL 3 im16 1 5]) (l₂ := [G.encL 3 im8 3 5, encI 0 im1.toNat 10 0, iRet]) hA₁
  have hA₂ : core.At s₂ (next (next (next pc 1) 1) 1) [G.encL 3 im8 3 5, encI 0 im1.toNat 10 0, iRet] :=
    ⟨hn₂.cfg, hn₂.pc, core.codeAt_mem (memOf hn₂) sp2.2.1, sp2.2.2⟩
  obtain ⟨h2, hpc2, hok2, hi2⟩ := first hA₂
  have g5' : getX s₂ 5 = getX s₁ 5 := by rw [hn₂.x, ite_neg (by decide)]
  have haddr2 : getX s₂ 5 + im8.signExtend 64 = BitVec.ofNat 64 (frameBase 0 (getX s 2)) := by
    rw [g5', g5, sx_im8]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, shr_shl_toNat, BitVec.toNat_ofNat, frameBase]
    have := (getX s 2).isLt
    rw [BitVec.toNat_ofNat]
    omega
  have hA0' : (BitVec.ofNat 64 (frameBase 0 (getX s 2))).toNat = frameBase 0 (getX s 2) := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; unfold Base.inRAM at hr; omega
  have hr0 : core.inRAM (frameBase 0 (getX s 2)) 8 := by unfold Base.inRAM at hr ⊢; omega
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := bytesAt_le8 (bytes_le8 hg)
  have hm2 : s₂.mem = s.mem := by rw [hn₂.mem, hn₁.mem, hn₀.mem]
  obtain ⟨s₃, hn₃⟩ := G.step_ld h2 hpc2 hok2 3 5 im8 hi2 haddr2 (by rw [hA0']; exact hr0)
    (by rw [hA0']; unfold frameBase at hal ⊢; omega)
    (by rw [hm2, hA0']; exact c0) (by rw [hm2, hA0']; exact c1)
    (by rw [hm2, hA0']; exact c2) (by rw [hm2, hA0']; exact c3)
    (by rw [hm2, hA0']; exact c4) (by rw [hm2, hA0']; exact c5)
    (by rw [hm2, hA0']; exact c6) (by rw [hm2, hA0']; exact c7)
  rw [Proven.le8_cat] at hn₃
  have sp3 := Core.At.split _ (l₁ := [G.encL 3 im8 3 5]) (l₂ := [encI 0 im1.toNat 10 0, iRet]) hA₂
  have hA₃ : core.At s₃ (next (next (next (next pc 1) 1) 1) 1) [encI 0 im1.toNat 10 0, iRet] :=
    ⟨hn₃.cfg, hn₃.pc, core.codeAt_mem (memOf hn₃) sp3.2.1, sp3.2.2⟩
  obtain ⟨h3, hpc3, hok3, hi3⟩ := first hA₃
  obtain ⟨s₄, hn₄⟩ := G.step_addi h3 hpc3 hok3 10 0 im1 hi3
  rw [sx_im1] at hn₄
  have sp4 := Core.At.split _ (l₁ := [encI 0 im1.toNat 10 0]) (l₂ := [iRet]) hA₃
  have hA₄ : core.At s₄ (next (next (next (next (next pc 1) 1) 1) 1) 1) [iRet] :=
    ⟨hn₄.cfg, hn₄.pc, core.codeAt_mem (memOf hn₄) sp4.2.1, sp4.2.2⟩
  obtain ⟨h4, hpc4, hok4, hi4⟩ := first1 hA₄
  have g1 : getX s₄ 1 = w := by
    rw [hn₄.x, ite_neg (by decide), hn₃.x, ite_neg (by decide), hn₂.x]; exact ite_pos ⟨rfl, by decide⟩
  obtain ⟨s₅, hn₅⟩ := step_ret h4 hpc4 hok4 hi4 (by rw [g1]; exact hw)
  refine runsTo_next hn₀ (runsTo_next hn₁ (runsTo_next hn₂ (runsTo_next hn₃ (runsTo_next hn₄
    (run1 hn₅ ⟨hn₅.cfg, ?_, ?_, ?_, ?_, ?_⟩)))))
  · have := hn₅.pc; rwa [g1] at this
  · show getX s₅ (phys (avar 0)) = _
    rw [phys_avar0, hn₅.x, ite_neg (by decide), hn₄.x, ite_pos ⟨rfl, by decide⟩, Proven.G.getX_zero]
    decide
  · exact (memOf hn₅).trans ((memOf hn₄).trans ((memOf hn₃).trans ((memOf hn₂).trans ((memOf hn₁).trans
      (memOf hn₀)))))
  · intro j hj h3' h1'
    have j5 : j ≠ 5 := hj R0
    have j10 : j ≠ 10 := hj RIn
    rw [hn₅.x, ite_neg (fun e => by simp_all), hn₄.x, ite_neg (fun e => j10 e.1), hn₃.x, ite_neg (fun e => h3' e.1),
      hn₂.x, ite_neg (fun e => h1' e.1), hn₁.x, ite_neg (fun e => j5 e.1), hn₀.x, ite_neg (fun e => j5 e.1)]
  · rw [hn₅.x, ite_neg (by decide), hn₄.x, ite_neg (by decide), hn₃.x]; exact if_pos ⟨rfl, by decide⟩

/-- **The Sail RV64 model is an IR target.** -/
def rvT : Target where
  toWideF := rvwF
  top s := (getX s 2).toNat / 8 * 8
  encT d := encK (.getTop d)
  t_top hd h16 hA := by
    have := law_getTop hd (by unfold frameBase; omega) hA
    simpa [frameBase] using this
  top_keepF h := by
    show (getX _ 2).toNat / 8 * 8 = (getX _ 2).toNat / 8 * 8
    rw [h 2 phys_ne2 (by decide)]
  frameAt_top _ _ := rfl
  enterOK_of {s n} hn h8 hal hr := by
    obtain ⟨h1, h2⟩ := hr
    refine ⟨?_, ?_, ?_, hn⟩
    · show ((getX s 2).toNat / 8 * 8 - 8 * (n + 1)) % 8 = 0
      have : (getX s 2).toNat / 8 * 8 % 8 = 0 := Nat.mul_mod_left _ _
      omega
    · exact h1
    · exact h2
  keepC := KC
  keepC_of_keepF h j hj h3 _ := h j hj h3
  keepC_trans h₁ h₂ j hj h3 h1 := (h₂ j hj h3 h1).trans (h₁ j hj h3 h1)
  top_keepC h := by
    show (getX _ 2).toNat / 8 * 8 = (getX _ 2).toNat / 8 * 8
    rw [h 2 phys_ne2 (by decide) (by decide)]
  retOK_al v h := by show v.toNat % 2 = 0; omega
  encCall d := encC (.call d)
  callOK d := decide (-2 ^ 18 ≤ d ∧ d < 2 ^ 18)
  lenCall := 1
  len_call _ := rfl
  c_call h hA := law_call (of_decide_eq_true h) hA
  encEC n := encC (.enterC n)
  c_enterC hn hA h1 hr hal _ := law_enterC hn hA h1 hr hal
  encLC n := encC (.leaveC n)
  c_leaveC := law_leaveC
  encX := encXG
  c_exit {s pc w v} hA h16 hr hal hb hg hw := by
    have e : frameBase 0 (getX s 2) - 8 = (getX s 2).toNat / 8 * 8 - 16 := by unfold frameBase; omega
    have e' : frameBase 0 (getX s 2) = (getX s 2).toNat / 8 * 8 - 8 := by unfold frameBase; omega
    have h16' : 16 ≤ (getX s 2).toNat / 8 * 8 := h16
    refine core.runsTo_mono (law_exitG hA (by unfold frameBase; omega) (by rw [e]; exact hr) (by rw [e]; exact hal)
      (by rw [e]; exact hb) (by rw [e']; exact hg) hw) fun s' ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩

end Proven.Mach.Riscv
