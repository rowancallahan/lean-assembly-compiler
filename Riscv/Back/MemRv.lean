/- The RISC-V instance of the run-time memory interface (`Compiler/MemCode.lean`): `rvM : MachineM` over `rvC`.
`bltu` / `bgeu` are the single instructions; `getFr d` is `addi d, gp, 0`; `getTop d` is
`andi d, sp, -8; addi d, d, -8` (the entry stub's frame); the out-of-memory exit is
`andi t0, sp, -8; ld ra, -16(t0); addi a0, x0, -1; ret` (the caller's return address from the stub's cell,
status `-1` in `a0`).  Every law is proved from the register-generic step lemmas. -/
import Compiler.MemCode
import Riscv.Back.Call
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv

/-- the 12-bit immediate `-8` / `-16` / `-1` -/
def im8 : BitVec 12 := 0xff8#12
def im16 : BitVec 12 := 0xff0#12
def im1 : BitVec 12 := 0xfff#12

def encK : KOp → List (BitVec 32)
  | .bltu a b n => [wB 6 (.ofFin (phys a)) (.ofFin (phys b)) (BitVec.ofNat 12 (2 * n))]
  | .bgeu a b n => [wB 7 (.ofFin (phys a)) (.ofFin (phys b)) (BitVec.ofNat 12 (2 * n))]
  | .getFr d => [encI 0 0 (phys d) 3]
  | .getTop d => [encI 5 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) (phys d) 2,
      encI 1 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) (phys d) (phys d), encI 0 im8.toNat (phys d) (phys d)]
  | .exit => [encI 5 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) 5 2, encI 1 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) 5 5,
      G.encL 3 im16 1 5, encI 0 im1.toNat 10 0, iRet]

theorem sx_im8 : im8.signExtend 64 = 0xfffffffffffffff8#64 := by decide
theorem sx_im16 : im16.signExtend 64 = 0xfffffffffffffff0#64 := by decide
theorem sx_im1 : im1.signExtend 64 = 0xffffffffffffffff#64 := by decide
theorem sx_0 : (0 : BitVec 12).signExtend 64 = 0#64 := by decide

theorem shr_shl_toNat (x : BitVec 64) : ((x >>> (3#6 : BitVec 6).toNat) <<< (3#6 : BitVec 6).toNat).toNat =
    x.toNat / 8 * 8 := by
  have := x.isLt
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  show x.toNat / 2 ^ 3 * 2 ^ 3 % 2 ^ 64 = _
  rw [Nat.mod_eq_of_lt (by omega)]

theorem frameBase_bv (x : BitVec 64) (h : 8 ≤ x.toNat / 8 * 8) :
    ((x >>> (3#6 : BitVec 6).toNat) <<< (3#6 : BitVec 6).toNat) + 0xfffffffffffffff8#64 =
      BitVec.ofNat 64 (frameBase 0 x) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, shr_shl_toNat, frameBase, BitVec.toNat_ofNat]
  have := x.isLt
  rw [BitVec.toNat_ofNat]
  omega

theorem law_bltu {a b : Reg} {n : Nat} {s : St} {pc : BitVec 64} (hn : core.bzOK n)
    (hA : core.At s pc (encK (.bltu a b n))) :
    core.runsTo s fun s' => core.Done s s'
        (if (core.get s a).toNat < (core.get s b).toNat then next pc n else next pc 1) ∧
      core.Same s s' ∧ core.mem s' = core.mem s := by
  have hn' : 2 * n < 2048 := hn
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  by_cases hc : (core.get s a).toNat < (core.get s b).toNat
  · rw [if_pos hc]
    obtain ⟨s', hx⟩ := G.bltu_t h hpc hok (phys a) (phys b) _ hi hc
    rw [boff_fwd n hn'] at hx
    exact run1 hx ⟨ofNext hx (.inl rfl), sameOf hx, memOf hx⟩
  · rw [if_neg hc]
    obtain ⟨s', hx⟩ := G.bltu_n h hpc hok (phys a) (phys b) _ hi hc
    exact run1 hx ⟨ofNext hx (.inl rfl), sameOf hx, memOf hx⟩

theorem law_bgeu {a b : Reg} {n : Nat} {s : St} {pc : BitVec 64} (hn : core.bzOK n)
    (hA : core.At s pc (encK (.bgeu a b n))) :
    core.runsTo s fun s' => core.Done s s'
        (if (core.get s b).toNat ≤ (core.get s a).toNat then next pc n else next pc 1) ∧
      core.Same s s' ∧ core.mem s' = core.mem s := by
  have hn' : 2 * n < 2048 := hn
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  by_cases hc : (core.get s b).toNat ≤ (core.get s a).toNat
  · rw [if_pos hc]
    have hc' : (getX s (phys b)).toNat ≤ (getX s (phys a)).toNat := hc
    obtain ⟨s', hx⟩ := G.bgeu_t h hpc hok (phys a) (phys b) _ hi (by omega)
    rw [boff_fwd n hn'] at hx
    exact run1 hx ⟨ofNext hx (.inl rfl), sameOf hx, memOf hx⟩
  · rw [if_neg hc]
    have hc' : ¬(getX s (phys b)).toNat ≤ (getX s (phys a)).toNat := hc
    obtain ⟨s', hx⟩ := G.bgeu_n h hpc hok (phys a) (phys b) _ hi (by omega)
    exact run1 hx ⟨ofNext hx (.inl rfl), sameOf hx, memOf hx⟩

theorem law_getFr {d : Reg} {s : St} {pc : BitVec 64} (hd : d.val < 7) (hA : core.At s pc (encK (.getFr d))) :
    core.runsTo s fun s' => core.Done s s' (next pc (encK (.getFr d)).length) ∧
      core.Set1 s s' d (getX s 3) ∧ core.mem s' = core.mem s := by
  obtain ⟨h, hpc, hok, hi⟩ := first1 hA
  obtain ⟨s', hn⟩ := G.step_addi h hpc hok (phys d) 3 0 hi
  rw [sx_0, BitVec.add_zero] at hn
  exact run1 hn ⟨ofNext hn (.inr ⟨d, rfl⟩), set1Of hn, memOf hn⟩

theorem law_getTop {d : Reg} {s : St} {pc : BitVec 64} (hd : d.val < 7) (hen : FrOK 0 (frameBase 0 (getX s 2)))
    (hA : core.At s pc (encK (.getTop d))) :
    core.runsTo s fun s' => core.Done s s' (next pc (encK (.getTop d)).length) ∧
      core.Set1 s s' d (BitVec.ofNat 64 (frameBase 0 (getX s 2))) ∧ core.mem s' = core.mem s := by
  obtain ⟨h, hpc, hok, hi⟩ := first hA
  obtain ⟨s₁, hn₁⟩ := G.step_srli h hpc hok (phys d) 2 3#6 hi
  have sp := Core.At.split _ (l₁ := [encI 5 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) (phys d) 2])
    (l₂ := [encI 1 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) (phys d) (phys d), encI 0 im8.toNat (phys d) (phys d)]) hA
  have hA₁ : core.At s₁ (next pc 1) [encI 1 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) (phys d) (phys d),
      encI 0 im8.toNat (phys d) (phys d)] :=
    ⟨hn₁.cfg, hn₁.pc, core.codeAt_mem (memOf hn₁) sp.2.1, sp.2.2⟩
  obtain ⟨h', hpc', hok', hi'⟩ := first hA₁
  obtain ⟨s₂, hn₂⟩ := G.step_slli h' hpc' hok' (phys d) (phys d) 3#6 hi'
  have sp2 := Core.At.split _ (l₁ := [encI 1 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) (phys d) (phys d)])
    (l₂ := [encI 0 im8.toNat (phys d) (phys d)]) hA₁
  have hA₂ : core.At s₂ (next (next pc 1) 1) [encI 0 im8.toNat (phys d) (phys d)] :=
    ⟨hn₂.cfg, hn₂.pc, core.codeAt_mem (memOf hn₂) sp2.2.1, sp2.2.2⟩
  obtain ⟨h'', hpc'', hok'', hi''⟩ := first1 hA₂
  obtain ⟨s₃, hn₃⟩ := G.step_addi h'' hpc'' hok'' (phys d) (phys d) im8 hi''
  rw [sx_im8] at hn₃
  have g₁ : getX s₁ (phys d) = getX s 2 >>> (3#6 : BitVec 6).toNat := by
    rw [hn₁.x]; exact ite_pos ⟨rfl, phys_ne0 d⟩
  have g₂ : getX s₂ (phys d) = (getX s 2 >>> (3#6 : BitVec 6).toNat) <<< (3#6 : BitVec 6).toNat := by
    rw [hn₂.x, ite_pos ⟨rfl, phys_ne0 d⟩, g₁]
  rw [g₂] at hn₃
  have hlo := hen.lo
  have hfb : 8 ≤ (getX s 2).toNat / 8 * 8 := by unfold frameBase at hlo; omega
  rw [frameBase_bv _ hfb] at hn₃
  refine runsTo_next hn₁ (runsTo_next hn₂ (run1 hn₃ ⟨⟨hn₃.cfg, fun j hj => ?_, ?_⟩, fun r => ?_, ?_⟩))
  · show getX s₃ j = getX s j
    rw [hn₃.x j, ite_neg (fun e => hj d e.1), hn₂.x j, ite_neg (fun e => hj d e.1), hn₁.x j]
    exact ite_neg (fun e => hj d e.1)
  · have := hn₃.pc; rwa [n4 (next (next pc 1) 1), next_add, next_add] at this
  · show getX s₃ (phys r) = if r = d then _ else getX s (phys r)
    rw [hn₃.x]
    by_cases hr : r = d
    · subst hr; rw [ite_pos ⟨rfl, phys_ne0 r⟩, ite_pos rfl]
    · have hne : phys r ≠ phys d := fun e => hr (phys_inj _ _ e)
      rw [ite_neg (fun e => hne e.1), ite_neg hr, hn₂.x, ite_neg (fun e => hne e.1), hn₁.x,
        ite_neg (fun e => hne e.1)]
  · exact (memOf hn₃).trans ((memOf hn₂).trans (memOf hn₁))

theorem phys_avar0 : phys (avar 0) = 10 := by decide

theorem law_exit {s : St} {pc w : BitVec 64} (hA : core.At s pc (encK .exit)) (h8 : 8 ≤ frameBase 0 (getX s 2))
    (hr : core.inRAM (frameBase 0 (getX s 2) - 8) 8) (hal : (frameBase 0 (getX s 2) - 8) % 8 = 0)
    (hb : bytes (core.mem s) (frameBase 0 (getX s 2) - 8) 8 = (le8 w).map some) (hw : core.retOK w) :
    core.runsTo s fun s' => core.ok s' ∧ core.pcIs s' w ∧ core.get s' (avar 0) = BitVec.allOnes 64 ∧
      core.mem s' = core.mem s := by
  obtain ⟨h, hpc, hok, hi⟩ := first hA
  obtain ⟨s₀, hn₀⟩ := G.step_srli h hpc hok 5 2 3#6 hi
  have sp0 := Core.At.split _ (l₁ := [encI 5 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) 5 2])
    (l₂ := [encI 1 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) 5 5, G.encL 3 im16 1 5, encI 0 im1.toNat 10 0, iRet]) hA
  have hA₀ : core.At s₀ (next pc 1) [encI 1 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) 5 5, G.encL 3 im16 1 5,
      encI 0 im1.toNat 10 0, iRet] :=
    ⟨hn₀.cfg, hn₀.pc, core.codeAt_mem (memOf hn₀) sp0.2.1, sp0.2.2⟩
  obtain ⟨h0, hpc0, hok0, hi0⟩ := first hA₀
  obtain ⟨s₁, hn₁⟩ := G.step_slli h0 hpc0 hok0 5 5 3#6 hi0
  have sp1 := Core.At.split _ (l₁ := [encI 1 (0 <<< 6 ||| (3#6 : BitVec 6).toNat) 5 5])
    (l₂ := [G.encL 3 im16 1 5, encI 0 im1.toNat 10 0, iRet]) hA₀
  have hA₁ : core.At s₁ (next (next pc 1) 1) [G.encL 3 im16 1 5, encI 0 im1.toNat 10 0, iRet] :=
    ⟨hn₁.cfg, hn₁.pc, core.codeAt_mem (memOf hn₁) sp1.2.1, sp1.2.2⟩
  have g5 : getX s₁ 5 = (getX s 2 >>> (3#6 : BitVec 6).toNat) <<< (3#6 : BitVec 6).toNat := by
    rw [hn₁.x, ite_pos ⟨rfl, by decide⟩, hn₀.x, ite_pos ⟨rfl, by decide⟩]
  obtain ⟨h1, hpc1, hok1, hi1⟩ := first hA₁
  have hfb : 8 ≤ (getX s 2).toNat / 8 * 8 - 8 := by unfold frameBase at h8; omega
  have haddr : getX s₁ 5 + im16.signExtend 64 = BitVec.ofNat 64 (frameBase 0 (getX s 2) - 8) := by
    rw [g5, sx_im16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, shr_shl_toNat, BitVec.toNat_ofNat, frameBase]
    have := (getX s 2).isLt
    rw [BitVec.toNat_ofNat]
    omega
  have hA8 : (BitVec.ofNat 64 (frameBase 0 (getX s 2) - 8)).toNat = frameBase 0 (getX s 2) - 8 := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; unfold Base.inRAM at hr; have : core.ramHi = 0x100000000 := rfl
    omega
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := bytesAt_le8 (bytes_le8 hb)
  obtain ⟨s₂, hn₂⟩ := G.step_ld h1 hpc1 hok1 1 5 im16 hi1 haddr (by rw [hA8]; exact hr) (by rw [hA8]; exact hal)
    (by rw [hn₁.mem, hn₀.mem, hA8]; exact b0) (by rw [hn₁.mem, hn₀.mem, hA8]; exact b1)
    (by rw [hn₁.mem, hn₀.mem, hA8]; exact b2) (by rw [hn₁.mem, hn₀.mem, hA8]; exact b3)
    (by rw [hn₁.mem, hn₀.mem, hA8]; exact b4) (by rw [hn₁.mem, hn₀.mem, hA8]; exact b5)
    (by rw [hn₁.mem, hn₀.mem, hA8]; exact b6) (by rw [hn₁.mem, hn₀.mem, hA8]; exact b7)
  rw [Proven.le8_cat] at hn₂
  have sp2 := Core.At.split _ (l₁ := [G.encL 3 im16 1 5]) (l₂ := [encI 0 im1.toNat 10 0, iRet]) hA₁
  have hA₂ : core.At s₂ (next (next (next pc 1) 1) 1) [encI 0 im1.toNat 10 0, iRet] :=
    ⟨hn₂.cfg, hn₂.pc, core.codeAt_mem (memOf hn₂) sp2.2.1, sp2.2.2⟩
  obtain ⟨h2, hpc2, hok2, hi2⟩ := first hA₂
  obtain ⟨s₃, hn₃⟩ := G.step_addi h2 hpc2 hok2 10 0 im1 hi2
  rw [sx_im1] at hn₃
  have sp3 := Core.At.split _ (l₁ := [encI 0 im1.toNat 10 0]) (l₂ := [iRet]) hA₂
  have hA₃ : core.At s₃ (next (next (next (next pc 1) 1) 1) 1) [iRet] :=
    ⟨hn₃.cfg, hn₃.pc, core.codeAt_mem (memOf hn₃) sp3.2.1, sp3.2.2⟩
  obtain ⟨h3, hpc3, hok3, hi3⟩ := first1 hA₃
  have g1 : getX s₃ 1 = w := by
    rw [hn₃.x, ite_neg (by decide), hn₂.x]; exact ite_pos ⟨rfl, by decide⟩
  obtain ⟨s₄, hn₄⟩ := step_ret h3 hpc3 hok3 hi3 (by rw [g1]; exact hw)
  refine runsTo_next hn₀ (runsTo_next hn₁ (runsTo_next hn₂ (runsTo_next hn₃ (run1 hn₄ ⟨hn₄.cfg, ?_, ?_, ?_⟩))))
  · have := hn₄.pc; rwa [g1] at this
  · show getX s₄ (phys (avar 0)) = _
    rw [phys_avar0, hn₄.x, ite_neg (by decide), hn₃.x, ite_pos ⟨rfl, by decide⟩, Proven.G.getX_zero]
    decide
  · exact (memOf hn₄).trans ((memOf hn₃).trans ((memOf hn₂).trans ((memOf hn₁).trans (memOf hn₀))))

/-- **The Sail RV64 model is a `MachineM`.** -/
def rvM : MachineM where
  toMachineC := rvC
  encM := encK
  lenBr := 1
  len_bltu _ _ _ := rfl
  len_bgeu _ _ _ := rfl
  law_bltu := law_bltu
  law_bgeu := law_bgeu
  law_getFr := law_getFr
  law_getTop hd hen hA := law_getTop hd hen hA
  law_exit := law_exit
  frameAt_keepC {s s' n} h := by
    show frameBase n (getX s' 2) = frameBase n (getX s 2)
    rw [h 2 (by decide) (by decide) (by decide)]
  enterOK_keep {s s' n} h hen := by
    show FrOK n (frameBase n (getX s' 2))
    rw [show getX s' 2 = getX s 2 from h 2 (by decide)]; exact hen

end Proven.Mach.Riscv
