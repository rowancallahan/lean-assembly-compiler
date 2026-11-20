/- The RISC-V instance of the IR target interface (`Compiler/Ir/Target.lean`): `rvT`, assembled from the existing
step lemmas: the wide operations with a frame (`rvwF`, `Riscv/Back/OptB.lean`) and `getTop`
(`andi d, sp, -8; addi d, d, -8`, `Riscv/Back/MemRv.lean`).  No new Sail reasoning. -/
import Legacy.Compiler.Ir.Emit
import Nano.Base.Riscv.Back.OptB
import Legacy.Riscv.Back.MemRv
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv
open Proven.Ir

theorem phys_ne2 : ∀ r : Reg, (2 : Fin 32) ≠ phys r := by decide

/-- **The Sail RV64 model is an IR target.** -/
def rvT : Target where
  toWideF := rvwF
  top s := (getX s 2).toNat / 8 * 8
  encT d := encK (.getTop d)
  t_top hd h16 hA := by
    have := law_getTop hd (by unfold frameBase; omega) hA
    exact this
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
  encX := encK .exit
  c_exit {s pc w} hA h16 hr hal hb hw := by
    have e : frameBase 0 (getX s 2) - 8 = (getX s 2).toNat / 8 * 8 - 16 := by unfold frameBase; omega
    have h16' : 16 ≤ (getX s 2).toNat / 8 * 8 := h16
    refine core.runsTo_mono (law_exit hA (by unfold frameBase; omega) (by rw [e]; exact hr) (by rw [e]; exact hal)
      (by rw [e]; exact hb) hw) fun s' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩

end Proven.Mach.Riscv
