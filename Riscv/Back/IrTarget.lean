/- The RISC-V instance of the IR target interface (`Compiler/Ir/Target.lean`): `rvT`, assembled from the existing
step lemmas: the wide operations with a frame (`rvwF`, `Riscv/Back/OptB.lean`) and `getTop`
(`andi d, sp, -8; addi d, d, -8`, `Riscv/Back/MemRv.lean`).  No new Sail reasoning. -/
import Compiler.Ir.Emit
import Riscv.Back.OptB
import Riscv.Back.MemRv
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

end Proven.Mach.Riscv
