/- Drop-in replacements for the generated `Riscv/Legacy/Steps/Arr2Words.lean` lemmas the proofs use (same names
and statements), as instances of `Riscv/Steps/GenMem.lean` / `GenALU.lean`.  Not provided: the per-slot
instances `W2.ldS_*`/`W2.sdS_*` (only the dispatchers `step_ldS`/`step_sdS` were used). -/
import Riscv.Direct.Arr2Code
import Riscv.Steps.Arr2Step
import Riscv.Steps.Compat
import Riscv.Steps.MemSteps
import Riscv.Steps.Imm12
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven

open Compat

namespace W2
theorem sdGp {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x0032b023#32) (ha : 0x80000000 ≤ (getX s 5).toNat ∧ (getX s 5).toNat + 8 ≤ 0x100000000) (hal : (getX s 5).toNat % 8 = 0) :
    ∃ s', Next s s' (pc + 4) 0 0 (storeBytes s.mem (getX s 5).toNat (le8 (getX s 3))) := by
  rw [show (0x0032b023#32 : BitVec 32) = G.encS 3 0 3 5 by decide] at hi
  exact G.step_sd h hpc hok 3 5 0 hi (addr0 _) ha hal
theorem ldGp {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x0001b183#32) (ha : 0x80000000 ≤ (getX s 3).toNat ∧ (getX s 3).toNat + 8 ≤ 0x100000000) (hal : (getX s 3).toNat % 8 = 0) {b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8}
    (h0 : s.mem[(getX s 3).toNat]? = some b0) (h1 : s.mem[(getX s 3).toNat + 1]? = some b1) (h2 : s.mem[(getX s 3).toNat + 2]? = some b2) (h3 : s.mem[(getX s 3).toNat + 3]? = some b3) (h4 : s.mem[(getX s 3).toNat + 4]? = some b4) (h5 : s.mem[(getX s 3).toNat + 5]? = some b5) (h6 : s.mem[(getX s 3).toNat + 6]? = some b6) (h7 : s.mem[(getX s 3).toNat + 7]? = some b7) :
    ∃ s', Next s s' (pc + 4) 3 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) s.mem := by
  rw [show (0x0001b183#32 : BitVec 32) = G.encL 3 0 3 3 by decide] at hi
  exact G.step_ld h hpc hok 3 3 0 hi (addr0 _) ha hal h0 h1 h2 h3 h4 h5 h6 h7
theorem ldT {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x0002b283#32) (ha : 0x80000000 ≤ (getX s 5).toNat ∧ (getX s 5).toNat + 8 ≤ 0x100000000) (hal : (getX s 5).toNat % 8 = 0) {b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8}
    (h0 : s.mem[(getX s 5).toNat]? = some b0) (h1 : s.mem[(getX s 5).toNat + 1]? = some b1) (h2 : s.mem[(getX s 5).toNat + 2]? = some b2) (h3 : s.mem[(getX s 5).toNat + 3]? = some b3) (h4 : s.mem[(getX s 5).toNat + 4]? = some b4) (h5 : s.mem[(getX s 5).toNat + 5]? = some b5) (h6 : s.mem[(getX s 5).toNat + 6]? = some b6) (h7 : s.mem[(getX s 5).toNat + 7]? = some b7) :
    ∃ s', Next s s' (pc + 4) 5 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) s.mem := by
  rw [show (0x0002b283#32 : BitVec 32) = G.encL 3 0 5 5 by decide] at hi
  exact G.step_ld h hpc hok 5 5 0 hi (addr0 _) ha hal h0 h1 h2 h3 h4 h5 h6 h7
theorem sdT {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc 0x0062b023#32) (ha : 0x80000000 ≤ (getX s 5).toNat ∧ (getX s 5).toNat + 8 ≤ 0x100000000) (hal : (getX s 5).toNat % 8 = 0) :
    ∃ s', Next s s' (pc + 4) 0 0 (storeBytes s.mem (getX s 5).toNat (le8 (getX s 6))) := by
  rw [show (0x0062b023#32 : BitVec 32) = G.encS 3 0 6 5 by decide] at hi
  exact G.step_sd h hpc hok 6 5 0 hi (addr0 _) ha hal
theorem spT {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc iSpT) : ∃ s', Next s s' (pc + 4) 5 (getX s 2) s.mem :=
  mv h hpc hok 5 2 (by decide) hi
theorem gpT {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc) (hi : instrAt s pc iGpT) : ∃ s', Next s s' (pc + 4) 3 (getX s 5) s.mem :=
  mv h hpc hok 3 5 (by decide) hi
end W2

namespace Compat

/-- the slot offsets `8 (j + 1)`, `j < NS`, as 12-bit immediates -/
theorem slot_se (j : Nat) (hj : j < NS) :
    (BitVec.ofNat 12 (8 * (j + 1))).signExtend 64 = BitVec.ofNat 64 (8 * (j + 1)) := by
  simp only [NS] at hj; exact sx12_pos _ (by omega)

theorem iLdS_eq (j k : Nat) (hj : j < NS) : iLdS j k = G.encL 3 (BitVec.ofNat 12 (8 * (j + 1))) (T k) 3 := by
  simp only [NS] at hj
  simp only [iLdS, G.encL, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]; rfl

set_option maxRecDepth 100000 in
theorem iSdS_all : ∀ j : Fin 254, iSdS j.val = G.encS 3 (BitVec.ofNat 12 (8 * (j.val + 1))) 5 3 := by decide

theorem iSdS_eq (j : Nat) (hj : j < NS) : iSdS j = G.encS 3 (BitVec.ofNat 12 (8 * (j + 1))) 5 3 :=
  iSdS_all ⟨j, hj⟩

end Compat

variable {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)
include h hpc hok

/-- `ld t_k, 8(j+1)(gp)` reads the 8 bytes at `A = gp + 8(j+1)` -/
theorem step_ldS (j k : Nat) (hj : j < NS) (hk : k < 7) (hi : instrAt s pc (iLdS j k)) {A : BitVec 64}
    (ha : 0x80000000 ≤ A.toNat ∧ A.toNat + 8 ≤ 0x100000000) (hal : A.toNat % 8 = 0) (hA : getX s 3 + BitVec.ofNat 64 (8 * (j + 1)) = A) {v : BitVec 64}
    (hv : bytesAt s A.toNat 8 = (le8 v).map some) : ∃ s', Next s s' (pc + 4) (T k) v s.mem := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bytesAt_le8 hv
  rw [iLdS_eq j k hj] at hi
  have := G.step_ld h hpc hok (T k) 3 _ hi (by rw [slot_se j hj]; exact hA) ha hal h0 h1 h2 h3 h4 h5 h6 h7
  rwa [le8_cat] at this

/-- `sd t0, 8(j+1)(gp)` -/
theorem step_sdS (j : Nat) (hj : j < NS) (hi : instrAt s pc (iSdS j)) {A : BitVec 64}
    (ha : 0x80000000 ≤ A.toNat ∧ A.toNat + 8 ≤ 0x100000000) (hal : A.toNat % 8 = 0) (hA : getX s 3 + BitVec.ofNat 64 (8 * (j + 1)) = A) :
    ∃ s', Next s s' (pc + 4) 0 0 (storeBytes s.mem A.toNat (le8 (getX s 5))) := by
  rw [iSdS_eq j hj] at hi
  exact G.step_sd h hpc hok 5 3 _ hi (by rw [slot_se j hj]; exact hA) ha hal

/-- `ld rd, 0(rs1)` for `(rd, rs1) = (gp, gp), (t0, t0)`, in `bytesAt` form -/
theorem step_ldGp (hi : instrAt s pc iLdGp) (ha : 0x80000000 ≤ (getX s 3).toNat ∧ (getX s 3).toNat + 8 ≤ 0x100000000)
    (hal : (getX s 3).toNat % 8 = 0) {v : BitVec 64} (hv : bytesAt s (getX s 3).toNat 8 = (le8 v).map some) :
    ∃ s', Next s s' (pc + 4) 3 v s.mem := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bytesAt_le8 hv
  rw [← le8_cat v]; exact W2.ldGp h hpc hok hi ha hal h0 h1 h2 h3 h4 h5 h6 h7
theorem step_ldT (hi : instrAt s pc 0x0002b283#32) (ha : 0x80000000 ≤ (getX s 5).toNat ∧ (getX s 5).toNat + 8 ≤ 0x100000000)
    (hal : (getX s 5).toNat % 8 = 0) {v : BitVec 64} (hv : bytesAt s (getX s 5).toNat 8 = (le8 v).map some) :
    ∃ s', Next s s' (pc + 4) 5 v s.mem := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := bytesAt_le8 hv
  rw [← le8_cat v]; exact W2.ldT h hpc hok hi ha hal h0 h1 h2 h3 h4 h5 h6 h7

end Proven
