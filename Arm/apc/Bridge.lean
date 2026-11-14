/- The bridge: on every emitted word, one step of the AlphaProof-Code semantics and one full step of the Sail
ARMv9.4-A model (`stepModel`, under `ArmFull`) from related states end in related states.
Composition of `ArmProof.full_word` (Arm/proofs/Arm/Full.lean) and `agree_emitted` (apc/Apc/AgreeAll.lean).
Checked by apc/bridge.sh (file kept as .txt so that the apc lake package, which has no Sail model, ignores it). -/
import Arm.Full
import Br.AgreeAll
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
namespace ArmProof
open Proven.Apc

theorem apc_eq_sail {w : BitVec 32} (hw : w ∈ emitted) {s : St} {t : Arm64.State} (hf : ArmFull s)
    (ha : Abs s (Proven.Apc.abs t)) (hpc : s.regs.get? ._PC = some t.pc) (hlt : t.pc.toNat < 2 ^ 29)
    (hal : t.pc.toNat % 4 = 0) (hm : MemWord s.mem t.pc.toNat w)
    (hrun : t.status = .Running) (hx : t.mem.canExec t.pc 4 = true) (hr : t.mem.read32 t.pc = w) :
    ∃ s' t', stepModel s = .ok () s' ∧ Arm64.Step Pg t t' ∧ Abs s' (Proven.Apc.abs t') ∧ ArmFull s' ∧
      s'.regs.get? ._PC = some t'.pc ∧ s'.mem = s.mem ∧ t'.mem = t.mem := by
  obtain ⟨i, hd, hag⟩ := agree_emitted w hw
  obtain ⟨s', h1, h2, h3, h4, h5⟩ := full_word hw hf ha hpc hlt hal hm
  obtain ⟨g1, g2, g3, -, -⟩ := hag t
  refine ⟨s', Pg.evalInst i t, h1, ?_, by rw [g1]; exact h2, h3, by rw [g2]; exact h4, h5, g3⟩
  refine .exec hrun ?_
  have he : Pg.externAt? t.pc = none := rfl
  unfold Arm64.Program.fetchMem
  rw [he]
  simp [hal, hx, hr, hd]

#print axioms apc_eq_sail
end ArmProof
