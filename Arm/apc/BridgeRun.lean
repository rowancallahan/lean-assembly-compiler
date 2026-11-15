/- Run-level corollary on the Sail model: a program proved on DeepMind's semantics whose words are all bridged
(`brW`) runs the same way on Sail ARMv9 (full `stepModel` steps). Instance: `gcd_apc` (subtractive gcd loop). -/
import Br.BridgeBr
import Apc.Stack
open Armv9 Armv9.Functions Sail Sail.ConcurrencyInterfaceV1
set_option maxRecDepth 100000
set_option linter.all false
namespace ArmProof
open Proven Proven.Apc Proven.Mach

/-- `CodeOK` from the program: the only executable aligned DeepMind words are the program `ws` at `pc`, Sail holds the
same words there (below `2^29`), and every word of `ws` is bridged -/
theorem codeOK_of {L : Lay} {s : St} {t : Arm64.State} {pc : BitVec 64} {ws : List (BitVec 32)}
    (hc : (base L).codeAt t pc ws) (hS : CodeAt s.mem pc.toNat ws) (hlt : pc.toNat + 4 * ws.length < 2 ^ 29)
    (hb : ∀ w ∈ ws, brW w = true)
    (hX : ∀ a : BitVec 64, a.toNat % 4 = 0 → t.mem.canExec a 4 = true →
      ∃ i < ws.length, a = pc + BitVec.ofNat 64 (4 * i)) : CodeOK s t := by
  intro a ha hx
  obtain ⟨i, hi, rfl⟩ := hX a ha hx
  have e : (pc + BitVec.ofNat 64 (4 * i)).toNat = pc.toNat + 4 * i := by simp [BitVec.toNat_add]; omega
  rw [instr_read32 (hc i hi), e]
  exact ⟨by omega, hS i hi, hb _ (List.getElem_mem _)⟩

theorem gcd_words0 : ((apc L0).code ((apc L0).compF gcdProg)).all brW = true := by decide +kernel
theorem gcd_words (L : Lay) : ∀ w ∈ (apc L).code ((apc L).compF gcdProg), brW w = true :=
  List.all_eq_true.mp gcd_words0

/-- **gcd on Sail ARMv9, end to end**: from a Sail state related to a DeepMind state that is about to run the gcd
code (the `gcd_apc` hypothesis), with the same words in Sail memory and no other executable memory, full Sail
steps reach `PC = x30` with `x0 = gcdSub x0 x1`, `ArmFull` again and the memory unchanged. -/
theorem gcd_sail (L : Lay) {t : Arm64.State} {pc : BitVec 64}
    (hA : (apc L).At t pc ((apc L).code ((apc L).compF gcdProg))) {s : St} (hR : Rel s t)
    (hS : CodeAt s.mem pc.toNat ((apc L).code ((apc L).compF gcdProg)))
    (hlt : pc.toNat + 4 * ((apc L).code ((apc L).compF gcdProg)).length < 2 ^ 29)
    (hX : ∀ a : BitVec 64, a.toNat % 4 = 0 → t.mem.canExec a 4 = true →
      ∃ i < ((apc L).code ((apc L).compF gcdProg)).length, a = pc + BitVec.ofNat 64 (4 * i)) :
    ∃ n s', ArmSteps n s s' ∧ s'.regs.get? ._PC = some (t.regs.read 30#5) ∧
      xget s'.regs 0 = some (gcdSub (t.regs.read 0#5) (t.regs.read 1#5)) ∧ ArmFull s' ∧ s'.mem = s.mem := by
  obtain ⟨t', hs, h1, h2, h3, -, -⟩ := gcd_apc L hA
  have hC := codeOK_of hA.code hS hlt (gcd_words L) hX
  obtain ⟨n, s', h, hR', hm, -⟩ := sim hs h3 hR hC
  refine ⟨n, s', h, by rw [hR'.pc, h1], ?_, hR'.full, hm⟩
  rw [hR'.abs.x 0 (by decide), ← h2]; rfl

#print axioms sim
#print axioms gcd_sail
end ArmProof
