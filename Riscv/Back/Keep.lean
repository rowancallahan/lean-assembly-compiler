/- Variants of the RISC-V corollaries that keep the full register frame (`rv.keep`) in the conclusion,
for the ABI clause of `Implements1` (`abiSavedKept`: `sp`, `gp`, `tp`, `s0..s11`). -/
import Riscv.Back.Arr
import Spec.Implements1

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv

/-- `keep` (all registers outside the abstract ones) gives the ABI-preserved registers -/
theorem abi_of_keep {s s' : St} (h : Cfg s) (h₃ : Cfg s') (f : rv.keep s s') : abiSavedKept s s' := by
  have k : ∀ j ∈ ([2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] : List (Fin 32)), getX s' j = getX s j :=
    fun j hj => f j (by revert j; decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₃.x2, h.x2, k 2 (by decide)]
  · rw [h₃.x3, h.x3, k 3 (by decide)]
  · rw [h₃.x4, h.x4, k 4 (by decide)]
  · rw [h₃.x8, h.x8, k 8 (by decide)]
  · rw [h₃.x9, h.x9, k 9 (by decide)]
  · rw [h₃.x18, h.x18, k 18 (by decide)]
  · rw [h₃.x19, h.x19, k 19 (by decide)]
  · rw [h₃.x20, h.x20, k 20 (by decide)]
  · rw [h₃.x21, h.x21, k 21 (by decide)]
  · rw [h₃.x22, h.x22, k 22 (by decide)]
  · rw [h₃.x23, h.x23, k 23 (by decide)]
  · rw [h₃.x24, h.x24, k 24 (by decide)]
  · rw [h₃.x25, h.x25, k 25 (by decide)]
  · rw [h₃.x26, h.x26, k 26 (by decide)]
  · rw [h₃.x27, h.x27, k 27 (by decide)]

/-- `compileAF_ok'` with the full frame `keep` (every register outside the abstract ones) in the conclusion -/
theorem compileAF_okK (bv : List (Fin 8)) {p : AStmt} (hp : p.wf bv) {R : List Proven.Region} (hR : Proven.RegOK R)
    {σ σ' : AState} (hex : AExec p σ σ') {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compileAF bv p)) (hok : codeOK pc (compileAF bv p).length)
    (hcd : ∀ r ∈ R, Proven.disjoint ⟨pc.toNat, 4 * (compileAF bv p).length⟩ r) (hrel : Proven.Rel bv R σ s)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      Proven.Rel bv R σ' s' ∧ unchangedOutside s s' R ∧ Cfg s' ∧ rv.keep s s' := by
  have ec := code_compAF bv p hp
  rw [← ec] at hc hok hcd
  have hcd' : ∀ r ∈ R.map toR, disjoint ⟨pc.toNat, 4 * (rv.code (rv.compAF bv p)).length⟩ r := fun r hr => by
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr; exact hcd r' hr'
  refine runsTo_mono (rv.compAF_ok bv (code_compA bv p hp).2 (regOK_toR hR) hex ⟨h, hpc, hc, hok⟩ hcd'
    (rel_toR hrel) hra) fun s' ⟨p1, p2, p3, p4, p5⟩ => ⟨p1, rel_ofR p2, fun a ha => p3 a fun r hr => by
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr; exact ha r' hr', p4, p5⟩

end Proven.Mach.Riscv

namespace Proven

theorem sortCode_ok_k {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc sortCode) (hok : codeOK pc sortCode.length) (hra : (getX s 1).toNat % 2 = 0)
    {xs out : List (BitVec 8)} {inb outb : Nat} (hR : RegOK [⟨inb, xs.length⟩, ⟨outb, xs.length⟩])
    (hcd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨outb, xs.length⟩], disjoint ⟨pc.toNat, 4 * sortCode.length⟩ r)
    (h0 : getX s 10 = BitVec.ofNat 64 inb) (h1 : getX s 11 = BitVec.ofNat 64 xs.length)
    (h3 : getX s 13 = BitVec.ofNat 64 outb)
    (hx : bytesAt s inb xs.length = xs.map some) (ho : bytesAt s outb xs.length = out.map some) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      bytesAt s' outb xs.length = (xs.mergeSort leB).map some ∧
      bytesAt s' inb xs.length = xs.map some ∧ unchangedOutside s s' [⟨outb, xs.length⟩] ∧
      Cfg s' ∧ Mach.Riscv.rv.keep s s' := by
  have hn : xs.length < 2 ^ 63 := by
    have := hR.1 _ (List.mem_cons_self ..); unfold Region.inRAM at this; dsimp only at this; omega
  have hout : out.length = xs.length := by simpa [bytesAt] using (congrArg List.length ho).symm
  obtain ⟨σ', hex, hh⟩ := sortProg_mergeSort xs out ⟨fun i => getX s (A8 i), [xs, out]⟩ rfl h1 hn hout
  have hrel : Rel [0, 3] [⟨inb, xs.length⟩, ⟨outb, xs.length⟩] ⟨fun i => getX s (A8 i), [xs, out]⟩ s :=
    ⟨fun _ => rfl, rfl, rfl, fun b hb => by obtain _ | _ | b := b; exact h0; exact h3; simp at hb; omega,
      fun b hb => by obtain _ | _ | b := b; rfl; exact hout; simp at hb; omega,
      fun b hb => by obtain _ | _ | b := b; exact hx; exact ho; simp at hb; omega⟩
  refine runsTo_mono (Mach.Riscv.compileAF_okK [0, 3] sortProg_wf hR hex h hpc hc hok hcd hrel hra) ?_
  rintro s' ⟨p1, p2, p3, p4, p5⟩
  have e0 := p2.bytes 0 (by simp); have e1 := p2.bytes 1 (by simp)
  simp only [hh] at e0 e1
  exact ⟨p1, by simpa using e1, by simpa using e0, unchanged_drop p3 (by simpa [hx] using e0), p4, p5⟩

end Proven
