/- The middle layer instantiated at the AlphaProof-Code AArch64 user-mode semantics:
expressions, loops (gcd), byte arrays (insertion sort). -/
import Apc.Mach
import Apc.Src.Loop
import Apc.Src.SortIns
namespace Proven.Apc
open Proven Proven.Mach

theorem xr_v4 : ∀ i : Fin 4, xr (v4 i) = BitVec.ofNat 5 i.val := by decide
/-- a fixed layout: side conditions on code sizes do not depend on the layout -/
def L0 : Lay := ⟨0, 0, 0, 0, by decide⟩

/-- **Expressions.**  Code of `e` at `pc` (inside the executable code range), arguments in x0..x3:
the run returns to x30 with x0 = `e.denote`, memory and sp unchanged. -/
theorem compile_apc (L : Lay) (e : Exp) (he : e.depth < 11) {s : Arm64.State} {pc : BitVec 64}
    (hA : (apc L).At s pc ((apc L).code (mcompile e))) :
    ∃ s', Arm64.Steps P s s' ∧ s'.pc = s.regs.read 30#5 ∧
      s'.regs.read 0#5 = e.denote (fun i => s.regs.read (BitVec.ofNat 5 i.val)) ∧
      s'.status = .Running ∧ memV s' = memV s ∧ s'.sp = s.sp := by
  obtain ⟨s', hs, h1, h2, h3, h4, h5⟩ := (apc L).compile_ok e he hA trivial
  refine ⟨s', hs, h1, ?_, h3.1, h4, h5.2⟩
  have e0 : (apc L).get s' (rk 11) = s'.regs.read 0#5 := rfl
  have ev : (fun i => (apc L).get s (v4 i)) = fun i : Fin 4 => s.regs.read (BitVec.ofNat 5 i.val) := by
    funext i; show s.regs.read (xr (v4 i)) = _; rw [xr_v4]
  rw [← e0, h2, ev]

theorem gcd_wf0 : (apc L0).wf gcdProg := by
  simp only [gcdProg, Machine.wf]
  refine ⟨⟨by decide, ⟨by decide, by decide, by decide⟩, ?_, ?_⟩, by decide⟩ <;> (show _ < 1024; decide +kernel)
theorem gcd_wf (L : Lay) : (apc L).wf gcdProg := gcd_wf0

/-- **gcd** (a loop): x0 := gcd(x0, x1) by repeated subtraction. -/
theorem gcd_apc (L : Lay) {s : Arm64.State} {pc : BitVec 64}
    (hA : (apc L).At s pc ((apc L).code ((apc L).compF gcdProg))) :
    ∃ s', Arm64.Steps P s s' ∧ s'.pc = s.regs.read 30#5 ∧
      s'.regs.read 0#5 = gcdSub (s.regs.read 0#5) (s.regs.read 1#5) ∧
      s'.status = .Running ∧ memV s' = memV s ∧ s'.sp = s.sp := by
  obtain ⟨σ', hex, hv⟩ := gcdProg_exec (fun i => (apc L).get s (v4 i))
  obtain ⟨s', hs, h1, h2, h3, h4, h5⟩ := (apc L).compF_ok (gcd_wf L) hex hA trivial
  exact ⟨s', hs, h1, (h2 0).trans hv, h3.1, h4, h5.2⟩

theorem sort_wf0 : (apc L0).wfA [0, 3] sortProg := by
  simp only [sortProg, insProg, outerBody, innerBody, mapProg, idxE, cE, valE, Machine.wfA]
  repeat' apply And.intro
  all_goals first | decide | (show _ < 1024; decide +kernel)
theorem sort_wf (L : Lay) : (apc L).wfA [0, 3] sortProg := sort_wf0

/-- the compiled insertion sort for this target -/
def sortCode : List (BitVec 32) := (apc L0).code ((apc L0).compAF [0, 3] sortProg)

set_option maxRecDepth 100000 in
/-- **Insertion sort on the AlphaProof-Code user-mode semantics** (memory/region form, the shape of
`sortCode_ok_m`).  The code is at `pc` inside the executable range; input `xs` at x0 (length in x1) and an output
block of `|xs|` bytes at x3 (any contents), both inside the writable data range, disjoint from each other and from
the code.  The run returns to x30 with the output block holding `xs.mergeSort`, the input unchanged, every byte
outside the two blocks unchanged, status `Running`, sp unchanged. -/
theorem sort_apc (L : Lay) {s : Arm64.State} {pc : BitVec 64} (hA : (apc L).At s pc ((apc L).code ((apc L).compAF [0, 3] sortProg)))
    {xs out : List (BitVec 8)} {inb outb : Nat} (hd : L.dHi < 2 ^ 63)
    (hi : L.dLo ≤ inb ∧ inb + xs.length ≤ L.dHi) (ho' : L.dLo ≤ outb ∧ outb + xs.length ≤ L.dHi)
    (hio : disjoint ⟨inb, xs.length⟩ ⟨outb, xs.length⟩)
    (hcd : ∀ r ∈ [(⟨inb, xs.length⟩ : Region), ⟨outb, xs.length⟩], disjoint ⟨pc.toNat, 4 * ((apc L).code ((apc L).compAF [0, 3] sortProg)).length⟩ r)
    (h0 : s.regs.read 0#5 = BitVec.ofNat 64 inb) (h1 : s.regs.read 1#5 = BitVec.ofNat 64 xs.length)
    (h3 : s.regs.read 3#5 = BitVec.ofNat 64 outb)
    (hx : bytes (memV s) inb xs.length = xs.map some) (ho : bytes (memV s) outb xs.length = out.map some) :
    ∃ s', Arm64.Steps P s s' ∧ s'.pc = s.regs.read 30#5 ∧
      bytes (memV s') outb xs.length = (xs.mergeSort leB).map some ∧
      bytes (memV s') inb xs.length = xs.map some ∧
      Out [⟨inb, xs.length⟩, ⟨outb, xs.length⟩] (memV s) (memV s') ∧ s'.status = .Running ∧ s'.sp = s.sp := by
  obtain ⟨hi1, hi2⟩ := hi
  obtain ⟨ho1, ho2⟩ := ho'
  have hn : xs.length < 2 ^ 63 := by omega
  have hout : out.length = xs.length := by simpa [length_bytes] using (congrArg List.length ho).symm
  have hR : (apc L).RegOK [⟨inb, xs.length⟩, ⟨outb, xs.length⟩] := by
    refine ⟨fun r hr => ?_, by simpa using hio, fun r hr a h1 h2 _ _ => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨Nat.zero_le _, by show inb + xs.length ≤ 2 ^ 64 - 1; omega⟩
      · exact ⟨Nat.zero_le _, by show outb + xs.length ≤ 2 ^ 64 - 1; omega⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨by show L.dLo ≤ a; dsimp only at h1 h2; omega, by show a < L.dHi; dsimp only at h1 h2; omega⟩
      · exact ⟨by show L.dLo ≤ a; dsimp only at h1 h2; omega, by show a < L.dHi; dsimp only at h1 h2; omega⟩
  obtain ⟨σ', hex, hh⟩ := sortProg_mergeSort xs out ⟨fun i => (apc L).get s (avar i), [xs, out]⟩ rfl h1 hn hout
  have hrel : (apc L).Rel [0, 3] [⟨inb, xs.length⟩, ⟨outb, xs.length⟩] ⟨fun i => (apc L).get s (avar i), [xs, out]⟩ s :=
    ⟨fun _ => rfl, rfl, rfl, fun b hb => by obtain _ | _ | b := b; exact h0; exact h3; simp at hb; omega,
      fun b hb => by obtain _ | _ | b := b; rfl; exact hout; simp at hb; omega,
      fun b hb => by obtain _ | _ | b := b; exact hx; exact ho; simp at hb; omega⟩
  obtain ⟨s', hs, p1, p2, p3, p4, p5⟩ := (apc L).compAF_ok [0, 3] (sort_wf L) hR hex hA hcd hrel trivial
  have e0 := p2.bytes 0 (by simp); have e1 := p2.bytes 1 (by simp)
  simp only [hh] at e0 e1
  have em : (apc L).mem s' = memV s' := rfl
  rw [em] at e0 e1
  exact ⟨s', hs, p1, by simpa using e1, by simpa using e0, p3, p4.1, p5.2⟩

#print axioms compile_apc
#print axioms gcd_apc
#print axioms sort_apc
end Proven.Apc
