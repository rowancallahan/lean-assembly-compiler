/- Theorems about the allocator specification `Spec/Alloc.lean` (the definitions moved there, 2026-11-19). -/
import Spec.Alloc

namespace Proven.Top.Alloc

/-- an address outside the whole output block is outside the result prefix -/
theorem outside_prefix {address output : UInt64} {n m : Nat} (hnm : n ≤ m) (h : Outside address (output, m)) :
    Outside address (output, n) := by
  unfold Outside at *; dsimp only at *; omega

theorem CompileRuns.weak {P : Type} [Program P] {machine : Machine} {compile : P → Option CompiledA}
    (h : CompileRuns machine compile) : CompileRunsWeak machine compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call hc hf hs ho
  obtain ⟨finishState, hr, hpc, hm, hflag, -, -⟩ := h program compiled f encodeInput encodeOutput argument
    startState call hc hf hs ho
  exact ⟨finishState, hr, hpc, fun a h1 h2 => hm a (outside_prefix ho h1) h2, hflag⟩

theorem CompileCorrect.weak {P : Type} [Program P] {machine : Machine} {compile : P → Option CompiledA}
    (h : CompileCorrect machine compile) : CompileCorrectWeak machine compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call hc hf hs ho hmem
  obtain ⟨finishState, hr, hpc, hflag, hread, -⟩ := h program compiled f encodeInput encodeOutput argument
    startState call hc hf hs ho hmem
  exact ⟨finishState, hr, hpc, hflag, hread⟩

end Proven.Top.Alloc
