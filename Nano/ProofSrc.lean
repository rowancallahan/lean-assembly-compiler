/- nano from source text: `nanoCompileSrcIR src = nanoElab src >>= nanoCompileIR`, with the meaning of a source
`nanoElab` (the spec of nano) followed by `nanoRun`.  `nano_src_correct : CompileCorrect riscv nanoCompileSrcIR` and
`nano_src_runs : CompileRuns riscv nanoCompileSrcIR`, from the theorems on programs (`Nano/ProofTop.lean`). -/
import Nano.ProofTop
import Nano.Elab

set_option linter.unusedVariables false

namespace Nano
open Proven Proven.Mach Proven.Top Proven.Top.Alloc

/-- nano source text (UTF-8 bytes) -/
structure Src where
  bytes : List UInt8

/-- the meaning of a source: elaborate (`nanoElab`, the spec), then run the program -/
def srcRun (s : Src) (input : List UInt8) : Option (List UInt8) := (nanoElab s.bytes).bind fun p => nanoRun p input

instance : Proven.Top.Program Src := ⟨srcRun⟩

/-- **the nano compiler from source text** -/
noncomputable def nanoCompileSrcIR (s : Src) : Option CompiledA := (nanoElab s.bytes).bind nanoCompileIR

theorem src_inv {s : Src} {c : CompiledA} (h : nanoCompileSrcIR s = some c) :
    ∃ p, nanoElab s.bytes = some p ∧ nanoCompileIR p = some c ∧ ∀ input, srcRun s input = nanoRun p input := by
  unfold nanoCompileSrcIR at h
  cases he : nanoElab s.bytes with
  | none => rw [he] at h; exact nomatch h
  | some p => rw [he] at h; exact ⟨p, rfl, h, fun input => by simp [srcRun, he]⟩

theorem computes_src {s : Src} {p : Prog} (hr : ∀ input, srcRun s input = nanoRun p input) {α β : Type} {f : α → β}
    {encodeInput : α → List UInt8} {encodeOutput : β → List UInt8} (h : Computes s f encodeInput encodeOutput) :
    Computes p f encodeInput encodeOutput := fun a => by
  have := h a
  change srcRun s _ = _ at this
  rw [hr] at this; exact this

/-- **What comes out** from source text -/
theorem nano_src_correct : CompileCorrect riscv nanoCompileSrcIR := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits enoughMemory
  obtain ⟨p, -, hc, hr⟩ := src_inv compiles
  exact nano_compile_correct p compiled f encodeInput encodeOutput argument startState call hc (computes_src hr computes)
    startsRight outputFits enoughMemory

/-- **What happens** from source text -/
theorem nano_src_runs : CompileRuns riscv nanoCompileSrcIR := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits
  obtain ⟨p, -, hc, hr⟩ := src_inv compiles
  exact nano_compile_runs p compiled f encodeInput encodeOutput argument startState call hc (computes_src hr computes)
    startsRight outputFits

/-- the code from source text is `nanoGenIR` of the elaborated program -/
theorem nanoCompileSrcIR_code {s : Src} {c : CompiledA} (h : nanoCompileSrcIR s = some c) :
    ∃ p, nanoElab s.bytes = some p ∧ c.code = nanoGenIR p := by
  obtain ⟨p, he, hc, -⟩ := src_inv h
  exact ⟨p, he, nanoGenIR_code hc⟩

end Nano
