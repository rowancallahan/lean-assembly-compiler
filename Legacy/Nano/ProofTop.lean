/- **The nano compiler is correct on RISC-V** (the owner's statements, `Compiler/AllocSpec.lean`):
`Nano.nano_compile_correct : CompileCorrectWeak riscv nanoCompileIR` and `Nano.nano_compile_runs : CompileRunsWeak riscv
nanoCompileIR`, for `nanoCompileIR p = Ir.compile (lower p)` (code = `nanoGenIR p`, `nanoGenIR_code`).  The program meaning is
`nanoRun` (`Nano/Proof.lean`: arguments as 8-byte LE words, `Prog.eval`, result as 8 LE bytes); the lowering is
proved there (`lower_ok`), the IR compiler in `Riscv/Back/IrTop.lean` (`Ir.machine_run`). -/
import Legacy.Nano.Proof
import Legacy.Riscv.Back.IrTop

set_option linter.unusedVariables false

namespace Nano
open Proven Proven.Mach Proven.Top Proven.Top.Alloc

/-- **the nano compiler** -/
noncomputable def nanoCompileIR (p : Prog) : Option CompiledA := Ir.compile (lower p)

/-- the code of `nanoCompileIR` is `nanoGenIR` -/
theorem nanoGenIR_code {p : Prog} {c : CompiledA} (h : nanoCompileIR p = some c) : c.code = nanoGenIR p := by
  unfold nanoCompileIR Ir.compile at h
  unfold nanoGenIR
  split at h
  · next ws Q hw => cases h; rw [hw]
  · exact nomatch h

theorem computes_of {p : Prog} {α β : Type} {f : α → β} {encodeInput : α → List UInt8}
    {encodeOutput : β → List UInt8} (computes : Computes p f encodeInput encodeOutput) (argument : α)
    (hsmall : (encodeInput argument).length ≤ 2 ^ 20) :
    (lower p).meaning (encodeInput argument) = some (encodeOutput (f argument)) :=
  lower_ok p _ _ (computes argument) hsmall

/-- **What happens** (`CompileRunsWeak`) -/
theorem nano_compile_runs : CompileRunsWeak riscv nanoCompileIR := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits
  obtain ⟨finishState, hruns, hpc, hframe, hcase⟩ :=
    Ir.machine_run compiles (fun h => computes_of computes argument h) startsRight outputFits
  refine ⟨finishState, hruns, hpc, hframe, ?_⟩
  unfold OutOfMemory
  rcases hcase with ⟨hle, hne, -⟩ | ⟨hlt, heq⟩
  · exact ⟨fun h => absurd h hne, fun h => absurd h (Nat.not_lt.2 hle)⟩
  · exact ⟨fun _ => hlt, fun _ => heq⟩

/-- **What comes out** (`CompileCorrectWeak`) -/
theorem nano_compile_correct : CompileCorrectWeak riscv nanoCompileIR := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits enoughMemory
  obtain ⟨finishState, hruns, hpc, hframe, hcase⟩ :=
    Ir.machine_run compiles (fun h => computes_of computes argument h) startsRight outputFits
  rcases hcase with ⟨-, hne, hread⟩ | ⟨hlt, -⟩
  · exact ⟨finishState, hruns, hpc, hne, hread⟩
  · exact absurd enoughMemory (Nat.not_le.2 hlt)

end Nano
