/- **The S3 compiler on RISC-V** (`Testing/notes/IR_S3.md`): `S3.compile : S3.Prog → Option CompiledA` lowers a
typed S3 program to RTL (`Compiler/S3/Lower.lean`) and compiles it with the IR compiler (`Riscv/Back/IrTop.lean`).
Its theorems have the owner's shapes (`Compiler/AllocSpec.lean`): `S3.compile_runs : CompileRuns riscv compile`,
`S3.compile_correct : CompileCorrect riscv compile`, proved ONCE for every S3 program by composing the lowering
simulation (`Compiler/S3/LowerMain.lean`: `lower_meaning`) with `Ir.machine_run`. -/
import Riscv.Back.IrTop
import Compiler.S3.LowerMain

set_option linter.unusedVariables false

namespace Proven.S3
open Proven Proven.Mach Proven.Top Proven.Top.Alloc

/-- **the S3 compiler** -/
noncomputable def compile (P : Prog) : Option CompiledA :=
  open Classical in if Good P then Ir.compile (lowerP P) else none

theorem compile_inv {P : Prog} {c : CompiledA} (h : compile P = some c) : Good P ∧ Ir.compile (lowerP P) = some c := by
  unfold compile at h
  split at h
  · exact ⟨by assumption, h⟩
  · exact nomatch h

/-- the output block of a start state lies in RAM: at most `2 ^ 32` bytes -/
theorem out_small {startState : riscv.State} {call : Call} {code input : List UInt8}
    (h : StartCorrect riscv startState call code input) : call.outputLength ≤ 2 ^ 32 := by
  have := (h.inRam (call.outputAddress, call.outputLength) (by simp [Call.blocks])).2
  have e : riscv.ramEnd = 0x100000000 := rfl
  simp only at this; omega

/-- the RTL program computes what `P` computes, on the inputs a start state allows -/
theorem computes_of {P : Prog} (hG : Good P) {α β : Type} {f : α → β} {encodeInput : α → List UInt8}
    {encodeOutput : β → List UInt8} (computes : Computes P f encodeInput encodeOutput) (argument : α)
    (hsmall : (encodeInput argument).length ≤ 2 ^ 20) (hout : (encodeOutput (f argument)).length ≤ 2 ^ 32) :
    (lowerP P).meaning (encodeInput argument) = some (encodeOutput (f argument)) := by
  obtain ⟨v, hD, ho⟩ := Prog.run_some (computes argument)
  exact lower_meaning P hG _ _ v hD ho (by omega) (by omega)

/-- **What happens** (`CompileRuns`) for every S3 program -/
theorem compile_runs : CompileRuns riscv compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits
  obtain ⟨hG, hc⟩ := compile_inv compiles
  obtain ⟨finishState, hruns, hpc, hframe, hcase⟩ :=
    Ir.machine_run hc (fun h => computes_of hG computes argument h
      (Nat.le_trans outputFits (out_small startsRight))) startsRight outputFits
  refine ⟨finishState, hruns, hpc, hframe, ?_⟩
  unfold OutOfMemory
  rcases hcase with ⟨hle, hne, -⟩ | ⟨hlt, heq⟩
  · exact ⟨fun h => absurd h hne, fun h => absurd h (Nat.not_lt.2 hle)⟩
  · exact ⟨fun _ => hlt, fun _ => heq⟩

/-- **What comes out** (`CompileCorrect`) for every S3 program -/
theorem compile_correct : CompileCorrect riscv compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits enoughMemory
  obtain ⟨hG, hc⟩ := compile_inv compiles
  obtain ⟨finishState, hruns, hpc, hframe, hcase⟩ :=
    Ir.machine_run hc (fun h => computes_of hG computes argument h
      (Nat.le_trans outputFits (out_small startsRight))) startsRight outputFits
  rcases hcase with ⟨-, hne, hread⟩ | ⟨hlt, -⟩
  · exact ⟨finishState, hruns, hpc, hne, hread⟩
  · exact absurd enoughMemory (Nat.not_le.2 hlt)

end Proven.S3
