/- Opus box E: `CompileRuns` for C with no premises (D's `shiftInv` discharges `ShiftInv`), and its instance for C's
own source text. -/
import Nano.V2Self.Proof.Main.RunsTop
import Nano.V2Self.Proof.Bridge.MainShift4
import Nano.V2Self.Proof.Main.SelfC
open LeanRV64D
namespace NanoMain
open Proven Proven.Top Proven.Top.Alloc ParSpec

/-- **C runs correctly with any work block** (owner's `CompileRuns`): return to the caller, memory changed only in
the work block and the result prefix of the output block, callee-saved registers kept, configured, and out of memory
reported (a0 = −1) exactly when the work block is smaller than `memoryNeeded`. -/
theorem C_runsO : CompileRuns riscv compileC := C_runs shiftInv

/-- **the code C emits for its own source text, with any work block**: for every input that does not hit the 2^19-word
capacity, the run returns to the caller, changes memory only in the work block and the first `|mC a|` output bytes,
keeps the callee-saved registers, and reports out of memory exactly when the work block is smaller than
`memoryNeeded compiled a` -/
theorem self_runs_C (compiled : CompiledA) (a : SelfIn) (startState : riscv.State) (call : Call)
    (compiles : compileC ⟨SrcGen.X0⟩ = some compiled)
    (startsRight : StartCorrect riscv startState call compiled.code a.1)
    (outputFits : (mC a.1).length ≤ call.outputLength) :
    ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (∀ address, Outside address (call.outputAddress, (mC a.1).length) →
        Outside address (call.workAddress, call.workLength) →
        (riscv.observe finishState).memory address = (riscv.observe startState).memory address) ∧
      ((riscv.observe finishState).register riscv.mapping.status = oomFlag ↔
        OutOfMemory compiled a.1 call.workLength) ∧
      KeptRegisters riscv startState finishState ∧ riscv.configured finishState := by
  have h := C_runsO (α := SelfIn) (β := List UInt8) ⟨SrcGen.X0⟩ compiled (fun a : SelfIn => mC a.1) Subtype.val id a
    startState call compiles self_computes_C startsRight (by simp only [id]; exact outputFits)
  simp only [id] at h
  exact h

end NanoMain
