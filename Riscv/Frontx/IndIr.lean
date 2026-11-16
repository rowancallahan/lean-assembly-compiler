/- The inductive path on the shared IR (`Testing/notes/IR_DESIGN.md` §4, stage S2), beside the old route
(`Riscv/Frontx/IndMem.lean`, unchanged): `IndIr.compile : IndProg → Option CompiledA` lowers the program to RTL
(`Compiler/Ir/IndLow.lean`: cells as blocks of 4, field reads as `ld`, dispatch as `switch`, tail calls as jumps,
`dec` / `enc` as RTL functions, strings as length + UTF-8 bytes) and compiles it with `Ir.compile` (calls with frames,
`Riscv/Back/IrTop.lean`).  Its theorems have the owner's shapes (`Compiler/AllocSpec.lean`):
`IndIr.compile_runs : CompileRuns riscv compile`, `IndIr.compile_correct : CompileCorrect riscv compile`, with exactly
the Sail axioms; `memoryNeeded` is the peak of the Lin run's events (frames and cells), so out of memory is exact.

**Open (not proved yet)**: the correctness of the lowering against the source semantics, `LowerOk p` (the RTL
program's meaning on every well-formed input of at most `2^20` bytes is the output of `Pg.sem`).  `compile` checks it
as a (classical) condition, so the two theorems say nothing about a program until `LowerOk` is proved for it; the
structured-code lemmas it needs (`Compiler/Ir/StructOk.lean`: `flatS_ok`, `flatT_ok`, `reach_call`) are proved.
Tests: every inductive-path entry (incl. `pos_comp`, `tree_insert5`, `level_combining`, `level_simplify`, which the
old route rejects, and the 11 `Expr` entries) on QEMU + Sail at `memoryNeeded` and `memoryNeeded - 1`
(`Testing/asm/emit_ind_ir.lean`, `Testing/asm/ir_test.py`). -/
import Riscv.Back.IrTop
import Riscv.Frontx.IndMem
import Compiler.Ir.IndLow

set_option linter.unusedVariables false

namespace Proven.Frontx.IndIr
open Proven Proven.Mach Proven.Mach.Ind Proven.Top Proven.Top.Alloc Proven.Frontx.IndMem

/-- the RTL program of an inductive-path program -/
def lowerP (p : IndProg) : Ir.Prog Ir.VReg := Ir.IndLow.lower p.sh p.shO p.pg p.hs p.bi p.ain p.a0 p.nb

/-- **the lowering is correct** for `p`: on every well-formed input that a start state allows, the RTL program's
output is the program's (the meaning of `Pg.sem`) -/
def LowerOk (p : IndProg) : Prop :=
  ∀ x, p.Valid x → (p.bytes x).length ≤ 2 ^ 20 → (lowerP p).meaning (p.bytes x) = some (p.out x)

/-- **the compiler** (the IR route) -/
noncomputable def compile (p : IndProg) : Option CompiledA :=
  open Classical in if LowerOk p then Ir.compile (lowerP p) else none

theorem compile_inv {p : IndProg} {c : CompiledA} (h : compile p = some c) : LowerOk p ∧ Ir.compile (lowerP p) = some c := by
  unfold compile at h
  split at h
  · exact ⟨by assumption, h⟩
  · exact nomatch h

/-- the RTL program computes what `p` computes, on the inputs a start state allows -/
theorem computes_of {p : IndProg} (hok : LowerOk p) {α β : Type} {f : α → β} {encodeInput : α → List UInt8}
    {encodeOutput : β → List UInt8} (computes : Computes p f encodeInput encodeOutput) (argument : α)
    (hsmall : (encodeInput argument).length ≤ 2 ^ 20) :
    (lowerP p).meaning (encodeInput argument) = some (encodeOutput (f argument)) := by
  obtain ⟨x, hv, hin, hout⟩ := run_some (computes argument)
  rw [hin] at hsmall ⊢; rw [hout]; exact hok x hv hsmall

/-- **What happens** (`CompileRuns`) on the IR route -/
theorem compile_runs : CompileRuns riscv compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits
  obtain ⟨hok, hc⟩ := compile_inv compiles
  obtain ⟨finishState, hruns, hpc, hframe, hcase⟩ :=
    Ir.machine_run hc (computes_of hok computes argument) startsRight outputFits
  refine ⟨finishState, hruns, hpc, hframe, ?_⟩
  unfold OutOfMemory
  rcases hcase with ⟨hle, hne, -⟩ | ⟨hlt, heq⟩
  · exact ⟨fun h => absurd h hne, fun h => absurd h (Nat.not_lt.2 hle)⟩
  · exact ⟨fun _ => hlt, fun _ => heq⟩

/-- **What comes out** (`CompileCorrect`) on the IR route -/
theorem compile_correct : CompileCorrect riscv compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits enoughMemory
  obtain ⟨hok, hc⟩ := compile_inv compiles
  obtain ⟨finishState, hruns, hpc, hframe, hcase⟩ :=
    Ir.machine_run hc (computes_of hok computes argument) startsRight outputFits
  rcases hcase with ⟨-, hne, hread⟩ | ⟨hlt, -⟩
  · exact ⟨finishState, hruns, hpc, hne, hread⟩
  · exact absurd enoughMemory (Nat.not_le.2 hlt)

end Proven.Frontx.IndIr
