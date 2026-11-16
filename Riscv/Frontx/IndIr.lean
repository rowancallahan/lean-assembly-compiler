/- The inductive path on the shared IR (`Testing/notes/IR_DESIGN.md` §4, stage S2), beside the old route
(`Riscv/Frontx/IndMem.lean`, unchanged): `IndIr.compile : IndProg → Option CompiledA` lowers the program to RTL
(`Compiler/Ir/IndLow.lean`: cells as blocks of 4, field reads as `ld`, dispatch as `switch`, tail calls as jumps,
`dec` / `enc` as RTL functions, strings as length + UTF-8 bytes) and compiles it with `Ir.compile` (calls with frames,
`Riscv/Back/IrTop.lean`).  Its theorems have the owner's shapes (`Compiler/AllocSpec.lean`):
`IndIr.compile_runs : CompileRuns riscv compile`, `IndIr.compile_correct : CompileCorrect riscv compile`, with exactly
the Sail axioms; `memoryNeeded` is the peak of the Lin run's events (frames and cells), so out of memory is exact.

**The lowering is proved** (`Compiler/Ir/IndLow*.lean`, `lower_ok`): on the input bytes of well-formed values the
RTL program's meaning is the output of `Pg.sem` (outputs of at most `2 ^ 32` bytes, all a start state's RAM can
hold).  `compile` checks `LGood` (the shape has fewer than 255 tags, `Chain`, `okL`, a fresh constructor's tag below
256, at most 8 result bytes: the conditions of `IndMem.compile` the lowering needs; `frontx_ind` entries satisfy
`Chain` by `rfl`), so the two theorems hold for every such program.
Tests: every inductive-path entry (incl. `pos_comp`, `tree_insert5`, `level_combining`, `level_simplify`, which the
old route rejects, and the 11 `Expr` entries) on QEMU + Sail at `memoryNeeded` and `memoryNeeded - 1`
(`Testing/asm/emit_ind_ir.lean`, `Testing/asm/ir_test.py`). -/
import Riscv.Back.IrTop
import Riscv.Frontx.IndMem
import Compiler.Ir.IndLowMain

set_option linter.unusedVariables false

namespace Proven.Frontx.IndIr
open Proven Proven.Mach Proven.Mach.Ind Proven.Top Proven.Top.Alloc Proven.Frontx.IndMem

/-- the RTL program of an inductive-path program -/
def lowerP (p : IndProg) : Ir.Prog Ir.VReg := Ir.IndLow.lower p.sh p.shO p.pg p.hs p.bi p.ain p.a0 p.nb

/-- the conditions the compiler checks (those of `IndMem.compile` that the lowering needs): each function's `X` the
meanings of the later ones (`Chain`), and `goodB`: a shape of fewer than 255 tags, arms well-kinded with constructor
tags below 256 (`okL`), a fresh constructor's tag below 256, at most 8 result bytes -/
def LGood (p : IndProg) : Prop :=
  Chain (⟨p.rk, p.pg⟩ :: p.hs) ∧ Ir.IndLow.goodB p.sh p.pg p.hs p.bi p.nb = true

/-- **the lowering is correct** for `p`: on every well-formed input that a start state allows, the RTL program's
output is the program's (the meaning of `Pg.sem`), when it fits in a machine's memory -/
def LowerOk (p : IndProg) : Prop :=
  ∀ x, p.Valid x → (p.bytes x).length ≤ 2 ^ 20 → (p.out x).length ≤ 2 ^ 32 →
    (lowerP p).meaning (p.bytes x) = some (p.out x)

/-- **the lowering is correct** (`Compiler/Ir/IndLowMain.lean`: `lower_ok`) -/
theorem lowerOk (p : IndProg) (h : LGood p) : LowerOk p := by
  obtain ⟨hch, hg⟩ := h
  obtain ⟨hsh, hok, hbi, hnb⟩ := Ir.IndLow.goodB_spec hg
  intro x hv hI hO
  exact Ir.IndLow.lower_ok p.sh p.shO p.pg p.hs p.bi p.ain p.a0 p.nb hsh hch hok hbi hnb x.1 x.2.1 x.2.2 hv.1 hv.2 hI hO

/-- **the compiler** (the IR route) -/
noncomputable def compile (p : IndProg) : Option CompiledA :=
  open Classical in if LGood p then Ir.compile (lowerP p) else none

theorem compile_inv {p : IndProg} {c : CompiledA} (h : compile p = some c) : LowerOk p ∧ Ir.compile (lowerP p) = some c := by
  unfold compile at h
  split at h
  · exact ⟨lowerOk p (by assumption), h⟩
  · exact nomatch h

/-- the output block of a start state lies in RAM: at most `2 ^ 32` bytes -/
theorem out_small {startState : riscv.State} {call : Call} {code input : List UInt8}
    (h : StartCorrect riscv startState call code input) : call.outputLength ≤ 2 ^ 32 := by
  have := (h.inRam (call.outputAddress, call.outputLength) (by simp [Call.blocks])).2
  have e : riscv.ramEnd = 0x100000000 := rfl
  simp only at this; omega

/-- the RTL program computes what `p` computes, on the inputs a start state allows -/
theorem computes_of {p : IndProg} (hok : LowerOk p) {α β : Type} {f : α → β} {encodeInput : α → List UInt8}
    {encodeOutput : β → List UInt8} (computes : Computes p f encodeInput encodeOutput) (argument : α)
    (hsmall : (encodeInput argument).length ≤ 2 ^ 20) (hout : (encodeOutput (f argument)).length ≤ 2 ^ 32) :
    (lowerP p).meaning (encodeInput argument) = some (encodeOutput (f argument)) := by
  obtain ⟨x, hv, hin, hout'⟩ := run_some (computes argument)
  rw [hin] at hsmall ⊢; rw [hout'] at hout ⊢; exact hok x hv hsmall hout

/-- **What happens** (`CompileRuns`) on the IR route -/
theorem compile_runs : CompileRuns riscv compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits
  obtain ⟨hok, hc⟩ := compile_inv compiles
  obtain ⟨finishState, hruns, hpc, hframe, hcase⟩ :=
    Ir.machine_run hc (fun h => computes_of hok computes argument h
      (Nat.le_trans outputFits (out_small startsRight))) startsRight outputFits
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
    Ir.machine_run hc (fun h => computes_of hok computes argument h
      (Nat.le_trans outputFits (out_small startsRight))) startsRight outputFits
  rcases hcase with ⟨-, hne, hread⟩ | ⟨hlt, -⟩
  · exact ⟨finishState, hruns, hpc, hne, hread⟩
  · exact absurd enoughMemory (Nat.not_le.2 hlt)

end Proven.Frontx.IndIr
