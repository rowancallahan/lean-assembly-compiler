/- **The S3 compiler on RISC-V** (`Testing/notes/IR_S3.md`): `S3.compile : S3.Prog → Option CompiledA` lowers a
typed S3 program to RTL (`Compiler/S3/Lower.lean`) and compiles it with the IR compiler (`Riscv/Back/IrTop.lean`).
Its theorems have the owner's shapes (`Compiler/AllocSpec.lean`): `S3.compile_runs : CompileRunsWeak riscv compile`,
`S3.compile_correct : CompileCorrectWeak riscv compile`, proved ONCE for every S3 program by composing the lowering
simulation (`Compiler/S3/LowerMain.lean`: `lower_meaning`) with `Ir.machine_run`. -/
import Riscv.Back.IrTop
import Compiler.S3.LowerMain

set_option linter.unusedVariables false

namespace Proven.S3
open Proven Proven.Mach Proven.Top Proven.Top.Alloc

/-- **the S3 compiler** -/
noncomputable def compile (P : Prog) : Option CompiledA :=
  open Classical in if Accepted P then Ir.compile (lowerP P) else none

theorem compile_inv {P : Prog} {c : CompiledA} (h : compile P = some c) : Accepted P ∧ Ir.compile (lowerP P) = some c := by
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
theorem computes_of {P : Prog} (hG : Accepted P) {α β : Type} {f : α → β} {encodeInput : α → List UInt8}
    {encodeOutput : β → List UInt8} (computes : Computes P f encodeInput encodeOutput) (argument : α)
    (hsmall : (encodeInput argument).length ≤ 2 ^ 20) (hout : (encodeOutput (f argument)).length ≤ 2 ^ 32) :
    (lowerP P).meaning (encodeInput argument) = some (encodeOutput (f argument)) := by
  obtain ⟨v, hD, ho⟩ := Prog.run_some (computes argument)
  exact lower_meaning P hG _ _ v hD ho (by omega) (by omega)

/-- **What happens** (`CompileRunsWeak`) for every S3 program -/
theorem compile_runs : CompileRunsWeak riscv compile := by
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

/-- **What comes out** (`CompileCorrectWeak`) for every S3 program -/
theorem compile_correct : CompileCorrectWeak riscv compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits enoughMemory
  obtain ⟨hG, hc⟩ := compile_inv compiles
  obtain ⟨finishState, hruns, hpc, hframe, hcase⟩ :=
    Ir.machine_run hc (fun h => computes_of hG computes argument h
      (Nat.le_trans outputFits (out_small startsRight))) startsRight outputFits
  rcases hcase with ⟨-, hne, hread⟩ | ⟨hlt, -⟩
  · exact ⟨finishState, hruns, hpc, hne, hread⟩
  · exact absurd enoughMemory (Nat.not_le.2 hlt)

/-! ## The strengthened statements -/

/-- the RTL program's run: the output of `P`, and `main` returns its length -/
theorem result_of {P : Prog} (hG : Accepted P) {α β : Type} {f : α → β} {encodeInput : α → List UInt8}
    {encodeOutput : β → List UInt8} (computes : Computes P f encodeInput encodeOutput) (argument : α)
    (hsmall : (encodeInput argument).length ≤ 2 ^ 20) (hout : (encodeOutput (f argument)).length ≤ 2 ^ 32) :
    ∀ r, (lowerP P).result (encodeInput argument) = some r →
      r.vs = [.w (BitVec.ofNat 64 (encodeOutput (f argument)).length)] := by
  obtain ⟨v, hD, ho⟩ := Prog.run_some (computes argument)
  obtain ⟨r, hr, -, hvs⟩ := lower_result P hG _ _ v hD ho (by omega) (by omega)
  intro r' hr'
  rw [hr] at hr'; cases hr'; exact hvs

/-- **What comes out, strengthened** (`CompileCorrect`) for every S3 program: the output, its length in `a1`, the
callee-saved registers kept, `Cfg`, nothing changed outside the result and the work block -/
theorem compile_correctL : CompileCorrect riscv compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits enoughMemory
  obtain ⟨hG, hc⟩ := compile_inv compiles
  have hout := Nat.le_trans outputFits (out_small startsRight)
  obtain ⟨finishState, hruns, hpc, hframe, -, hcfg, hcase⟩ :=
    Ir.machine_runL hc (fun h => computes_of hG computes argument h hout) startsRight outputFits
  rcases hcase with ⟨-, hne, hread, hkept, hlen⟩ | ⟨hlt, -⟩
  · exact ⟨finishState, hruns, hpc, hne, hread,
      hlen (result_of hG computes argument startsRight.inputSmall hout), hframe, hkept, hcfg⟩
  · exact absurd enoughMemory (Nat.not_le.2 hlt)

/-- **What comes out, strengthened, with the full memory frame** (`CompileCorrectRV`) for every S3 program: the
hypothesis of the chaining adapter `Proven.Top.implements_of_compileL` -/
theorem compile_correctRV : CompileCorrectRV compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits enoughMemory
  obtain ⟨hG, hc⟩ := compile_inv compiles
  have hout := Nat.le_trans outputFits (out_small startsRight)
  obtain ⟨finishState, hruns, hpc, -, hnat, hcfg, hcase⟩ :=
    Ir.machine_runL hc (fun h => computes_of hG computes argument h hout) startsRight outputFits
  rcases hcase with ⟨-, hne, hread, hkept, hlen⟩ | ⟨hlt, -⟩
  · exact ⟨finishState, hruns, hpc, hne, hread,
      hlen (result_of hG computes argument startsRight.inputSmall hout), hnat, hkept, hcfg⟩
  · exact absurd enoughMemory (Nat.not_le.2 hlt)

/-- **S3-compiled code implements its function** in the `Implements1With` form that `Nano.Link.link_stage` chains:
the adapter applied to `compile_correctRV` -/
theorem implements {P : Prog} {compiled : CompiledA} {code : List (BitVec 32)} {α β : Type}
    {encA : α → List UInt8} {encB : β → List UInt8} {f : α → β} {space : Nat → Nat} {maxLen : Nat} {retLen : Bool}
    (compiles : compile P = some compiled) (hcode : compiled.code = wordBytes code)
    (computes : Computes P f encA encB)
    (hspace : ∀ a, (encA a).length ≤ maxLen → memoryNeeded compiled (encA a) ≤ space (encA a).length)
    (hmax : maxLen ≤ 2 ^ 20) :
    Implements1With encA encB code f space maxLen retLen :=
  implements_of_compileL compile_correctRV compiles hcode computes hspace hmax

end Proven.S3
