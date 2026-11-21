/- Nano/Expr/CExprTop: **C's machine code computes the meaning of C's emitted Expr.** For every input in `SelfIn`
(shorter than 2^64 bytes, not hitting the 2^19-word capacity), the RISC-V code C emits for its own text writes
`mC a` (`self_correct_C`), and `mC a` is the big-step meaning of the Expr nano emits for C's `m` (`C_expr`).
That Expr equals Lean's elaborated Expr of C on 234/236 defs (the spot check, Testing/notes/EXPR.md §0). -/
import Nano.Main.SelfC
import Nano.Expr.CExpr
namespace NanoMain
open Proven.Top Proven.Top.Alloc ParSpec ExprSpec LeanRV64D

theorem self_expr_C (compiled : CompiledA) (a : SelfIn) (startState : riscv.State) (call : Call)
    (compiles : compileC ⟨SrcGen.X0⟩ = some compiled)
    (startsRight : StartCorrect riscv startState call compiled.code a.1)
    (outputFits : (mC a.1).length ≤ call.outputLength)
    (enough : memoryNeeded compiled a.1 ≤ call.workLength) :
    ∃ finishState, Runs riscv startState finishState ∧
      readMemory (riscv.observe finishState) call.outputAddress (mC a.1).length = some (mC a.1) ∧
      Ev (progOf oC) [.l a.1] (.app (.c "m" []) (.bv 0)) (.l (mC a.1)) := by
  obtain ⟨fs, hrun, -, -, hmem, -⟩ := self_correct_C compiled a startState call compiles startsRight outputFits enough
  have hsem : Sem κC Cert.PC.all a.1 = .ok (mC a.1) := by
    rcases self_meaning_C a.1 a.2.1 with ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h a.2.2
    · exact h
  exact ⟨fs, hrun, hmem, C_expr a.1 a.2.1 hsem⟩

end NanoMain
