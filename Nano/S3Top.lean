/- **nano through the S3 calculus: the composed compiler and its theorems** (`Testing/notes/NANO_S3.md`).

`nanoCompileS3 = S3.compile ∘ toS3 ∘ tr2P ∘ tr1P`: nano `Prog` → L1 (calls inlined as lets, `Nano/S3L1.lean`) →
L2 (A-normal form, `Nano/S3L2.lean`) → L3/L4 (S3 word expressions under the byte-list I/O `main`,
`Nano/S3L3.lean`, `Nano/S3L4.lean`) → `S3.compile` (proved once, `Riscv/Back/S3Top.lean`).
* `nanoToS3_run`: the chain preserves the byte-level meaning (`nanoRun p input = some out → (nanoToS3 p).run input =
  some out`), from `tr1_eval`, `tr2_eval`, `toS3_run`;
* **`nano_s3_correct : CompileCorrect riscv nanoCompileS3`**, **`nano_s3_runs : CompileRuns riscv nanoCompileS3`**:
  S3's theorems + the chain, nothing proved at the machine level here;
* `nano_s3_chain` / `nano_s3_chain_int`: source text to machine, `UInt64` and `Int64` (`chain_of`/`chain_int_of`). -/
import Nano.S3L4
import Nano.Chain
import Riscv.Back.S3Top

set_option linter.unusedVariables false

namespace Nano.S3
open Proven Proven.Mach Proven.Top Proven.Top.Alloc

/-- **the chain**: nano program → S3 program -/
def nanoToS3 (p : Nano.Prog) : Proven.S3.Prog := toS3 (tr2P (tr1P p))

/-- **the S3 back end for nano** -/
noncomputable def nanoCompileS3 (p : Nano.Prog) : Option CompiledA := Proven.S3.compile (nanoToS3 p)

/-- the chain preserves nano's byte-level meaning -/
theorem nanoToS3_run (p : Nano.Prog) (input out : List UInt8) (h : nanoRun p input = some out) :
    (nanoToS3 p).run input = some out := by
  apply toS3_run
  have e : ∀ args, (tr2P (tr1P p)).eval args = p.eval args := fun args => by rw [tr2_eval, tr1_eval]
  unfold run2; unfold nanoRun at h
  simp only [e]; exact h

theorem computes_tr {α β : Type} {p : Nano.Prog} {f : α → β} {encodeInput : α → List UInt8}
    {encodeOutput : β → List UInt8} (h : Computes p f encodeInput encodeOutput) :
    Computes (nanoToS3 p) f encodeInput encodeOutput := fun a => nanoToS3_run p _ _ (h a)

/-- the signature is small (S3's `Accepted`) -/
theorem small_S0 : Proven.S3.Small S0 := by
  intro i
  rcases i with _ | _ | i
  · refine ⟨by decide, fun j => ?_⟩
    rcases j with _ | _ | j <;> simp [Proven.S3.Sig.flds, Proven.S3.lget]
  · refine ⟨by decide, fun j => ?_⟩
    rcases j with _ | j <;> simp [Proven.S3.Sig.flds, Proven.S3.lget]
  · simp [Proven.S3.Sig.nc, Proven.S3.Sig.flds, Proven.S3.Sig.dt, Proven.S3.lget]

/-- every program of the chain passes S3's check -/
theorem accepted (p : Nano.Prog) : Proven.S3.Accepted (nanoToS3 p) := ⟨small_S0, rfl⟩

/-- **What comes out** (`CompileCorrect`) for every nano program, through S3 -/
theorem nano_s3_correct : CompileCorrect riscv nanoCompileS3 := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits enoughMemory
  exact Proven.S3.compile_correct (nanoToS3 program) compiled f encodeInput encodeOutput argument startState call
    compiles (computes_tr computes) startsRight outputFits enoughMemory

/-- **What happens** (`CompileRuns`) for every nano program, through S3 -/
theorem nano_s3_runs : CompileRuns riscv nanoCompileS3 := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits
  exact Proven.S3.compile_runs (nanoToS3 program) compiled f encodeInput encodeOutput argument startState call
    compiles (computes_tr computes) startsRight outputFits

/-- the S3 back end compiles every nano program the IR back end accepts -/
theorem nanoCompileS3_eq (p : Nano.Prog) : nanoCompileS3 p = Ir.compile (Proven.S3.lowerP (nanoToS3 p)) := by
  unfold nanoCompileS3 Proven.S3.compile; rw [if_pos (accepted p)]

/-- **source to machine through S3, `UInt64`** -/
theorem nano_s3_chain (src : List UInt8) (p : Nano.Prog) (c : CompiledA) (helab : nanoElab src = some p)
    (hc : nanoCompileS3 p = some c) (args : List UInt64) (harity : args.length = p.1) (startState : riscv.State)
    (call : Call) (startsRight : StartCorrect riscv startState call c.code (encWs args))
    (outputFits : 8 ≤ call.outputLength) (enoughMemory : memoryNeeded c (encWs args) ≤ call.workLength) :
    ∃ v, p.eval args = some v ∧
    ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
      readMemory (riscv.observe finishState) call.outputAddress 8 = some (leN 8 v.toNat) :=
  chain_of nano_s3_correct src p c helab hc args harity startState call startsRight outputFits enoughMemory

/-- **source to machine through S3, `Int64`** -/
theorem nano_s3_chain_int (src : List UInt8) (p : Nano.Prog) (c : CompiledA)
    (helab : nanoElabT src = some (true, p)) (hc : nanoCompileS3 p = some c) (args : List Int64)
    (harity : args.length = p.1) (startState : riscv.State) (call : Call)
    (startsRight : StartCorrect riscv startState call c.code (encIs args))
    (outputFits : 8 ≤ call.outputLength) (enoughMemory : memoryNeeded c (encIs args) ≤ call.workLength) :
    ∃ v, p.evalI args = some v ∧
    ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
      readMemory (riscv.observe finishState) call.outputAddress 8 = some (encI v) :=
  chain_int_of nano_s3_correct src p c helab hc args harity startState call startsRight outputFits enoughMemory

end Nano.S3
