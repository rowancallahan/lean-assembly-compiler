/- **The nano chain, source text to RISC-V (Sail model)**, one theorem per meaning.

`nanoCompileSrc src = (nanoElab src).bind nanoCompileIR`: UTF-8 bytes → `nanoElab` (the SPEC: never proved, cross-checked
against Lean's elaborator) → `Prog` → `nanoCompileIR = Ir.compile ∘ lower` (PROVED: `nano_compile_correct`,
`Nano/ProofTop.lean`) → machine code `nanoGenIR p`.

* `nano_chain`: if `nanoElab src = some p` and the compiler gives `c`, then for every argument list of the entry's
  arity (8-byte little-endian words) and every correct start (`StartCorrect riscv`) with 8 output bytes and
  `memoryNeeded` work bytes, the Sail RISC-V model runs `c.code` (= `nanoGenIR p`) back to the caller, without the
  out-of-memory flag, with the output block holding `p.eval args` as 8 little-endian bytes.
* `nano_chain_int`: the same for an `Int64` source (`nanoElabT src = some (true, p)`): arguments and result as
  8-byte little-endian two's complement, the result is `p.evalI args` (Lean's `Int64` arithmetic).
* `nano_chain_runs`: `CompileRunsWeak` form (no memory hypothesis): returns, frame kept, flag iff out of memory.
These are corollaries of `CompileCorrectWeak riscv nanoCompileIR` / `CompileRunsWeak riscv nanoCompileIR` with
`f` = the program's meaning on argument lists of the right length (`Computes` holds by definition of `nanoRun`,
and for Int64 by `nanoRun_int`). -/
import Nano.ProofSrc
import Nano.Int
import Nano.Elab
import Nano.StackTop

set_option linter.unusedVariables false

namespace Nano
open Proven Proven.Mach Proven.Top Proven.Top.Alloc

/-- **the nano compiler from source bytes** -/
noncomputable def nanoCompileSrc (src : List UInt8) : Option CompiledA := (nanoElab src).bind nanoCompileIR

/-- the same compiler as nano-proof's `nanoCompileSrcIR` (`Nano/ProofSrc.lean`) -/
theorem nanoCompileSrc_eq (src : List UInt8) : nanoCompileSrc src = nanoCompileSrcIR ⟨src⟩ := rfl

/-- argument lists of the entry's arity -/
abbrev Args (p : Prog) (α : Type) := {args : List α // args.length = p.1}

/-- the words, 8 little-endian bytes each -/
def encWs (args : List UInt64) : List UInt8 := args.flatMap fun a => leN 8 a.toNat

theorem wordsOf_encWs : ∀ args : List UInt64, wordsOf args.length (encWs args) = some args
  | [] => rfl
  | a :: as => by
    have h8 : (leN 8 a.toNat).length = 8 := leN_length _ _
    have hd : (encWs (a :: as)).drop 8 = encWs as := by
      simp only [encWs, List.flatMap_cons]; exact List.drop_left' h8
    have ht : (encWs (a :: as)).take 8 = leN 8 a.toNat := by
      simp only [encWs, List.flatMap_cons]; exact List.take_left' h8
    have hl : 8 ≤ (encWs (a :: as)).length := by simp only [encWs, List.flatMap_cons, List.length_append]; omega
    simp only [List.length_cons, wordsOf, if_pos hl, hd, ht, wordsOf_encWs as, Option.map_some]
    congr
    rw [Proven.Ir.IndLow.unle_leN8 _ a.toNat_lt]; simp

/-- the program computes `den p.2 args.reverse` on words -/
theorem computes_words (p : Prog) :
    Computes p (fun a : Args p UInt64 => den p.2 a.1.reverse) (fun a => encWs a.1) (fun v => leN 8 v.toNat) := by
  intro ⟨args, h⟩
  show nanoRun p (encWs args) = _
  have hw := wordsOf_encWs args; rw [h] at hw
  unfold nanoRun; rw [hw, Option.bind_some]; unfold Prog.eval; rw [if_pos h]; rfl

/-- the `Int64` program computes `denI p.2 args.reverse` on two's complement words -/
theorem computes_int (p : Prog) :
    Computes p (fun a : Args p Int64 => denI p.2 a.1.reverse) (fun a => encIs a.1) encI := by
  intro ⟨args, h⟩
  show nanoRun p (encIs args) = _
  rw [nanoRun_int p args h]; unfold Prog.evalI; rw [if_pos h]; rfl

/-! ## any proved nano back end (`CompileCorrectWeak riscv compile`): the source-level corollaries
(for `nanoCompileIR` below; for nano-proof's `asm ∘ genR` route once its `CompileCorrectWeak` theorem lands) -/

/-- **`UInt64`, for any proved back end** -/
theorem chain_of {compile : Prog → Option CompiledA} (correct : CompileCorrectWeak riscv compile) (src : List UInt8)
    (p : Prog) (c : CompiledA) (helab : nanoElab src = some p) (hc : compile p = some c) (args : List UInt64)
    (harity : args.length = p.1) (startState : riscv.State) (call : Call)
    (startsRight : StartCorrect riscv startState call c.code (encWs args))
    (outputFits : 8 ≤ call.outputLength) (enoughMemory : memoryNeeded c (encWs args) ≤ call.workLength) :
    ∃ v, p.eval args = some v ∧
    ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
      readMemory (riscv.observe finishState) call.outputAddress 8 = some (leN 8 v.toNat) := by
  refine ⟨den p.2 args.reverse, by unfold Prog.eval; rw [if_pos harity], ?_⟩
  have := correct p c _ _ _ ⟨args, harity⟩ startState call hc (computes_words p) startsRight
    (by rw [leN_length]; exact outputFits) enoughMemory
  simpa only [leN_length] using this

/-- **`Int64`, for any proved back end** -/
theorem chain_int_of {compile : Prog → Option CompiledA} (correct : CompileCorrectWeak riscv compile)
    (src : List UInt8) (p : Prog) (c : CompiledA) (helab : nanoElabT src = some (true, p)) (hc : compile p = some c)
    (args : List Int64) (harity : args.length = p.1) (startState : riscv.State) (call : Call)
    (startsRight : StartCorrect riscv startState call c.code (encIs args))
    (outputFits : 8 ≤ call.outputLength) (enoughMemory : memoryNeeded c (encIs args) ≤ call.workLength) :
    ∃ v, p.evalI args = some v ∧
    ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
      readMemory (riscv.observe finishState) call.outputAddress 8 = some (encI v) := by
  refine ⟨denI p.2 args.reverse, by unfold Prog.evalI; rw [if_pos harity], ?_⟩
  have := correct p c _ _ _ ⟨args, harity⟩ startState call hc (computes_int p) startsRight
    (by rw [encI, leN_length]; exact outputFits) enoughMemory
  simpa only [encI, leN_length] using this

/-- **source to machine, `UInt64`** -/
theorem nano_chain (src : List UInt8) (p : Prog) (c : CompiledA) (helab : nanoElab src = some p)
    (hc : nanoCompileSrc src = some c) (args : List UInt64) (harity : args.length = p.1)
    (startState : riscv.State) (call : Call) (startsRight : StartCorrect riscv startState call c.code (encWs args))
    (outputFits : 8 ≤ call.outputLength) (enoughMemory : memoryNeeded c (encWs args) ≤ call.workLength) :
    c.code = nanoGenIR p ∧ ∃ v, p.eval args = some v ∧
    ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
      readMemory (riscv.observe finishState) call.outputAddress 8 = some (leN 8 v.toNat) := by
  rw [nanoCompileSrc, helab, Option.bind_some] at hc
  refine ⟨nanoGenIR_code hc, den p.2 args.reverse, by unfold Prog.eval; rw [if_pos harity], ?_⟩
  have := nano_compile_correct p c _ _ _ ⟨args, harity⟩ startState call hc (computes_words p) startsRight
    (by rw [leN_length]; exact outputFits) enoughMemory
  simpa only [leN_length] using this

/-- **source to machine, `Int64`**: two's complement in and out, Lean's `Int64` arithmetic -/
theorem nano_chain_int (src : List UInt8) (p : Prog) (c : CompiledA) (helab : nanoElabT src = some (true, p))
    (hc : nanoCompileSrc src = some c) (args : List Int64) (harity : args.length = p.1)
    (startState : riscv.State) (call : Call) (startsRight : StartCorrect riscv startState call c.code (encIs args))
    (outputFits : 8 ≤ call.outputLength) (enoughMemory : memoryNeeded c (encIs args) ≤ call.workLength) :
    c.code = nanoGenIR p ∧ ∃ v, p.evalI args = some v ∧
    ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
      readMemory (riscv.observe finishState) call.outputAddress 8 = some (encI v) := by
  rw [nanoCompileSrc, nanoElab, helab, Option.map_some, Option.bind_some] at hc
  refine ⟨nanoGenIR_code hc, denI p.2 args.reverse, by unfold Prog.evalI; rw [if_pos harity], ?_⟩
  have := nano_compile_correct p c _ _ _ ⟨args, harity⟩ startState call hc (computes_int p) startsRight
    (by rw [encI, leN_length]; exact outputFits) enoughMemory
  simpa only [encI, leN_length] using this

/-- **source to machine, what happens** (no memory hypothesis): return, frame kept, flag iff out of memory -/
theorem nano_chain_runs (src : List UInt8) (p : Prog) (c : CompiledA) (helab : nanoElab src = some p)
    (hc : nanoCompileSrc src = some c) (args : List UInt64) (harity : args.length = p.1)
    (startState : riscv.State) (call : Call) (startsRight : StartCorrect riscv startState call c.code (encWs args))
    (outputFits : 8 ≤ call.outputLength) :
    ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (∀ address, Outside address (call.outputAddress, call.outputLength) →
        Outside address (call.workAddress, call.workLength) →
        (riscv.observe finishState).memory address = (riscv.observe startState).memory address) ∧
      ((riscv.observe finishState).register riscv.mapping.status = oomFlag ↔
        OutOfMemory c (encWs args) call.workLength) := by
  rw [nanoCompileSrc, helab, Option.bind_some] at hc
  exact nano_compile_runs p c _ _ _ ⟨args, harity⟩ startState call hc (computes_words p) startsRight
    (by rw [leN_length]; exact outputFits)

/-! ## the stack path `nanoCompileA` (code `nanoGen p = asm (genR p)`; L2 in `Nano/StackTop.lean`) -/

/-- **stack path, source to machine, `UInt64`**: `chain_of nano_stack_correct` -/
theorem nano_stack_chain (src : List UInt8) (p : Prog) (c : CompiledA) (helab : nanoElab src = some p)
    (hc : nanoCompileA p = some c) (args : List UInt64) (harity : args.length = p.1)
    (startState : riscv.State) (call : Call) (startsRight : StartCorrect riscv startState call c.code (encWs args))
    (outputFits : 8 ≤ call.outputLength) (enoughMemory : memoryNeeded c (encWs args) ≤ call.workLength) :
    c.code = nanoGen p ∧ ∃ v, p.eval args = some v ∧
    ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
      readMemory (riscv.observe finishState) call.outputAddress 8 = some (leN 8 v.toNat) :=
  ⟨nanoCompileA_code hc, chain_of nano_stack_correct src p c helab hc args harity startState call startsRight
    outputFits enoughMemory⟩

/-- **stack path, source to machine, `Int64`**: `chain_int_of nano_stack_correct` -/
theorem nano_stack_chain_int (src : List UInt8) (p : Prog) (c : CompiledA) (helab : nanoElabT src = some (true, p))
    (hc : nanoCompileA p = some c) (args : List Int64) (harity : args.length = p.1)
    (startState : riscv.State) (call : Call) (startsRight : StartCorrect riscv startState call c.code (encIs args))
    (outputFits : 8 ≤ call.outputLength) (enoughMemory : memoryNeeded c (encIs args) ≤ call.workLength) :
    c.code = nanoGen p ∧ ∃ v, p.evalI args = some v ∧
    ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
      readMemory (riscv.observe finishState) call.outputAddress 8 = some (encI v) :=
  ⟨nanoCompileA_code hc, chain_int_of nano_stack_correct src p c helab hc args harity startState call startsRight
    outputFits enoughMemory⟩

end Nano
