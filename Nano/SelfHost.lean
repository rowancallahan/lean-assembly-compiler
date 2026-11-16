/- **Proven self-hosting of nano: the composed statement** (integration, branch nano-int).

`SelfHosted B space D compile`: the RISC-V binary `B` is a nano compiler that is itself machine code, and what it
outputs is correct machine code.  For every source text `src` (in the domain `D`: the size side conditions) and every
`p` with `nanoElab src = some p` (`nanoElab`, `Prog.eval`: the SPEC of nano):

* `emits`: `B`, run on the Sail RISC-V model on `src`, returns to its caller with the bytes `c.code = nanoGen p`
  (`asm (genR p)`, the stack generator) in the output block and their number in `a1`;
* `correct`/`correctInt`: those bytes, run on the Sail model on the arguments (8-byte little-endian words; two's
  complement for `Int64`), return with `p.eval args` (`p.evalI args`) in the output block and no out-of-memory flag,
  when the work block has `memoryNeeded` bytes (`CompileCorrect` form);
* `runs`: without the memory hypothesis they return with everything outside output and work unchanged, and the flag
  is set exactly when the work block is too small (`CompileRuns` form).

`selfHosted_of` proves it from the two lemmas:
(L1) `B` computes the compiler: `Implements1With` for a byte function `cb` with `cb src = nanoGen p`;
(L2) `CompileCorrect riscv compile` and `CompileRuns riscv compile` for a `compile` whose code is `nanoGen p`.
Trusted: `nanoElab`/`Prog.eval` (spec), the Sail model, the statements in `Spec/` and `Compiler/AllocSpec.lean`. -/
import Nano.Chain
import Nano.Gen
import Nano.Link
import Riscv.Back.Top

set_option linter.unusedVariables false

namespace Nano.SelfHost
open Proven Proven.Top Proven.Top.Alloc Nano

/-- the source texts of the domain `D` -/
abbrev SrcIn (D : List UInt8 → Prop) := {src : List UInt8 // D src}

/-- **the target statement** -/
structure SelfHosted (B : List (BitVec 32)) (space : Nat → Nat) (D : List UInt8 → Prop)
    (compile : Prog → Option CompiledA) : Prop where
  /-- the compiler's code is the stack generator's -/
  code : ∀ p c, compile p = some c → c.code = nanoGen p
  /-- `B` on the Sail model emits the code -/
  emits : ∀ (src : List UInt8) (p : Prog) (c : CompiledA), D src → nanoElab src = some p → compile p = some c →
    ∀ (startState : riscv.State) (call : Call), StartCorrect riscv startState call (wordBytes B) src →
    c.code.length ≤ call.outputLength → space src.length ≤ call.workLength →
    ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      readMemory (riscv.observe finishState) call.outputAddress c.code.length = some c.code ∧
      (riscv.observe finishState).register riscv.mapping.outputLength = c.code.length.toUInt64
  /-- the emitted code computes `p.eval` -/
  correct : ∀ (src : List UInt8) (p : Prog) (c : CompiledA), nanoElab src = some p → compile p = some c →
    ∀ (args : List UInt64), args.length = p.1 → ∀ (startState : riscv.State) (call : Call),
    StartCorrect riscv startState call c.code (encWs args) → 8 ≤ call.outputLength →
    memoryNeeded c (encWs args) ≤ call.workLength →
    ∃ v, p.eval args = some v ∧ ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
      readMemory (riscv.observe finishState) call.outputAddress 8 = some (leN 8 v.toNat)
  /-- the same for an `Int64` source -/
  correctInt : ∀ (src : List UInt8) (p : Prog) (c : CompiledA), nanoElabT src = some (true, p) →
    compile p = some c → ∀ (args : List Int64), args.length = p.1 → ∀ (startState : riscv.State) (call : Call),
    StartCorrect riscv startState call c.code (encIs args) → 8 ≤ call.outputLength →
    memoryNeeded c (encIs args) ≤ call.workLength →
    ∃ v, p.evalI args = some v ∧ ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
      readMemory (riscv.observe finishState) call.outputAddress 8 = some (encI v)
  /-- what happens without the memory hypothesis: the flag exactly when out of memory -/
  runs : ∀ (src : List UInt8) (p : Prog) (c : CompiledA), nanoElab src = some p → compile p = some c →
    ∀ (args : List UInt64), args.length = p.1 → ∀ (startState : riscv.State) (call : Call),
    StartCorrect riscv startState call c.code (encWs args) → 8 ≤ call.outputLength →
    ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (∀ address, Outside address (call.outputAddress, call.outputLength) →
        Outside address (call.workAddress, call.workLength) →
        (riscv.observe finishState).memory address = (riscv.observe startState).memory address) ∧
      ((riscv.observe finishState).register riscv.mapping.status = oomFlag ↔
        OutOfMemory c (encWs args) call.workLength)

/-- **the composition**: (L1) and (L2) give the target -/
theorem selfHosted_of {B : List (BitVec 32)} {space : Nat → Nat} {D : List UInt8 → Prop}
    {compile : Prog → Option CompiledA} {cb : List UInt8 → List UInt8}
    (L1 : Implements1With (α := SrcIn D) (fun s => s.1) encRaw B (fun s => cb s.1) space (retLen := true))
    (hcb : ∀ src p, D src → nanoElab src = some p → cb src = nanoGen p)
    (hcode : ∀ p c, compile p = some c → c.code = nanoGen p)
    (L2 : CompileCorrect riscv compile) (L2r : CompileRuns riscv compile) : SelfHosted B space D compile where
  code := hcode
  emits := fun src p c hD helab hc startState call startsRight outputFits enough => by
    have e : cb src = c.code := by rw [hcb src p hD helab, hcode p c hc]
    obtain ⟨fin, hruns, hpc, hread, -, -, -, hlen⟩ := implements1_top L1 (argument := (⟨src, hD⟩ : SrcIn D))
      startsRight (by show (cb src).length ≤ _; rw [e]; exact outputFits) enough
    replace hlen := hlen rfl
    simp only [encRaw, e] at hread hlen
    exact ⟨fin, hruns, hpc, hread, hlen⟩
  correct := fun src p c helab hc args harity startState call startsRight outputFits enough =>
    chain_of L2 src p c helab hc args harity startState call startsRight outputFits enough
  correctInt := fun src p c helab hc args harity startState call startsRight outputFits enough =>
    chain_int_of L2 src p c helab hc args harity startState call startsRight outputFits enough
  runs := fun src p c helab hc args harity startState call startsRight outputFits =>
    L2r p c _ _ _ ⟨args, harity⟩ startState call hc (computes_words p) startsRight
      (by rw [leN_length]; exact outputFits)

end Nano.SelfHost
