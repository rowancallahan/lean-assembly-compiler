/- Partial instance of the self-hosting statement, for the stage that is compiled today: `asm`.
`asm_stage_emits`: the binary our compiler made from `Nano.asm` (`Nano.Self.nanoAsm.code`, machine theorem
`nanoAsm.implements1`), run on the Sail model on the records `genR p`, returns with `nanoGen p` in the output block.
With (L2) for a `compile` whose code is `nanoGen p`, that output is correct machine code for `p` (`SelfHosted.correct`
has no reference to how the code was produced).  Missing for the full target: `genR` and `nanoElab` as compiled stages. -/
import Legacy.Nano.SelfHost
import Legacy.Nano.AsmSelf
import Legacy.Nano.StackTop

set_option linter.unusedVariables false

namespace Nano.SelfHost
open Proven Proven.Top Proven.Top.Alloc Nano Nano.Link

theorem nanoAsm_ofL (l : List UInt8) : Nano.Self.nanoAsm (ofL l) = asm l := rfl

/-- **the compiled assembler emits the code** (the self-hosted suffix of the compiler, on the Sail model) -/
theorem asm_stage_emits (p : Prog) (startState : riscv.State) (call : Call)
    (startsRight : StartCorrect riscv startState call (wordBytes Nano.Self.nanoAsm.code) (genR p))
    (outputFits : (nanoGen p).length ≤ call.outputLength)
    (enough : 8 * (Nano.Self.nanoAsm.slots + 1) + 7 ≤ call.workLength) :
    ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      readMemory (riscv.observe finishState) call.outputAddress (nanoGen p).length = some (nanoGen p) ∧
      (riscv.observe finishState).register riscv.mapping.outputLength = (nanoGen p).length.toUInt64 := by
  obtain ⟨fin, hruns, hpc, hread, -, -, -, hlen⟩ :=
    implements1_top (comap Nano.Self.nanoAsm.implements1 ofL) (argument := genR p) startsRight outputFits enough
  exact ⟨fin, hruns, hpc, hread, hlen rfl⟩

/-- **What is proved today, composed (Sail axioms only)**: the part of the nano compiler that runs as machine code
made by our compiler is the assembler; `nanoElab` (the spec) and `genR` still run in Lean.  For every source `src`
with `nanoElab src = some p` that the stack path accepts (`nanoCompileA p = some c`: scoped, depth ≤ 256):
1. the compiled assembler binary, run on the Sail model on the records `genR p`, returns with the code `c.code`
   (= `asm (genR p)`) in the output block and its length in `a1`;
2. that code, run on the Sail model on any arguments of the entry's arity (8-byte little-endian words), returns
   with `p.eval args` in the output block and no out-of-memory flag when the work block has `memoryNeeded` bytes;
3. without the memory hypothesis it returns, changes nothing outside output and work, and sets the flag exactly
   when the work block is too small.
(`Int64`: `nano_stack_chain_int`, `Nano/Chain.lean`.) -/
theorem selfHosted_asm_stage (src : List UInt8) (p : Prog) (c : CompiledA) (helab : nanoElab src = some p)
    (hc : nanoCompileA p = some c) :
    (∀ (startState : riscv.State) (call : Call),
      StartCorrect riscv startState call (wordBytes Nano.Self.nanoAsm.code) (genR p) →
      c.code.length ≤ call.outputLength → 8 * (Nano.Self.nanoAsm.slots + 1) + 7 ≤ call.workLength →
      ∃ finishState, Runs riscv startState finishState ∧
        (riscv.observe finishState).programCounter = call.returnAddress ∧
        readMemory (riscv.observe finishState) call.outputAddress c.code.length = some c.code ∧
        (riscv.observe finishState).register riscv.mapping.outputLength = c.code.length.toUInt64) ∧
    (∀ (args : List UInt64), args.length = p.1 → ∀ (startState : riscv.State) (call : Call),
      StartCorrect riscv startState call c.code (encWs args) → 8 ≤ call.outputLength →
      memoryNeeded c (encWs args) ≤ call.workLength →
      ∃ v, p.eval args = some v ∧ ∃ finishState, Runs riscv startState finishState ∧
        (riscv.observe finishState).programCounter = call.returnAddress ∧
        (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
        readMemory (riscv.observe finishState) call.outputAddress 8 = some (leN 8 v.toNat)) ∧
    (∀ (args : List UInt64), args.length = p.1 → ∀ (startState : riscv.State) (call : Call),
      StartCorrect riscv startState call c.code (encWs args) → 8 ≤ call.outputLength →
      ∃ finishState, Runs riscv startState finishState ∧
        (riscv.observe finishState).programCounter = call.returnAddress ∧
        (∀ address, Outside address (call.outputAddress, call.outputLength) →
          Outside address (call.workAddress, call.workLength) →
          (riscv.observe finishState).memory address = (riscv.observe startState).memory address) ∧
        ((riscv.observe finishState).register riscv.mapping.status = oomFlag ↔
          OutOfMemory c (encWs args) call.workLength)) := by
  have e : c.code = nanoGen p := nanoCompileA_code hc
  refine ⟨fun startState call startsRight outputFits enough => ?_,
    fun args harity startState call startsRight outputFits enough =>
      chain_of nano_stack_correct src p c helab hc args harity startState call startsRight outputFits enough,
    fun args harity startState call startsRight outputFits =>
      nano_stack_runs p c _ _ _ ⟨args, harity⟩ startState call hc (computes_words p) startsRight
        (by rw [leN_length]; exact outputFits)⟩
  rw [e] at outputFits ⊢
  exact asm_stage_emits p startState call startsRight outputFits enough

end Nano.SelfHost
