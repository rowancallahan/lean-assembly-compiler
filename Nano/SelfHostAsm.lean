/- Partial instance of the self-hosting statement, for the stage that is compiled today: `asm`.
`asm_stage_emits`: the binary our compiler made from `Nano.asm` (`Nano.Self.nanoAsm.code`, machine theorem
`nanoAsm.implements1`), run on the Sail model on the records `genR p`, returns with `nanoGen p` in the output block.
With (L2) for a `compile` whose code is `nanoGen p`, that output is correct machine code for `p` (`SelfHosted.correct`
has no reference to how the code was produced).  Missing for the full target: `genR` and `nanoElab` as compiled stages. -/
import Nano.SelfHost
import Nano.AsmSelf

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

end Nano.SelfHost
