/- Opus box E: **C compiled by itself, for C's actual source text.**  `SrcGen.X0` is the byte list of
`Testing/nano/v2self/self_S_input.txt`: it is written as the concatenation of the per-def chunks of that file, and the
generator `Testing/nano/v2self/srclink/gen.lean` reads the file with `IO.FS.readBinFile` and refuses to write the
modules unless the chunks concatenate to exactly those bytes (`cut does not cover the text`).  D's kernel-checked
`SrcGen.link_pc` says X0 lexes and parses to the certified AST `Cert.PC.all`; the certificate `Cert.sem_C` says that
AST means `mC`; `C_correctLO` says compiled code runs as the meaning.  No hypotheses remain except, in `self_correct_C`,
the ones every `CompileCorrect` statement has: `compileC ⟨X0⟩ = some compiled` (holds iff `mC X0 ≠ []`; the
bootstrap fixpoint shows it empirically, a proof needs kernel evaluation of `mC` on the 66 KB text), a correct start,
and enough output and work space. -/
import Nano.Main.SelfLink
import Nano.SelfHost.SrcLink.Top
open LeanRV64D
namespace NanoMain
open Proven.Top Proven.Top.Alloc ParSpec

set_option maxRecDepth 200000 in
/-- C's own text has no `match` (checked by the kernel on its token list) -/
theorem noMatch_C : DsSpec.matchTok ∉ SrcGen.T0 := by decide +kernel

set_option maxRecDepth 200000 in
theorem len_C : SrcGen.W0.length < 2 ^ 24 := by decide +kernel

/-- C's text means its certified AST: it lexes, its words desugar to themselves (no `match`), and they parse -/
theorem hsrc_C : ∃ ts, DsSpec.LexesD SrcGen.X0 ts ∧ ParsesProgram ts Cert.PC.all := by
  obtain ⟨hl, hp⟩ := SrcGen.link_pc
  have ht := tokL_of_tokens (lexes_tokWF hl) SrcGen.tk0
  exact ⟨_, ⟨_, hl, DsSpec.ds_id ht noMatch_C len_C⟩, hp⟩

/-- **C's text means `mC`**: for every input shorter than 2^64 bytes, the meaning of C's source text is `mC inp`,
except on inputs where the meaning hits Gen's buffer capacity (2^19 words): there, and only there, it has no result. -/
theorem self_meaning_C (inp : List UInt8) (hin : inp.length < 2 ^ 64) :
    (Sem κC Cert.PC.all inp = .error .cap ∧ srcRun ⟨SrcGen.X0⟩ inp = none) ∨
    (Sem κC Cert.PC.all inp = .ok (mC inp) ∧ srcRun ⟨SrcGen.X0⟩ inp = some (mC inp)) :=
  self_meaning _ hsrc_C inp hin

/-- C's text computes `mC` on `SelfIn`: inputs shorter than 2^64 bytes on which the meaning does NOT hit the 2^19-word
capacity (inputs that hit it are excluded: there the source program has no result to compare against). -/
theorem self_computes_C : Computes (⟨SrcGen.X0⟩ : SrcC) (fun a : SelfIn => mC a.1) Subtype.val id :=
  self_computes _ hsrc_C

/-- **The code C emits for its own source text computes C.**  If C, run on its own source text `X0`, emits `compiled`,
then for every input `a` that does not hit the 2^19-word capacity, the emitted RISC-V code, started per the calling
convention with room for the output and at least `memoryNeeded` work bytes, returns to the caller with `mC a` in the
output block, its length in the length register, memory outside the output and work blocks and the callee-saved
registers unchanged, and the machine still configured. -/
theorem self_correct_C (compiled : CompiledA) (a : SelfIn) (startState : riscv.State) (call : Call)
    (compiles : compileC ⟨SrcGen.X0⟩ = some compiled)
    (startsRight : StartCorrect riscv startState call compiled.code a.1)
    (outputFits : (mC a.1).length ≤ call.outputLength)
    (enough : memoryNeeded compiled a.1 ≤ call.workLength) :
    ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
      readMemory (riscv.observe finishState) call.outputAddress (mC a.1).length = some (mC a.1) ∧
      (riscv.observe finishState).register riscv.mapping.outputLength = (mC a.1).length.toUInt64 ∧
      (∀ address, Outside address (call.outputAddress, (mC a.1).length) →
        Outside address (call.workAddress, call.workLength) →
        (riscv.observe finishState).memory address = (riscv.observe startState).memory address) ∧
      KeptRegisters riscv startState finishState ∧ riscv.configured finishState :=
  self_correct _ hsrc_C compiled a startState call compiles startsRight outputFits enough

end NanoMain
