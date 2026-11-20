/- Opus box E: the FINAL LINK: C compiled by itself.  For C's own source text `x` (whose parse is the certified AST
`Cert.PC.all`, hypothesis `hsrc` until D's source link lands): the meaning of `x` is the driver `mC`, except where the
meaning hits Gen's buffer capacity (2^19 words); hence the code `compileC` emits for `x` computes `mC` on every such
input, in the owner's `CompileCorrect` terms (via `C_correctLO`). -/
import Nano.V2Self.Proof.Main.RvTop
import Nano.V2Self.Proof.Cert.All
open LeanRV64D
namespace NanoMain
open Proven.Top Proven.Top.Alloc ParSpec

/-- the certificate's output shadow is the driver -/
theorem mLean_eq : Cert.Sh.mLean = mC := rfl

/-- **C's text means `mC`.** If `x` lexes and parses to C's certified AST, then on every input shorter than 2^64 bytes
the meaning of `x` is exactly `mC inp`, unless the meaning stops at the buffer capacity; in that case (and only then)
the meaning has no result (`srcRun = none`).  The meaning never gets stuck. -/
theorem self_meaning (x : List UInt8) (hsrc : ∃ ts, LexSpec.Lexes x ts ∧ ParsesProgram ts Cert.PC.all)
    (inp : List UInt8) (hin : inp.length < 2 ^ 64) :
    (Sem κC Cert.PC.all inp = .error .cap ∧ srcRun ⟨x⟩ inp = none) ∨
    (Sem κC Cert.PC.all inp = .ok (mC inp) ∧ srcRun ⟨x⟩ inp = some (mC inp)) := by
  obtain ⟨ts, hl, hp⟩ := hsrc
  have hpo := pOf_eq hl hp
  rcases Cert.sem_C inp hin with h | h
  · exact Or.inl ⟨h, by simp [srcRun, hpo, h, Except.toOption]⟩
  · exact Or.inr ⟨h, by simp [srcRun, hpo, h, Except.toOption, mLean_eq]⟩

/-- the inputs on which C's meaning does not hit the capacity -/
def SelfIn : Type := {inp : List UInt8 // inp.length < 2 ^ 64 ∧ Sem κC Cert.PC.all inp ≠ .error .cap}

/-- C's text computes `mC` (on `SelfIn`, bytes in, bytes out) -/
theorem self_computes (x : List UInt8) (hsrc : ∃ ts, LexSpec.Lexes x ts ∧ ParsesProgram ts Cert.PC.all) :
    Computes (⟨x⟩ : SrcC) (fun a : SelfIn => mC a.1) Subtype.val id := by
  unfold Computes
  intro a
  rw [show Program.run (⟨x⟩ : SrcC) a.val = srcRun ⟨x⟩ a.val from rfl, id]
  rcases self_meaning x hsrc a.1 a.2.1 with ⟨h, -⟩ | ⟨-, h⟩
  · exact (a.2.2 h).elim
  · exact h

/-- **C compiled by itself is correct.** Let `x` be C's source text (it lexes and parses to the certified AST) and let
`compiled` be what C emits for it.  Then on every input that does not hit the 2^19-word buffer capacity, the emitted
RISC-V code, started per the calling convention with enough output and work space, returns to the caller with output
`mC inp`, length register set, memory outside the output and work blocks and the kept registers unchanged. -/
theorem self_correct (x : List UInt8) (hsrc : ∃ ts, LexSpec.Lexes x ts ∧ ParsesProgram ts Cert.PC.all)
    (compiled : CompiledA) (a : SelfIn) (startState : riscv.State) (call : Call)
    (compiles : compileC ⟨x⟩ = some compiled)
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
  by
  have h := C_correctLO (α := SelfIn) (β := List UInt8) ⟨x⟩ compiled (fun a : SelfIn => mC a.1) Subtype.val id a
    startState call compiles (self_computes x hsrc) startsRight (by simp only [id]; exact outputFits) enough
  simp only [id] at h
  exact h

end NanoMain
