/- The loader contract for machines with page permissions (DeepMind's AArch64 model): `StartCorrect` only constrains
what `observe` shows, so the statements below add, as a premise on the start state, that the code bytes are
executable and the input, output and work blocks readable and writable. -/
import Spec.Alloc

namespace Proven.Top.Alloc

/-- The loader mapped the code executable (`X`) and the call's data blocks readable and writable (`W`). -/
def LoaderMaps {machine : Machine} (X W : machine.State → Nat → Prop) (state : machine.State) (call : Call)
    (code : List UInt8) : Prop :=
  (∀ address, (machine.observe state).programCounter.toNat ≤ address →
    address < (machine.observe state).programCounter.toNat + code.length → X state address) ∧
  (∀ address,
    (call.inputAddress.toNat ≤ address ∧ address < call.inputAddress.toNat + call.inputLength) ∨
    (call.outputAddress.toNat ≤ address ∧ address < call.outputAddress.toNat + call.outputLength) ∨
    (call.workAddress.toNat ≤ address ∧ address < call.workAddress.toNat + call.workLength) → W state address)

/-- `CompileCorrect` for start states that also meet `LoaderMaps X W`. -/
def CompileCorrectLoaded {P : Type} [Program P] (machine : Machine) (X W : machine.State → Nat → Prop)
    (compile : P → Option CompiledA) : Prop :=
  ∀ {α β : Type} (program : P) (compiled : CompiledA) (f : α → β) (encodeInput : α → List UInt8)
    (encodeOutput : β → List UInt8) (argument : α) (startState : machine.State) (call : Call),
    compile program = some compiled →
    Computes program f encodeInput encodeOutput →
    StartCorrect machine startState call compiled.code (encodeInput argument) →
    LoaderMaps X W startState call compiled.code →
    (encodeOutput (f argument)).length ≤ call.outputLength →
    memoryNeeded compiled (encodeInput argument) ≤ call.workLength →
    ∃ finishState, Runs machine startState finishState ∧
      (machine.observe finishState).programCounter = call.returnAddress ∧
      (machine.observe finishState).register machine.mapping.status ≠ oomFlag ∧
      readMemory (machine.observe finishState) call.outputAddress (encodeOutput (f argument)).length
        = some (encodeOutput (f argument)) ∧
      (machine.observe finishState).register machine.mapping.outputLength = (encodeOutput (f argument)).length.toUInt64 ∧
      (∀ address, Outside address (call.outputAddress, (encodeOutput (f argument)).length) →
        Outside address (call.workAddress, call.workLength) →
        (machine.observe finishState).memory address = (machine.observe startState).memory address) ∧
      KeptRegisters machine startState finishState ∧ machine.configured finishState

/-- `CompileRuns` for start states that also meet `LoaderMaps X W`. -/
def CompileRunsLoaded {P : Type} [Program P] (machine : Machine) (X W : machine.State → Nat → Prop)
    (compile : P → Option CompiledA) : Prop :=
  ∀ {α β : Type} (program : P) (compiled : CompiledA) (f : α → β) (encodeInput : α → List UInt8)
    (encodeOutput : β → List UInt8) (argument : α) (startState : machine.State) (call : Call),
    compile program = some compiled →
    Computes program f encodeInput encodeOutput →
    StartCorrect machine startState call compiled.code (encodeInput argument) →
    LoaderMaps X W startState call compiled.code →
    (encodeOutput (f argument)).length ≤ call.outputLength →
    ∃ finishState, Runs machine startState finishState ∧
      (machine.observe finishState).programCounter = call.returnAddress ∧
      (∀ address, Outside address (call.outputAddress, (encodeOutput (f argument)).length) →
        Outside address (call.workAddress, call.workLength) →
        (machine.observe finishState).memory address = (machine.observe startState).memory address) ∧
      ((machine.observe finishState).register machine.mapping.status = oomFlag ↔
        OutOfMemory compiled (encodeInput argument) call.workLength) ∧
      KeptRegisters machine startState finishState ∧ machine.configured finishState

end Proven.Top.Alloc
