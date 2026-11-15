/- Draft (NOT part of `Spec/`): memory as an allocator SPECIFICATION, machine-independent, above RISC-V and ARM.
See `Testing/notes/SPEC_DRAFT.md`, "Sketch: out of memory as a machine step".

* No allocator implementation is required: `AllocSpec` only says what a valid allocation is.
* A compiled program reports the memory events of its abstract run; `memoryNeeded` is the most cells in use at
  any point of that run, with unlimited space. Defined, not calculated.
* `CompileRuns` (what happens): no memory hypothesis; the code returns to the caller, nothing outside the output
  and work blocks changes, and `oomFlag` is in the
  status register exactly when the run is out of memory.
* `CompileCorrect` (what comes out): with the hypothesis `memoryNeeded ≤ workLength` it returns with the right
  output and no flag.
Only definitions and statements (as `Prop`s); no theorem is assumed. -/
import Spec.Top

namespace Proven.Top.Alloc

/-- A memory event of a program's abstract run, in cells of one fixed size. -/
inductive MemEvent where
  | alloc (cells : Nat)
  | free (cells : Nat)

/-- Cells in use after the events: allocated and not yet freed. -/
def inUse : List MemEvent → Nat
  | [] => 0
  | .alloc n :: rest => inUse rest + n
  | .free n :: rest => inUse rest - n

/-- The most cells in use at any point (the events are listed newest first). -/
def peak : List MemEvent → Nat
  | [] => 0
  | event :: rest => max (inUse (event :: rest)) (peak rest)

/-- A block lies inside another. -/
def Inside (block outer : UInt64 × Nat) : Prop :=
  outer.1.toNat ≤ block.1.toNat ∧ block.1.toNat + block.2 ≤ outer.1.toNat + outer.2

/-- The allocator specification: a valid answer to a request for `cells` cells of `cellSize` bytes is a block
inside the work block, apart from every block in use. No implementation is fixed. -/
def AllocSpec (cellSize : Nat) (work : UInt64 × Nat) (blocksInUse : List (UInt64 × Nat)) (cells : Nat)
    (block : UInt64 × Nat) : Prop :=
  block.2 = cells * cellSize ∧ Inside block work ∧ ∀ used ∈ blocksInUse, Apart used block

/-- Compiled code with the memory events of its abstract run. -/
structure CompiledA where
  code : List UInt8
  cellSize : Nat
  events : List UInt8 → List MemEvent

/-- Most work memory the run uses, in bytes, with unlimited space. -/
def memoryNeeded (compiled : CompiledA) (input : List UInt8) : Nat :=
  compiled.cellSize * peak (compiled.events input)

/-- The reported out-of-memory value. -/
def oomFlag : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- Out of memory: a property of the run, not of a register. -/
def OutOfMemory (compiled : CompiledA) (input : List UInt8) (workLength : Nat) : Prop :=
  workLength < memoryNeeded compiled input

/-- Running (what happens), no memory hypothesis: the code returns to the caller, and the status register holds
`oomFlag` exactly when the run is out of memory. -/
def CompileRuns {P : Type} [Program P] (machine : Machine) (compile : P → Option CompiledA) : Prop :=
  ∀ {α β : Type} (program : P) (compiled : CompiledA) (f : α → β) (encodeInput : α → List UInt8)
    (encodeOutput : β → List UInt8) (argument : α) (startState : machine.State) (call : Call),
    compile program = some compiled →
    Computes program f encodeInput encodeOutput →
    StartCorrect machine startState call compiled.code (encodeInput argument) →
    ∃ finishState, Runs machine startState finishState ∧
      (machine.observe finishState).programCounter = call.returnAddress ∧
      (∀ address, Outside address (call.outputAddress, call.outputLength) →
        Outside address (call.workAddress, call.workLength) →
        (machine.observe finishState).memory address = (machine.observe startState).memory address) ∧
      ((machine.observe finishState).register machine.mapping.status = oomFlag ↔
        OutOfMemory compiled (encodeInput argument) call.workLength)

/-- Correct (what comes out): with enough memory the code returns with the right output and no flag. -/
def CompileCorrect {P : Type} [Program P] (machine : Machine) (compile : P → Option CompiledA) : Prop :=
  ∀ {α β : Type} (program : P) (compiled : CompiledA) (f : α → β) (encodeInput : α → List UInt8)
    (encodeOutput : β → List UInt8) (argument : α) (startState : machine.State) (call : Call),
    compile program = some compiled →
    Computes program f encodeInput encodeOutput →
    StartCorrect machine startState call compiled.code (encodeInput argument) →
    (encodeOutput (f argument)).length ≤ call.outputLength →
    memoryNeeded compiled (encodeInput argument) ≤ call.workLength →
    ∃ finishState, Runs machine startState finishState ∧
      (machine.observe finishState).programCounter = call.returnAddress ∧
      (machine.observe finishState).register machine.mapping.status ≠ oomFlag ∧
      readMemory (machine.observe finishState) call.outputAddress (encodeOutput (f argument)).length
        = some (encodeOutput (f argument))

end Proven.Top.Alloc
