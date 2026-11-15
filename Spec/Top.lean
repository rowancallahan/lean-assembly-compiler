/- Top-level specification: machines, runs, calls. -/
import Spec.Machines

namespace Proven.Top

/-- What the caller can see. -/
structure MachineState where
  programCounter : UInt64
  register : Nat → UInt64
  memory : UInt64 → Option UInt8

/-- A machine with its own states. -/
structure Machine where
  State : Type
  step : State → Option State
  observe : State → MachineState
  configured : State → Prop
  mapping : RegisterMapping
  ramStart : Nat
  ramEnd : Nat

/-- Zero or more successful steps. -/
inductive Runs (machine : Machine) : machine.State → machine.State → Prop
  | stop {state} : Runs machine state state
  | step {state next finish} : machine.step state = some next → Runs machine next finish →
      Runs machine state finish

/-- Source programs: bytes to bytes. -/
class Program (P : Type) where
  run : P → List UInt8 → Option (List UInt8)

def Computes {P α β : Type} [Program P] (program : P) (f : α → β) (encodeInput : α → List UInt8)
    (encodeOutput : β → List UInt8) : Prop :=
  ∀ argument, Program.run program (encodeInput argument) = some (encodeOutput (f argument))

/-- Code bytes and work space bound. -/
structure Compiled where
  code : List UInt8
  space : Nat → Nat

structure Call where
  returnAddress : UInt64
  inputAddress : UInt64
  inputLength : Nat
  workAddress : UInt64
  workLength : Nat
  outputAddress : UInt64
  outputLength : Nat

def readMemory (state : MachineState) (address : UInt64) (length : Nat) : Option (List UInt8) :=
  (List.range length).mapM fun offset => state.memory (address + offset.toUInt64)

/-- Every byte of the block exists. -/
def Present (state : MachineState) (address : UInt64) (length : Nat) : Prop :=
  ∀ offset < length, (state.memory (address + offset.toUInt64)).isSome

def Apart (first second : UInt64 × Nat) : Prop :=
  first.1.toNat + first.2 ≤ second.1.toNat ∨ second.1.toNat + second.2 ≤ first.1.toNat

/-- Address outside the block. -/
def Outside (address : UInt64) (block : UInt64 × Nat) : Prop :=
  address.toNat < block.1.toNat ∨ block.1.toNat + block.2 ≤ address.toNat

/-- Input, output, work, code. -/
def Call.blocks (call : Call) (codeStart : UInt64) (codeLength : Nat) : List (UInt64 × Nat) :=
  [(call.inputAddress, call.inputLength), (call.outputAddress, call.outputLength),
    (call.workAddress, call.workLength), (codeStart, codeLength)]

/-- The hypotheses on the start state. -/
structure StartCorrect (machine : Machine) (state : machine.State) (call : Call) (code input : List UInt8) :
    Prop where
  configured : machine.configured state
  codeLoaded : readMemory (machine.observe state) (machine.observe state).programCounter code.length = some code
  inputLoaded : readMemory (machine.observe state) call.inputAddress input.length = some input
  inputLength : call.inputLength = input.length
  inputSmall : input.length ≤ 2 ^ 20
  returnRegister : (machine.observe state).register machine.mapping.returnAddress = call.returnAddress
  inputRegister : (machine.observe state).register machine.mapping.inputAddress = call.inputAddress
  lengthRegister : (machine.observe state).register machine.mapping.inputLength = input.length.toUInt64
  workRegister : (machine.observe state).register machine.mapping.workAddress = call.workAddress
  workTopRegister : (machine.observe state).register machine.mapping.workTop =
    call.workAddress + call.workLength.toUInt64
  outputRegister : (machine.observe state).register machine.mapping.outputAddress = call.outputAddress
  codeAligned : (machine.observe state).programCounter.toNat % 4 = 0
  returnAligned : call.returnAddress.toNat % 4 = 0
  workAligned : call.workAddress.toNat % 8 = 0
  returnOutsideCode : Apart (call.returnAddress, 4) ((machine.observe state).programCounter, code.length)
  inRam : ∀ block ∈ call.blocks (machine.observe state).programCounter code.length,
    machine.ramStart ≤ block.1.toNat ∧ block.1.toNat + block.2 ≤ machine.ramEnd
  disjoint : (call.blocks (machine.observe state).programCounter code.length).Pairwise Apart
  outputPresent : Present (machine.observe state) call.outputAddress call.outputLength
  workPresent : Present (machine.observe state) call.workAddress call.workLength

end Proven.Top
