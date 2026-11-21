/- DeepMind's AArch64 model (google-deepmind/code-verification, `Arm64`) as a Machine, with its page permissions.
Built by Arm/apc (not the root project, which does not have the model). -/
import Spec.Top
import Spec.Machines
import Arm64

namespace Proven.Top

/-- A program with no system calls. -/
def armDMProgram : Arm64.Program := Arm64.Program.ofSvc Arm64.noSyscalls

/-- Fetch, decode and execute one instruction while running, else none. -/
def armDMStep (state : Arm64.State) : Option Arm64.State :=
  match state.status with
  | .Running => (armDMProgram.fetchMem state.mem state.pc).map fun i => armDMProgram.evalInst i state
  | _ => none

/-- X0–X30, register 31 = sp; only mapped bytes are visible. -/
def armDMObserve (state : Arm64.State) : MachineState where
  programCounter := UInt64.ofBitVec state.pc
  register number :=
    if number < 31 then UInt64.ofBitVec (state.regs.read (BitVec.ofNat 5 number))
    else if number = 31 then UInt64.ofBitVec state.sp else 0
  memory address :=
    if (state.mem.perm address.toBitVec).isSome then some (UInt8.ofBitVec (state.mem.read8 address.toBitVec)) else none

def armDM : Machine where
  State := Arm64.State
  step := armDMStep
  observe := armDMObserve
  configured state := state.status = .Running
  mapping := armMapping
  ramStart := 0x80000000
  ramEnd := 0xC0000000

/-- Byte executable. -/
def ArmDMExecutable (state : Arm64.State) (address : Nat) : Prop :=
  state.mem.canExec (BitVec.ofNat 64 address) 1 = true

/-- Byte readable and writable. -/
def ArmDMWritable (state : Arm64.State) (address : Nat) : Prop :=
  state.mem.canRead (BitVec.ofNat 64 address) 1 = true ∧ state.mem.canWrite (BitVec.ofNat 64 address) 1 = true

end Proven.Top
