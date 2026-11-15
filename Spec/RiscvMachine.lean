/- Sail RV64 model as a Machine. -/
import Spec.Top
import Spec.Implements1
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

namespace Proven.Top

/-- Integer register by number. -/
def riscvRegister (state : St) (number : Nat) : Option (BitVec 64) :=
  match number with
  | 1 => state.regs.get? .x1 | 2 => state.regs.get? .x2 | 3 => state.regs.get? .x3
  | 4 => state.regs.get? .x4 | 5 => state.regs.get? .x5 | 6 => state.regs.get? .x6
  | 7 => state.regs.get? .x7 | 8 => state.regs.get? .x8 | 9 => state.regs.get? .x9
  | 10 => state.regs.get? .x10 | 11 => state.regs.get? .x11 | 12 => state.regs.get? .x12
  | 13 => state.regs.get? .x13 | 14 => state.regs.get? .x14 | 15 => state.regs.get? .x15
  | 16 => state.regs.get? .x16 | 17 => state.regs.get? .x17 | 18 => state.regs.get? .x18
  | 19 => state.regs.get? .x19 | 20 => state.regs.get? .x20 | 21 => state.regs.get? .x21
  | 22 => state.regs.get? .x22 | 23 => state.regs.get? .x23 | 24 => state.regs.get? .x24
  | 25 => state.regs.get? .x25 | 26 => state.regs.get? .x26 | 27 => state.regs.get? .x27
  | 28 => state.regs.get? .x28 | 29 => state.regs.get? .x29 | 30 => state.regs.get? .x30
  | 31 => state.regs.get? .x31
  | _ => none

/-- Missing values read as zero. -/
def riscvObserve (state : St) : MachineState where
  programCounter := ((state.regs.get? .PC).map UInt64.ofBitVec).getD 0
  register number := ((riscvRegister state number).map UInt64.ofBitVec).getD 0
  memory address := (state.mem[address.toNat]?).map UInt8.ofBitVec

/-- One retired instruction, else none. -/
noncomputable def riscvStep (state : St) : Option St :=
  match run_hart_active 0 state, try_step 0 false state with
  | .ok (.Step_Execute (.Retire_Success (), _)) _, .ok false next => some next
  | _, _ => none

noncomputable def riscv : Machine where
  State := St
  step := riscvStep
  observe := riscvObserve
  configured := Cfg
  mapping := riscvMapping
  ramStart := 0x80000000
  ramEnd := 0x100000000

end Proven.Top
