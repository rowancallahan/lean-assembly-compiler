/- Non-vacuity of `StartCorrect` (`Spec/Top.lean`) on the RISC-V machine: one explicit start state and call
(code at `0x80000000`, return address `0x80001000`, input `[3, 1, 2]` at `0x80002000`, output block
`[0x80004000, +0x100)`, work block `[0x80005000, +0x1000)`) meet every clause, for any code of at most 4000
bytes. -/
import Riscv.Examples.VacuityBase
import Riscv.Back.Top
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

namespace Proven.Vacuity
open Proven.Top

def topInput : List UInt8 := [3, 1, 2]

/-- block lengths, then arithmetic -/
local macro "lens" : tactic => `(tactic| ((try simp only [List.length_replicate, List.length_map, topInput,
  List.length_cons, List.length_nil, UInt64.reduceToNat] at *); omega))

def topCall : Call where
  returnAddress := 0x80001000
  inputAddress := 0x80002000
  inputLength := 3
  workAddress := 0x80005000
  workLength := 0x1000
  outputAddress := 0x80004000
  outputLength := 0x100

/-- input, zeroed output and work blocks, then the code -/
def topMemory (code : List UInt8) : Mem :=
  loadBytes (loadBytes (loadBytes (loadBytes ∅ 0x80002000 (topInput.map (·.toBitVec)))
    0x80004000 (List.replicate 0x100 0)) 0x80005000 (List.replicate 0x1000 0)) 0x80000000 (code.map (·.toBitVec))

def topState (code : List UInt8) : St :=
  witness 0x80000000#64 0x80001000#64 0x80006000#64 0x80002000#64 3#64 0x80005000#64 0x80004000#64
    (topMemory code)

theorem topState_pc (code : List UInt8) : (riscvObserve (topState code)).programCounter = 0x80000000 := by
  simp only [riscvObserve, topState, witness_pc]; rfl

theorem topMemory_high {code : List UInt8} (hlength : code.length ≤ 4000) {address : Nat}
    (haddress : 0x80001000 ≤ address) : (topMemory code)[address]? =
      (loadBytes (loadBytes (loadBytes ∅ 0x80002000 (topInput.map (·.toBitVec)))
        0x80004000 (List.replicate 0x100 0)) 0x80005000 (List.replicate 0x1000 0))[address]? := by
  rw [topMemory, load_get_other]; lens

theorem present_of {code : List UInt8} {base : UInt64} {length : Nat} (hbound : base.toNat + length ≤ 2 ^ 64)
    (h : ∀ offset < length, ((topMemory code)[base.toNat + offset]?).isSome) :
    Present (riscvObserve (topState code)) base length := fun offset hoffset => by
  simp only [riscvObserve, Option.isSome_map]
  rw [toNat_add_offset hbound hoffset]; exact h offset hoffset

/-- **`StartCorrect` is satisfiable** for every code of at most 4000 bytes -/
theorem startCorrect_nonvacuous {code : List UInt8} (hlength : code.length ≤ 4000) :
    StartCorrect riscv (topState code) topCall code topInput := by
  have hpc := topState_pc code
  refine ⟨witness_cfg .., ?_, ?_, rfl, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, ?_, ?_, ?_,
    ?_, ?_⟩
  all_goals try change riscvObserve (topState code) = _ at *
  · show readMemory (riscvObserve (topState code)) (riscvObserve (topState code)).programCounter _ = _
    rw [hpc, readMemory_riscv _ _ (by lens), bytesAt_eq]
    show memAt (topMemory code) 0x80000000 code.length = _
    rw [topMemory, show code.length = (code.map (·.toBitVec)).length by simp, memAt_load_self]; simp
  · show readMemory (riscvObserve (topState code)) 0x80002000 3 = _
    rw [readMemory_riscv _ _ (by lens), bytesAt_eq]
    show memAt (topMemory code) 0x80002000 3 = _
    rw [topMemory, memAt_load_other _ _ _ _ _ (by lens), memAt_load_other _ _ _ _ _ (by lens),
      memAt_load_other _ _ _ _ _ (by lens), show 3 = (topInput.map (·.toBitVec)).length by rfl, memAt_load_self]
    simp [topInput]
  · show ((riscvRegister (topState code) 1).map UInt64.ofBitVec).getD 0 = _
    simp only [riscvRegister, topState, witness_x1]; rfl
  · show ((riscvRegister (topState code) 10).map UInt64.ofBitVec).getD 0 = _
    simp only [riscvRegister, topState, witness_x10]; rfl
  · show ((riscvRegister (topState code) 11).map UInt64.ofBitVec).getD 0 = _
    simp only [riscvRegister, topState, witness_x11]; rfl
  · show ((riscvRegister (topState code) 12).map UInt64.ofBitVec).getD 0 = _
    simp only [riscvRegister, topState, witness_x12]; rfl
  · show ((riscvRegister (topState code) 2).map UInt64.ofBitVec).getD 0 = _
    simp only [riscvRegister, topState, witness_x2]; rfl
  · show ((riscvRegister (topState code) 13).map UInt64.ofBitVec).getD 0 = _
    simp only [riscvRegister, topState, witness_x13]; rfl
  · show (riscvObserve (topState code)).programCounter.toNat % 4 = 0
    rw [hpc]; rfl
  · show Apart _ ((riscvObserve (topState code)).programCounter, _)
    rw [hpc]; simp only [Apart, topCall]; lens
  · show ∀ block ∈ topCall.blocks (riscvObserve (topState code)).programCounter code.length, _
    rw [hpc]
    simp only [Call.blocks, topCall, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    show (0x80000000 ≤ 0x80002000 ∧ 0x80002000 + 3 ≤ 0x100000000) ∧
      (0x80000000 ≤ 0x80004000 ∧ 0x80004000 + 0x100 ≤ 0x100000000) ∧
      (0x80000000 ≤ 0x80005000 ∧ 0x80005000 + 0x1000 ≤ 0x100000000) ∧
      0x80000000 ≤ 0x80000000 ∧ 0x80000000 + code.length ≤ 0x100000000
    omega
  · show (topCall.blocks (riscvObserve (topState code)).programCounter code.length).Pairwise Apart
    rw [hpc]
    simp only [Call.blocks, topCall, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, Apart, false_implies, implies_true]
    lens
  · refine present_of (by decide) fun offset (hoffset : offset < 0x100) => ?_
    rw [show topCall.outputAddress.toNat + offset = 0x80004000 + offset from rfl,
      topMemory_high hlength (by lens), load_get_other _ _ _ _ (by lens), load_get_in _ _ _ _ (by lens)]; rfl
  · refine present_of (by decide) fun offset (hoffset : offset < 0x1000) => ?_
    rw [show topCall.workAddress.toNat + offset = 0x80005000 + offset from rfl,
      topMemory_high hlength (by lens), load_get_in _ _ _ _ (by lens)]; rfl

end Proven.Vacuity
