/- Programs with run-time memory checks on RISC-V (`Compiler/MemCode.lean`, `Riscv/Back/MemRv.lean`), from the
machine facts of a call to the facts the top-level statements (`Compiler/AllocSpec.lean`) need.

`memRaw`: in the shape of `Implements1With` (registers, memory, regions): the code returns to the caller; it
writes only the output block and the work block; if the run's cells in use (its events plus the entry stub's two
cells, 8 bytes each) fit the work block, the output block holds the run's output block and `a0` the input
address, else `a0 = -1`.  `memSpec`: the same from `StartCorrect` (`Spec/Top.lean`). -/
import Legacy.Riscv.Back.MemRv
import Legacy.Riscv.Back.CallsImpl1W
import Nano.Base.Riscv.Back.Top
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven.Mach.Riscv
open Proven.Top.Alloc

/-- the heap base: global 2 (`a2`) -/
def wb2 : Fin 8 := ⟨2, by decide⟩

/-- the code of a program with run-time memory checks; byte blocks in `a0` (input) and `a3` (output), the
heap at the bottom of the work block (base in `a2`), its length in `a7` -/
def memCode (P : Prog) (res main : Nat) : List (BitVec 32) := rvM.codeZ (rvM.compPM P [0, 3] wb2 res main)

/-- well-formedness for `memCode` -/
def WfMem (P : Prog) (res main : Nat) : Prop := rvM.WfPM P [0, 3] wb2 res main

theorem allOnes_ne_small {a : Nat} (h : a < 2 ^ 32) : BitVec.ofNat 64 a ≠ BitVec.allOnes 64 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_allOnes] at this
  omega

/-- **Programs with run-time memory checks on the Sail model**, from the machine facts of a call -/
theorem memRaw {P : Prog} {res main : Nat} (hwf : WfMem P res main) (hP : progClean P = true)
    (hres : (!unread.contains res) = true) (x : List UInt8) (s : St) (entry ra : BitVec 64)
    (input output work : Proven.Region)
    (hmax : x.length ≤ 2 ^ 20) (h : Cfg s) (hpc : s.regs.get? .PC = some entry) (hal : entry.toNat % 4 = 0)
    (hcode : bytesAt s entry.toNat (4 * (memCode P res main).length) = codeBytes (memCode P res main))
    (h10 : s.regs.get? .x10 = some (BitVec.ofNat 64 input.base))
    (h11 : s.regs.get? .x11 = some (BitVec.ofNat 64 x.length))
    (h12 : s.regs.get? .x12 = some (BitVec.ofNat 64 work.base))
    (h13 : s.regs.get? .x13 = some (BitVec.ofNat 64 output.base))
    (h2 : s.regs.get? .x2 = some (BitVec.ofNat 64 (work.base + work.len)))
    (h1 : s.regs.get? .x1 = some ra) (hra : ra.toNat % 4 = 0)
    (hrad : Proven.disjoint ⟨ra.toNat, 4⟩ ⟨entry.toNat, 4 * (memCode P res main).length⟩)
    (hx : bytesAt s input.base x.length = x.map (some ·.toBitVec)) (hil : input.len = x.length)
    (hwal : work.base % 8 = 0)
    (hram : ∀ r ∈ [input, output, work, (⟨entry.toNat, 4 * (memCode P res main).length⟩ : Proven.Region)], r.inRAM)
    (hdis : [input, output, work, (⟨entry.toNat, 4 * (memCode P res main).length⟩ : Proven.Region)].Pairwise
      Proven.disjoint)
    (hmapO : Mapped s output) (hmapW : Mapped s work) :
    ∃ out0 : List (BitVec 8), out0.length = output.len ∧
      ∀ {E : List MemEvent} {σ' : BState},
        TExec P (.call res main []) ⟨stubEnv (envOf s), [x.map (·.toBitVec), out0], [[]]⟩ E σ' →
        runsTo s fun s' => s'.regs.get? .PC = some ra ∧ Cfg s' ∧ unchangedOutside s s' [output, work] ∧
          ((8 * peak (E ++ [.alloc 2]) ≤ work.len ∧ getX s' 10 = BitVec.ofNat 64 input.base ∧
              bytesAt s' output.base output.len = (σ'.heap[1]?.getD []).map some) ∨
            (work.len < 8 * peak (E ++ [.alloc 2]) ∧ getX s' 10 = BitVec.allOnes 64)) := by
  have hin : ∀ r ∈ [input, output, work, (⟨entry.toNat, 4 * (memCode P res main).length⟩ : Proven.Region)],
    r.inRAM := hram
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true] at hdis
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := hdis
  obtain ⟨ri, ro, rw', rc⟩ := hin
  unfold Region.inRAM at ri ro rw' rc
  unfold Proven.disjoint at d12 d13 d14 d23 d24 d34
  dsimp only at d14 d24 d34 rc
  have hil' : input.len = x.length := hil
  have hsp : getX s 2 = BitVec.ofNat 64 (work.base + work.len) := getX_of (h.x2.symm.trans h2) rfl
  have hspn : (getX s 2).toNat = work.base + work.len := by rw [hsp]; exact toNat_ofNat' (by omega)
  have hfb : frameBase 0 (getX s 2) = (work.base + work.len) / 8 * 8 - 8 := by unfold frameBase; rw [hspn]
  have hok : codeOK entry (memCode P res main).length := ⟨hal, rc.1, rc.2⟩
  obtain ⟨out0, hout0l, ho⟩ : ∃ out0 : List (BitVec 8), out0.length = output.len ∧
      bytesAt s output.base output.len = out0.map some :=
    ⟨_, by simp [bytesAt], bytesAt_hosted fun i hi => hmapO i hi⟩
  refine ⟨out0, hout0l, fun {E σ'} hexec => ?_⟩
  have hfA : rvM.frameAt s 0 = (work.base + work.len) / 8 * 8 - 8 := hfb
  let R : List Mach.Region := [⟨input.base, x.length⟩, ⟨output.base, output.len⟩]
  have hL : rvM.PLayM entry (memCode P res main).length R work.base (rvM.frameAt s 0 + 8) := by
    rw [hfA]
    refine ⟨fun r hr => ?_, ?_, hwal, by omega, ?_, fun r hr => ?_, fun r hr => ?_, fun r hr q h1 h2 _ _ => ?_,
      fun q h1 h2 _ _ => ?_, ?_⟩
    · simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (show 0x80000000 ≤ _ ∧ _ ≤ 0x100000000; dsimp only; omega)
    · simp only [R, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq, List.Pairwise.nil,
        and_true, false_implies, implies_true]
      unfold Mach.disjoint; dsimp only; omega
    · show 0x80000000 ≤ _ ∧ _ ≤ 0x100000000; omega
    · simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> (unfold Mach.disjoint; dsimp only; omega)
    · simp only [R, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · unfold Mach.disjoint; dsimp only; omega
      · unfold Mach.disjoint; dsimp only; omega
      · unfold Mach.disjoint; dsimp only; omega
    · simp only [R, List.mem_cons, List.not_mem_nil, or_false] at hr
      show 0x80000000 ≤ q ∧ q + 1 ≤ 0x100000000
      rcases hr with rfl | rfl <;> (dsimp only at h1 h2; omega)
    · show 0x80000000 ≤ q ∧ q + 1 ≤ 0x100000000; omega
    · show 8 * (NS + 1) ≤ work.base; simp only [NS]; omega
  have hra' : getX s 1 = ra := getX_of (h.x1.symm.trans h1) rfl
  have hwb : envOf s wb2.val = BitVec.ofNat 64 work.base := by
    simp [envOf, wb2]; exact getX_of (h.x12.symm.trans h12) rfl
  refine runsTo_mono (rvM.compPM_ok hP hres hexec ⟨h, hpc, codeAt_of_codeBytes hok hcode, hok⟩ hwf
    (by intro x hx; simp at hx; omega) (by decide) (by decide)
    (fun hfit => by
      show FrOK 0 (frameBase 0 (getX s 2))
      rw [hfb]; rw [hfA] at hfit
      exact ⟨by omega, by omega, by omega, by simp [NS]⟩)
    hL (fun i => by show getX s (phys (avar i)) = _; rw [phys_avar]; simp [envOf]) hwb rfl rfl
    (fun b hb => by
      obtain _ | _ | b := b
      · simp [envOf]; exact getX_of (h.x10.symm.trans h10) rfl
      · simp [envOf]; exact getX_of (h.x13.symm.trans h13) rfl
      · exact absurd hb (by show ¬(b + 1 + 1 < 2); omega))
    (fun b hb => by
      obtain _ | _ | b := b
      · simp [R]
      · simpa [R] using hout0l
      · exact absurd hb (by show ¬(b + 1 + 1 < 2); omega))
    (fun b hb => by
      obtain _ | _ | b := b
      · show bytes (rv.mem s) input.base x.length = _
        exact (bytes_eq s _ _).trans (by simpa [List.map_map, Function.comp_def] using hx)
      · show bytes (rv.mem s) output.base output.len = _
        exact (bytes_eq s _ _).trans (by simpa using ho)
      · exact absurd hb (by show ¬(b + 1 + 1 < 2); omega))
    (by show (getX s 1).toNat % 2 = 0; rw [hra']; omega)
    (by rw [hfA]; omega)) ?_
  rintro s' ⟨p1, p2, p3, p4⟩
  have hA : (rvM.frameAt s 0 + 8 - work.base) / 8 = work.len / 8 := by rw [hfA]; omega
  rw [hA] at p4
  refine ⟨by rw [← hra']; exact p1, p2, fun q hq => ?_, ?_⟩
  · have a2 := hq output (by simp); have a3 := hq work (by simp)
    apply p3 q
    intro r hr
    rw [hfA] at hr
    simp only [R, List.drop_succ_cons, List.drop_zero, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> omega
  · rcases p4 with ⟨pk, rg, W', hb⟩ | ⟨pk, a0⟩
    · refine .inl ⟨by omega, ?_, ?_⟩
      · have := rg ⟨0, by decide⟩
        rw [show rvM.get s' (avar ⟨0, by decide⟩) = getX s' 10 from rfl] at this
        rw [this]; have := hb.base 0 (by simp [R]); simpa [R] using this
      · have := hb.rbytes 1 (by simp [R])
        exact (bytes_eq s' _ _).symm.trans (by simp [R] at this ⊢; exact this)
    · refine .inr ⟨by omega, ?_⟩
      rw [show getX s' 10 = rvM.get s' (avar 0) from rfl, a0]

end Proven.Mach.Riscv

namespace Proven.Top
open Proven.Mach Proven.Mach.Riscv Proven.Top.Alloc

/-- **Programs with run-time memory checks, from `StartCorrect`**: for the run with events of `res := main()`
from the input, the machine's output block and the globals of the call, the code returns to the caller, changes
nothing outside the output and work blocks, and either the cells fit (`8 * peak ≤ workLength`; the output block
holds the run's, the status register is not the flag) or not (the status register holds the flag). -/
theorem memSpec {P : Prog} {res main : Nat} (hwf : WfMem P res main) (hP : progClean P = true)
    (hres : (!unread.contains res) = true) {inp : List UInt8} {startState : riscv.State} {call : Call}
    (startsRight : StartCorrect riscv startState call (wordBytes (memCode P res main)) inp) :
    ∃ (env : Mach.BEnv) (out0 : List (BitVec 8)), env 1 = BitVec.ofNat 64 inp.length ∧ (∀ i, 8 ≤ i → env i = 0) ∧
      out0.length = call.outputLength ∧
      ∀ {E : List MemEvent} {σ' : Mach.BState},
        TExec P (.call res main []) ⟨stubEnv env, [inp.map (·.toBitVec), out0], [[]]⟩ E σ' →
        ∃ finishState, Runs riscv startState finishState ∧
          (riscv.observe finishState).programCounter = call.returnAddress ∧
          (∀ address, Outside address (call.outputAddress, call.outputLength) →
            Outside address (call.workAddress, call.workLength) →
            (riscv.observe finishState).memory address = (riscv.observe startState).memory address) ∧
          ((8 * peak (E ++ [.alloc 2]) ≤ call.workLength ∧
              (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
              readMemory (riscv.observe finishState) call.outputAddress call.outputLength =
                some ((σ'.heap[1]?.getD []).map UInt8.ofBitVec)) ∨
            (call.workLength < 8 * peak (E ++ [.alloc 2]) ∧
              (riscv.observe finishState).register riscv.mapping.status = oomFlag)) := by
  obtain ⟨configured, codeLoaded, inputLoaded, inputLength, inputSmall, returnRegister, inputRegister,
    lengthRegister, workRegister, workTopRegister, outputRegister, codeAligned, returnAligned, workAligned,
    returnOutsideCode, inRam, disjoint, outputPresent, workPresent⟩ := startsRight
  change Cfg startState at configured
  have eObserve : riscv.observe = riscvObserve := rfl
  have eMapping : riscv.mapping = riscvMapping := rfl
  have eStart : riscv.ramStart = 0x80000000 := rfl
  have eEnd : riscv.ramEnd = 0x100000000 := rfl
  simp only [eObserve, eMapping, eStart, eEnd, riscvMapping, Call.blocks, wordBytes_length] at *
  generalize hpc : (riscvObserve startState).programCounter = pc at *
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at inRam
  obtain ⟨⟨ri1, ri2⟩, ⟨ro1, ro2⟩, ⟨rw1, rw2⟩, ⟨rc1, rc2⟩⟩ := inRam
  have hreg := fun (register : Register) hregister => isSome_of_cfg configured (register := register) hregister
  have hpcReg := register_of (hreg .PC (by simp)) hpc
  have hentry : (BitVec.ofNat 64 pc.toNat).toNat = pc.toNat := by simp
  have hra : (BitVec.ofNat 64 call.returnAddress.toNat).toNat = call.returnAddress.toNat := by simp
  have hcode := (readMemory_riscv startState (address := pc) (length := (wordBytes (memCode P res main)).length) _
    (by rw [wordBytes_length]; omega)).1 (by rw [wordBytes_length]; exact codeLoaded)
  rw [wordBytes_length, wordBytes_codeBytes] at hcode
  have hinput := (readMemory_riscv startState (address := call.inputAddress) _ (by omega)).1 inputLoaded
  have h11 : startState.regs.get? .x11 = some (BitVec.ofNat 64 inp.length) := by
    have := register_of (hreg .x11 (by simp)) lengthRegister
    rw [this, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have h2 : startState.regs.get? .x2 = some (BitVec.ofNat 64 (call.workAddress.toNat + call.workLength)) := by
    have := register_of (hreg .x2 (by simp)) workTopRegister
    rw [this, toNat_add_offset (bound := call.workLength + 1) (by omega) (by omega)]
  have h10 := register_of (hreg .x10 (by simp)) inputRegister
  have h12 := register_of (hreg .x12 (by simp)) workRegister
  have h13 := register_of (hreg .x13 (by simp)) outputRegister
  have h1 := register_of (hreg .x1 (by simp)) returnRegister
  obtain ⟨out0, hl0, run⟩ := memRaw hwf hP hres inp startState (BitVec.ofNat 64 pc.toNat)
    (BitVec.ofNat 64 call.returnAddress.toNat)
    ⟨call.inputAddress.toNat, call.inputLength⟩ ⟨call.outputAddress.toNat, call.outputLength⟩
    ⟨call.workAddress.toNat, call.workLength⟩ inputSmall configured hpcReg (by rw [hentry]; exact codeAligned)
    (by rw [hentry]; exact hcode) h10 h11 h12 h13 h2 h1 (by rw [hra]; exact returnAligned)
    (by rw [hra, hentry]; exact returnOutsideCode) hinput inputLength workAligned
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Region.inRAM, hentry]
      omega)
    (by
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        List.Pairwise.nil, and_true, Proven.disjoint, Apart, hentry, false_implies, implies_true] at disjoint ⊢
      simpa only [] using disjoint)
    (fun offset (hoffset : offset < call.outputLength) => by
      have := outputPresent offset hoffset
      simp only [riscvObserve, Option.isSome_map] at this
      rwa [toNat_add_offset (by omega) hoffset] at this)
    (fun offset (hoffset : offset < call.workLength) => by
      have := workPresent offset hoffset
      simp only [riscvObserve, Option.isSome_map] at this
      rwa [toNat_add_offset (by omega) hoffset] at this)
  refine ⟨envOf startState, out0, ?_, fun i hi => ?_, hl0, fun {E σ'} hexec => ?_⟩
  · simp [envOf]; exact getX_of (configured.x11.symm.trans h11) rfl
  · simp only [envOf]; rw [dif_neg (by omega)]
  obtain ⟨steps, finishState, hsteps, hpcF, hcfg, hun, hcase⟩ := run hexec
  refine ⟨finishState, runs_of_steps steps _ _ hsteps, ?_, ?_, ?_⟩
  · simp [riscvObserve, hpcF]
  · intro address hout hwork
    simp only [riscvObserve]
    rw [hun address.toNat (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hout, hwork⟩)]
  · have hx10 : ∀ v, getX finishState 10 = v → (riscvObserve finishState).register 10 = UInt64.ofBitVec v := by
      intro v hv; simp only [riscvObserve, riscvRegister, hcfg.x10, hv, Option.map_some, Option.getD_some]
    rcases hcase with ⟨pk, a0, bo⟩ | ⟨pk, a0⟩
    · refine .inl ⟨pk, ?_, ?_⟩
      · rw [hx10 _ a0]
        intro e
        have := congrArg UInt64.toNat e
        rw [UInt64.toNat_ofBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt64.toNat_lt _)] at this
        have h2 : oomFlag.toNat = 2 ^ 64 - 1 := rfl
        omega
      · have hl : (σ'.heap[1]?.getD []).length = call.outputLength := by
          have := congrArg List.length bo; simp [bytesAt] at this; omega
        rw [← hl]
        refine (readMemory_riscv finishState _ (by rw [hl]; omega)).2 ?_
        rw [hl, bo, List.map_map]
        exact List.map_congr_left fun _ _ => rfl
    · refine .inr ⟨pk, ?_⟩
      rw [hx10 _ a0]; rfl

end Proven.Top
