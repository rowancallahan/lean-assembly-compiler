/- The top-level statement `Spec/Top.lean` for RISC-V, from `Implements1` (`Spec/Implements1.lean`).

`implements1_top` is the one adapter: any `Implements1With encA encB code f space` code, loaded as the bytes
`wordBytes code`, satisfies the top-level conclusion (run to the return address, result in the output block)
and the frame facts.  `compile` is the `XPipe` compiler `compileX1` (the list front end, `compile%`), and
`compile_correct` / `compile_frame` are the owner's statements for it. -/
import Nano.Base.Compiler.Front.PipeIMachine
import Spec.RiscvMachine
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

namespace Proven.Top

/-- the little-endian bytes of the instruction words -/
def wordBytes (code : List (BitVec 32)) : List UInt8 :=
  code.flatMap fun w =>
    [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8].map UInt8.ofBitVec

theorem wordBytes_codeBytes (code : List (BitVec 32)) :
    (wordBytes code).map (some ·.toBitVec) = codeBytes code := by
  simp [wordBytes, codeBytes, List.map_flatMap]

theorem wordBytes_length (code : List (BitVec 32)) : (wordBytes code).length = 4 * code.length := by
  induction code with
  | nil => rfl
  | cons w ws ih => simp [wordBytes] at ih ⊢; omega

theorem mapM_some (g : Nat → Option UInt8) :
    ∀ (offsets : List Nat) (bytes : List UInt8), offsets.mapM g = some bytes ↔ offsets.map g = bytes.map some
  | [], [] => by simp
  | [], _ :: _ => by simp
  | offset :: offsets, bytes => by
    rw [List.mapM_cons]
    cases hg : g offset with
    | none => cases bytes <;> simp [hg]
    | some byte =>
      cases bytes with
      | nil => cases hm : offsets.mapM g <;> simp_all
      | cons first rest =>
        have := mapM_some g offsets rest
        cases hm : offsets.mapM g <;> simp_all

theorem toNat_add_offset {address : UInt64} {offset bound : Nat} (hbound : address.toNat + bound ≤ 2 ^ 64)
    (hoffset : offset < bound) : (address + offset.toUInt64).toNat = address.toNat + offset := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem toBitVec_comp_ofBitVec : UInt8.toBitVec ∘ UInt8.ofBitVec = id := rfl
theorem ofBitVec_comp_toBitVec : UInt8.ofBitVec ∘ UInt8.toBitVec = id := rfl

theorem readMemory_riscv (state : St) {address : UInt64} {length : Nat} (bytes : List UInt8)
    (hbound : address.toNat + length ≤ 2 ^ 64) :
    readMemory (riscvObserve state) address length = some bytes ↔
      bytesAt state address.toNat length = bytes.map (some ·.toBitVec) := by
  have hmap : (List.range length).map (fun offset => (riscvObserve state).memory (address + offset.toUInt64)) =
      ((List.range length).map (state.mem[address.toNat + ·]?)).map (Option.map UInt8.ofBitVec) := by
    rw [List.map_map]
    refine List.map_congr_left fun offset hoffset => ?_
    simp only [riscvObserve, Function.comp]
    rw [toNat_add_offset hbound (List.mem_range.1 hoffset)]
  rw [readMemory, mapM_some, hmap, bytesAt]
  constructor
  · intro h
    have := congrArg (List.map (Option.map UInt8.toBitVec)) h
    simp only [List.map_map] at this
    refine Eq.trans (List.map_congr_left fun offset _ => ?_) (this.trans (List.map_congr_left fun _ _ => rfl))
    simp only [Function.comp]; cases state.mem[address.toNat + offset]? <;> rfl
  · intro h
    rw [h]; simp only [List.map_map]; exact List.map_congr_left fun _ _ => rfl

theorem register_of {value : Option (BitVec 64)} {target : UInt64} (hsome : value.isSome)
    (h : (value.map UInt64.ofBitVec).getD 0 = target) : value = some (BitVec.ofNat 64 target.toNat) := by
  cases value with
  | none => simp at hsome
  | some v => subst h; simp

theorem isSome_of_cfg {state : St} (configured : Cfg state) {register : Register}
    (hregister : register ∈ [Register.mideleg, .mip, .mie, .sig_meip, .sig_seip, .pmpaddr_n, .minstret, .PC,
      .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
      .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30, .x31]) :
    (state.regs.get? register).isSome := by
  rw [Std.ExtDHashMap.isSome_get?_eq_contains]; exact configured.present _ hregister

theorem step_of_retires {state next : St} (h : Retires state next) : riscv.step state = some next := by
  obtain ⟨⟨_, _, hrun⟩, htry⟩ := h
  show riscvStep state = some next
  unfold riscvStep; rw [hrun, htry]

theorem runs_of_steps : ∀ (n : Nat) (state finish : St), Steps n state finish → Runs riscv state finish
  | 0, _, _, h => by cases h; exact .stop
  | n + 1, _, _, ⟨_, hretires, hsteps⟩ => .step (step_of_retires hretires) (runs_of_steps n _ _ hsteps)

/-- **The adapter**: `Implements1With` code satisfies the top-level conclusion and the frame facts. -/
theorem implements1_top {α β : Type} {encA : α → List UInt8} {encB : β → List UInt8}
    {code : List (BitVec 32)} {f : α → β} {space : Nat → Nat} {retLen : Bool}
    (implements : Implements1With encA encB code f space (retLen := retLen))
    {argument : α} {startState : St} {call : Call}
    (startsRight : StartCorrect riscv startState call (wordBytes code) (encA argument))
    (outputFits : (encB (f argument)).length ≤ call.outputLength)
    (enoughWorkSpace : space (encA argument).length ≤ call.workLength) :
    ∃ finishState : St,
      Runs riscv startState finishState ∧
      (riscvObserve finishState).programCounter = call.returnAddress ∧
      readMemory (riscvObserve finishState) call.outputAddress (encB (f argument)).length
        = some (encB (f argument)) ∧
      (∀ address, Outside address (call.outputAddress, (encB (f argument)).length) →
        Outside address (call.workAddress, call.workLength) →
        (riscvObserve finishState).memory address = (riscvObserve startState).memory address) ∧
      (∀ number ∈ riscvMapping.kept,
        (riscvObserve finishState).register number = (riscvObserve startState).register number) ∧
      Cfg finishState ∧
      (retLen = true →
        (riscvObserve finishState).register riscvMapping.outputLength = (encB (f argument)).length.toUInt64) := by
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
  have hcode := (readMemory_riscv startState (address := pc) (length := (wordBytes code).length) _
    (by rw [wordBytes_length]; omega)).1 (by rw [wordBytes_length]; exact codeLoaded)
  rw [wordBytes_length, wordBytes_codeBytes] at hcode
  have hinput := (readMemory_riscv startState (address := call.inputAddress) _ (by omega)).1 inputLoaded
  have run := implements argument startState (BitVec.ofNat 64 pc.toNat) (BitVec.ofNat 64 call.returnAddress.toNat)
    ⟨call.inputAddress.toNat, call.inputLength⟩ ⟨call.outputAddress.toNat, call.outputLength⟩
    ⟨call.workAddress.toNat, call.workLength⟩ inputSmall configured hpcReg (by rw [hentry]; exact codeAligned) (by rw [hentry]; exact hcode)
    (register_of (hreg .x10 (by simp)) inputRegister)
    (by have := register_of (hreg .x11 (by simp)) lengthRegister
        rw [this, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)])
    (register_of (hreg .x12 (by simp)) workRegister)
    (register_of (hreg .x13 (by simp)) outputRegister)
    (by have := register_of (hreg .x2 (by simp)) workTopRegister
        rw [this, toNat_add_offset (bound := call.workLength + 1) (by omega) (by omega)])
    (register_of (hreg .x1 (by simp)) returnRegister) (by rw [hra]; exact returnAligned)
    (by rw [hra, hentry]; exact returnOutsideCode) hinput inputLength outputFits
    enoughWorkSpace workAligned
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
  obtain ⟨steps, finishState, hsteps, hpcFinish, hout, hunchanged, hkept, hcfg, hlen⟩ := run
  refine ⟨finishState, runs_of_steps steps _ _ hsteps, ?_, ?_, ?_, ?_, hcfg, ?_⟩
  · simp [riscvObserve, hpcFinish]
  · exact (readMemory_riscv finishState (address := call.outputAddress) _ (by omega)).2 hout
  · intro address hout hwork
    simp only [riscvObserve]
    rw [hunchanged address.toNat (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hout, hwork⟩)]
  · intro number hnumber
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hnumber
    simp only [abiSavedKept, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hkept
    obtain ⟨k2, k3, k4, k8, k9, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27⟩ := hkept
    rcases hnumber with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [riscvObserve, riscvRegister, k2, k3, k4, k8, k9, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27]
  · intro hret
    simp only [riscvObserve, riscvRegister, hlen hret, Option.map_some, Option.getD_some]; rfl

/-! ## The `XPipe` compiler -/

/-- an `XPipe` runs as its denotation (it never fails) -/
instance : Program XPipe := ⟨fun program input => some (program.denote input)⟩

/-- `compileX1` with the code as bytes and the work space bound `XPipe.space1` -/
def compile (program : XPipe) : Option Compiled :=
  match compileX1 program with
  | .ok code => some ⟨wordBytes code, XPipe.space1 program⟩
  | .error _ => none

theorem compile_inv {program : XPipe} {compiled : Compiled} (compiles : compile program = some compiled) :
    ∃ code, compileX1 program = .ok code ∧ compiled = ⟨wordBytes code, XPipe.space1 program⟩ := by
  unfold compile at compiles
  split at compiles
  · next code h => exact ⟨code, h, (Option.some.inj compiles).symm⟩
  · exact nomatch compiles

theorem compile_top {program : XPipe} {compiled : Compiled} {α β : Type} {f : α → β}
    {encodeInput : α → List UInt8} {encodeOutput : β → List UInt8} {argument : α} {startState : riscv.State}
    {call : Call}
    (compiles : compile program = some compiled)
    (computes : Computes program f encodeInput encodeOutput)
    (startsRight : StartCorrect riscv startState call compiled.code (encodeInput argument))
    (outputFits : (encodeOutput (f argument)).length ≤ call.outputLength)
    (enoughWorkSpace : compiled.space (encodeInput argument).length ≤ call.workLength) :
    ∃ finishState : St,
      Runs riscv startState finishState ∧
      (riscvObserve finishState).programCounter = call.returnAddress ∧
      readMemory (riscvObserve finishState) call.outputAddress (encodeOutput (f argument)).length
        = some (encodeOutput (f argument)) ∧
      (∀ address, Outside address (call.outputAddress, (encodeOutput (f argument)).length) →
        Outside address (call.workAddress, call.workLength) →
        (riscvObserve finishState).memory address = (riscvObserve startState).memory address) ∧
      (∀ number ∈ riscvMapping.kept,
        (riscvObserve finishState).register number = (riscvObserve startState).register number) ∧
      Cfg finishState ∧
      (riscvObserve finishState).register riscvMapping.outputLength
        = (encodeOutput (f argument)).length.toUInt64 := by
  obtain ⟨code, hcode, rfl⟩ := compile_inv compiles
  have hrun : program.denote (encodeInput argument) = encodeOutput (f argument) :=
    Option.some.inj (computes argument)
  have := implements1_top (argument := encodeInput argument) (compileX1_ok hcode) startsRight
    (by simpa only [encRaw, hrun] using outputFits) enoughWorkSpace
  simp only [encRaw, hrun] at this
  obtain ⟨finishState, h1, h2, h3, h4, h5, h6, h7⟩ := this
  exact ⟨finishState, h1, h2, h3, h4, h5, h6, h7 trivial⟩

/-- **The top-level theorem** for the RISC-V `XPipe` compiler (`Spec/Top.lean`) -/
theorem compile_correct {program : XPipe} {compiled : Compiled} {α β : Type} {f : α → β}
    {encodeInput : α → List UInt8} {encodeOutput : β → List UInt8} {argument : α} {startState : riscv.State}
    {call : Call}
    (compiles : compile program = some compiled)
    (computes : Computes program f encodeInput encodeOutput)
    (startsRight : StartCorrect riscv startState call compiled.code (encodeInput argument))
    (outputFits : (encodeOutput (f argument)).length ≤ call.outputLength)
    (enoughWorkSpace : compiled.space (encodeInput argument).length ≤ call.workLength) :
    ∃ finishState,
      Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      readMemory (riscv.observe finishState) call.outputAddress (encodeOutput (f argument)).length
        = some (encodeOutput (f argument)) := by
  obtain ⟨finishState, h1, h2, h3, -⟩ := compile_top compiles computes startsRight outputFits enoughWorkSpace
  exact ⟨finishState, h1, h2, h3⟩

/-- **The frame facts**, same hypotheses: memory outside the result and the work block unchanged, the
kept registers unchanged, the control state `Cfg` again, the result length in `a1` -/
theorem compile_frame {program : XPipe} {compiled : Compiled} {α β : Type} {f : α → β}
    {encodeInput : α → List UInt8} {encodeOutput : β → List UInt8} {argument : α} {startState : riscv.State}
    {call : Call}
    (compiles : compile program = some compiled)
    (computes : Computes program f encodeInput encodeOutput)
    (startsRight : StartCorrect riscv startState call compiled.code (encodeInput argument))
    (outputFits : (encodeOutput (f argument)).length ≤ call.outputLength)
    (enoughWorkSpace : compiled.space (encodeInput argument).length ≤ call.workLength) :
    ∃ finishState,
      Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (∀ address, Outside address (call.outputAddress, (encodeOutput (f argument)).length) →
        Outside address (call.workAddress, call.workLength) →
        (riscv.observe finishState).memory address = (riscv.observe startState).memory address) ∧
      (∀ number ∈ riscv.mapping.kept,
        (riscv.observe finishState).register number = (riscv.observe startState).register number) ∧
      riscv.configured finishState ∧
      (riscv.observe finishState).register riscv.mapping.outputLength
        = (encodeOutput (f argument)).length.toUInt64 := by
  obtain ⟨finishState, h1, h2, -, h4, h5, h6, h7⟩ :=
    compile_top compiles computes startsRight outputFits enoughWorkSpace
  exact ⟨finishState, h1, h2, h4, h5, h6, h7⟩

end Proven.Top
