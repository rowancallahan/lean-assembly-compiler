/- **The IR compiler on RISC-V**: `Ir.compile : Ir.Prog VReg → Option CompiledA` (trivial allocation, list-order
linearisation, long branches, placement, `alloc` with the out-of-memory exit; `Compiler/Ir/Lin.lean`) with the
owner's statements `CompileRuns riscv compile` and `CompileCorrect riscv compile` (`Compiler/AllocSpec.lean`).

The meaning of a program is its IR run (`Prog.meaning`, `Compiler/Ir/Sem.lean`): the output bytes of the run of
`main` from the input.  The events of `compile` are the events of that run plus the frame of `main`
(`alloc (slots + 1)`), so `memoryNeeded` is 8 bytes times the most cells in use. -/
import Riscv.Back.IrTarget
import Riscv.Back.Top
import Compiler.Ir.EmitTop
import Compiler.Ir.Lin
import Compiler.Ir.Rename
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven.Ir
open Proven Proven.Mach Proven.Mach.Riscv Proven.Top Proven.Top.Alloc

/-- the events of the Lin run from the input (none if it does not terminate), then the stub's and `main`'s frame -/
noncomputable def events (Q : Prog Nat) (input : List UInt8) : List MemEvent :=
  ((Q.result input).map (·.ev)).getD [] ++ [Ctx.base Q]

/-- the words of a program: allocation (validated), then the Lin code of the program -/
def compileW (P : Prog VReg) : Option (List (BitVec 32) × Prog Nat) :=
  match alloc P with
  | some Q => (rvT.lin Q).map fun c => (rvT.words c, Q)
  | none => none

/-- **the IR compiler** -/
noncomputable def compile (P : Prog VReg) : Option CompiledA :=
  match compileW P with
  | some (ws, Q) => some ⟨wordBytes ws, 8, events Q⟩
  | none => none

theorem compile_inv {P : Prog VReg} {c : CompiledA} (h : compile P = some c) :
    ∃ Q code L, alloc P = some Q ∧ rvT.emitP Q L = some code ∧ c = ⟨wordBytes (rvT.words code), 8, events Q⟩ := by
  unfold compile compileW at h
  split at h
  · next ws Q' hw =>
    cases h
    split at hw
    · next Q ha =>
      unfold Target.lin at hw
      cases he : rvT.emitP Q (rvT.layout Q (Target.rounds Q) ⟨[], [], 0⟩) with
      | none => rw [he] at hw; exact nomatch hw
      | some code => rw [he] at hw; cases hw; exact ⟨_, code, _, ha, he, rfl⟩
    · exact nomatch hw
  · exact nomatch h

theorem mapM_id_bytes : ∀ {l : List (Option UInt8)} {o : List UInt8}, l.mapM id = some o →
    o.length = l.length ∧ ∀ i (hi : i < o.length), l[i]? = some (some o[i])
  | [], o, h => by simp at h; subst h; simp
  | x :: xs, o, h => by
    rw [List.mapM_cons] at h
    cases x with
    | none => simp at h
    | some b =>
      cases hx : xs.mapM id with
      | none => simp [hx] at h
      | some os =>
        simp [hx] at h; subst h
        obtain ⟨hl, hg⟩ := mapM_id_bytes hx
        refine ⟨by simp [hl], fun i hi => ?_⟩
        cases i with
        | zero => rfl
        | succ i => simpa using hg i (by simp at hi; omega)

theorem output_bytes {m : Mem} {o : List UInt8} (h : m.output = some o) :
    o.length = m.out.length ∧ ∀ i (hi : i < o.length), m.out[i]? = some (some o[i]) :=
  mapM_id_bytes h

/-- **the machine run** of compiled code from `StartCorrect`, for a program that computes `f` -/
theorem machine_run {P : Prog VReg} {compiled : CompiledA} {α β : Type} {f : α → β} {encodeInput : α → List UInt8}
    {encodeOutput : β → List UInt8} {argument : α} {startState : riscv.State} {call : Call}
    (compiles : compile P = some compiled)
    (computes : (encodeInput argument).length ≤ 2 ^ 20 →
      P.meaning (encodeInput argument) = some (encodeOutput (f argument)))
    (startsRight : StartCorrect riscv startState call compiled.code (encodeInput argument))
    (outputFits : (encodeOutput (f argument)).length ≤ call.outputLength) :
    ∃ finishState, Proven.Top.Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (∀ address, Outside address (call.outputAddress, call.outputLength) →
        Outside address (call.workAddress, call.workLength) →
        (riscv.observe finishState).memory address = (riscv.observe startState).memory address) ∧
      ((memoryNeeded compiled (encodeInput argument) ≤ call.workLength ∧
          (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
          readMemory (riscv.observe finishState) call.outputAddress (encodeOutput (f argument)).length =
            some (encodeOutput (f argument))) ∨
        (call.workLength < memoryNeeded compiled (encodeInput argument) ∧
          (riscv.observe finishState).register riscv.mapping.status = oomFlag)) := by
  obtain ⟨Q, code, L, ha, he, rfl⟩ := compile_inv compiles
  -- the run of the program
  have hmean := computes startsRight.inputSmall
  change (P.result (encodeInput argument)).bind (fun r => r.mem.output) = _ at hmean
  cases hres : P.result (encodeInput argument) with
  | none => rw [hres] at hmean; exact nomatch hmean
  | some r0 =>
  rw [hres] at hmean; simp only [Option.bind_some] at hmean
  obtain ⟨r, hrun, -, hmem⟩ := alloc_runs ha (Prog.result_some hres)
  rw [← hmem] at hmean
  obtain ⟨hol, hob⟩ := output_bytes hmean
  have hmn : memoryNeeded ⟨wordBytes (rvT.words code), 8, events Q⟩ (encodeInput argument) =
      8 * peak (r.ev ++ [Ctx.base Q]) := by
    show 8 * peak (events Q (encodeInput argument)) = _
    simp [events, Prog.result_eq hrun]
  rw [hmn]
  -- the start state
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
  have hcode := (readMemory_riscv startState (address := pc) (length := (wordBytes (rvT.words code)).length) _
    (by rw [wordBytes_length]; omega)).1 (by rw [wordBytes_length]; exact codeLoaded)
  rw [wordBytes_length, wordBytes_codeBytes] at hcode
  have hinput := (readMemory_riscv startState (address := call.inputAddress) _ (by omega)).1 inputLoaded
  have h11 : startState.regs.get? .x11 = some (BitVec.ofNat 64 (encodeInput argument).length) := by
    have := register_of (hreg .x11 (by simp)) lengthRegister
    rw [this, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have h2 := register_of (hreg .x2 (by simp)) workTopRegister
  have h10 := register_of (hreg .x10 (by simp)) inputRegister
  have h12 := register_of (hreg .x12 (by simp)) workRegister
  have h13 := register_of (hreg .x13 (by simp)) outputRegister
  have h1 := register_of (hreg .x1 (by simp)) returnRegister
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true, Apart] at disjoint
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := disjoint
  have hent : (BitVec.ofNat 64 pc.toNat).toNat = pc.toNat := by simp
  have hcodeOK : rvT.codeOK (BitVec.ofNat 64 pc.toNat) (rvT.words code).length :=
    ⟨by rw [hent]; exact codeAligned, by rw [hent]; exact rc1, by rw [hent]; show _ ≤ 0x100000000; omega⟩
  have hsp : (getX startState 2).toNat = call.workAddress.toNat + call.workLength := by
    rw [getX_of (configured.x2.symm.trans h2) rfl, toNat_add_offset (bound := call.workLength + 1) (by omega)
      (by omega)]
    simp; omega
  -- the context
  let C : Ctx rvT := {
    W := rvT.words code
    pc0 := BitVec.ofNat 64 pc.toNat
    s0 := startState
    input := encodeInput argument
    inA := call.inputAddress.toNat
    outA := call.outputAddress.toNat
    outL := call.outputLength
    wb := call.workAddress.toNat
    wl := call.workLength
    nS := 0
    F0 := 0
    sv := 0
    hm := fun _ => none
    code0 := codeAt_of_codeBytes hcodeOK (by rw [hent]; exact hcode)
    codeOK := hcodeOK
    lo := by decide
    inR := ⟨ri1, by rw [← inputLength]; exact ri2⟩
    outR := ⟨ro1, ro2⟩
    wR := ⟨rw1, rw2⟩
    wal := workAligned
    dCO := by unfold Mach.disjoint; dsimp only; rw [hent]; omega
    dCW := by unfold Mach.disjoint; dsimp only; rw [hent]; omega
    dIO := by unfold Mach.disjoint; dsimp only; rw [← inputLength]; omega
    dIW := by unfold Mach.disjoint; dsimp only; rw [← inputLength]; omega
    dOW := by unfold Mach.disjoint; dsimp only; omega
    inb := fun i hi => by
      have h' : bytesAt startState call.inputAddress.toNat (encodeInput argument).length =
          ((encodeInput argument).map (·.toBitVec)).map some := by rw [hinput, List.map_map]; rfl
      have := mem_of_bytesAt h' (i := i) (by simpa using hi)
      simpa using this
    wr := fun s a h => by show 0x80000000 ≤ a ∧ a + 1 ≤ 0x100000000; omega
    retOK := by
      show (getX startState 1).toNat % 2 = 0
      rw [getX_of (configured.x1.symm.trans h1) rfl]; simp; omega
    htop := by
      show (getX startState 2).toNat / 8 * 8 = call.workAddress.toNat + call.workLength / 8 * 8
      rw [hsp]; have := workAligned; omega }
  have hW : C.W = rvT.words code := rfl
  have hout : r.mem.out.length ≤ C.outL := by
    show r.mem.out.length ≤ call.outputLength; omega
  have := C.emit_ok he hW configured hpcReg
    (by show getX startState 10 = _; rw [getX_of (configured.x10.symm.trans h10) rfl])
    (by show getX startState 11 = _; rw [getX_of (configured.x11.symm.trans h11) rfl])
    (by show getX startState 12 = _; rw [getX_of (configured.x12.symm.trans h12) rfl])
    (by show getX startState 13 = _; rw [getX_of (configured.x13.symm.trans h13) rfl])
    (by show 16 ≤ (getX startState 2).toNat / 8 * 8; rw [hsp]; omega)
    hrun hout
  obtain ⟨steps, finishState, hsteps, hok, hpcF, hU, hcase⟩ := this
  refine ⟨finishState, runs_of_steps steps _ _ hsteps, ?_, ?_, ?_⟩
  · have : finishState.regs.get? .PC = some (BitVec.ofNat 64 call.returnAddress.toNat) := by
      rw [← getX_of (configured.x1.symm.trans h1) rfl]; exact hpcF
    simp [riscvObserve, this]
  · intro address hO hWk
    simp only [riscvObserve]
    unfold Outside at hO hWk
    have := hU address.toNat (by omega) (by omega)
    change finishState.mem[address.toNat]? = startState.mem[address.toNat]? at this
    rw [this]
  · have hx10 : ∀ v, getX finishState 10 = v → (riscvObserve finishState).register 10 = UInt64.ofBitVec v := by
      intro v hv; simp only [riscvObserve, riscvRegister, hok.x10, hv, Option.map_some, Option.getD_some]
    rcases hcase with ⟨pk, a0, bo⟩ | ⟨pk, a0⟩
    · change peak (r.ev ++ [Ctx.base Q]) ≤ call.workLength / 8 at pk
      refine .inl ⟨by omega, ?_, ?_⟩
      · rw [hx10 _ a0]
        intro e
        have := congrArg UInt64.toNat e
        rw [UInt64.toNat_ofBitVec, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt64.toNat_lt _)] at this
        have h2 : oomFlag.toNat = 2 ^ 64 - 1 := rfl
        omega
      · refine (readMemory_riscv finishState _ (by omega)).2 ?_
        apply List.ext_getElem (by simp [bytesAt])
        intro i h1 h2
        simp only [bytesAt, List.getElem_map, List.getElem_range]
        have hi : i < (encodeOutput (f argument)).length := by simpa [bytesAt] using h1
        exact bo i _ (hob i hi)
    · change call.workLength / 8 < peak (r.ev ++ [Ctx.base Q]) at pk
      exact .inr ⟨by omega, by rw [hx10 _ a0]; rfl⟩

/-- **What happens** (`CompileRuns`): the code returns to the caller, changes nothing outside the output and work
blocks, and the status register holds `oomFlag` exactly when the run's memory exceeds the work block. -/
theorem ir_compile_runs : CompileRuns riscv compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits
  obtain ⟨finishState, hruns, hpc, hframe, hcase⟩ := machine_run compiles (fun _ => computes argument) startsRight outputFits
  refine ⟨finishState, hruns, hpc, hframe, ?_⟩
  unfold OutOfMemory
  rcases hcase with ⟨hle, hne, -⟩ | ⟨hlt, heq⟩
  · exact ⟨fun h => absurd h hne, fun h => absurd h (Nat.not_lt.2 hle)⟩
  · exact ⟨fun _ => hlt, fun _ => heq⟩

/-- **What comes out** (`CompileCorrect`): with `memoryNeeded ≤ workLength` the code returns with the right output
and no flag. -/
theorem ir_compile_correct : CompileCorrect riscv compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits enoughMemory
  obtain ⟨finishState, hruns, hpc, hframe, hcase⟩ := machine_run compiles (fun _ => computes argument) startsRight outputFits
  rcases hcase with ⟨-, hne, hread⟩ | ⟨hlt, -⟩
  · exact ⟨finishState, hruns, hpc, hne, hread⟩
  · exact absurd enoughMemory (Nat.not_le.2 hlt)

end Proven.Ir
