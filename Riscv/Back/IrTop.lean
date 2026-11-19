/- **The IR compiler on RISC-V**: `Ir.compile : Ir.Prog VReg → Option CompiledA` (trivial allocation, list-order
linearisation, long branches, placement, `alloc` with the out-of-memory exit; `Compiler/Ir/Lin.lean`) with the
owner's statements `CompileRunsWeak riscv compile` and `CompileCorrectWeak riscv compile` (`Compiler/AllocSpec.lean`).

The meaning of a program is its IR run (`Prog.meaning`, `Compiler/Ir/Sem.lean`): the output bytes of the run of
`main` from the input.  The events of `compile` are the events of that run plus the frame of `main`
(`alloc (slots + 1)`), so `memoryNeeded` is 8 bytes times the most cells in use. -/
import Riscv.Back.IrTarget
import Riscv.Back.Top
import Riscv.Back.LinkL
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

/-- `keepC` from the start state and the frame register restored: the callee-saved registers -/
theorem kept_of {s s' : St} (h : Cfg s) (h' : Cfg s') (hk : rvT.keepC s s') (hfr : rvT.fr s' = rvT.fr s) :
    KeptRegisters riscv s s' := by
  have hk' : ∀ j : Fin 32, (∀ r : Reg, j ≠ phys r) → j ≠ 3 → j ≠ 1 → getX s' j = getX s j := hk
  have h3 : getX s' 3 = getX s 3 := hfr
  have e : ∀ j : Fin 32, j ≠ 0 → getX s' j = getX s j →
      (riscvObserve s').register j.val = (riscvObserve s).register j.val := fun j hj hj' => by
    rw [obs_reg h' j hj, obs_reg h j hj, hj']
  intro r hr
  change r ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e 2 (by decide) (hk' 2 (by decide) (by decide) (by decide))
  · exact e 3 (by decide) h3
  · exact e 4 (by decide) (hk' 4 (by decide) (by decide) (by decide))
  · exact e 8 (by decide) (hk' 8 (by decide) (by decide) (by decide))
  · exact e 9 (by decide) (hk' 9 (by decide) (by decide) (by decide))
  · exact e 18 (by decide) (hk' 18 (by decide) (by decide) (by decide))
  · exact e 19 (by decide) (hk' 19 (by decide) (by decide) (by decide))
  · exact e 20 (by decide) (hk' 20 (by decide) (by decide) (by decide))
  · exact e 21 (by decide) (hk' 21 (by decide) (by decide) (by decide))
  · exact e 22 (by decide) (hk' 22 (by decide) (by decide) (by decide))
  · exact e 23 (by decide) (hk' 23 (by decide) (by decide) (by decide))
  · exact e 24 (by decide) (hk' 24 (by decide) (by decide) (by decide))
  · exact e 25 (by decide) (hk' 25 (by decide) (by decide) (by decide))
  · exact e 26 (by decide) (hk' 26 (by decide) (by decide) (by decide))
  · exact e 27 (by decide) (hk' 27 (by decide) (by decide) (by decide))

/-- **the machine run** of compiled code from `StartCorrect`, for a program that computes `f`, with the strengthened
facts: memory changes only in the result prefix of the output block and the work block, `Cfg` at the end; on a
normal return the callee-saved registers are kept and, when `main` returns the output length, `a1` holds it -/
theorem machine_runL {P : Prog VReg} {compiled : CompiledA} {α β : Type} {f : α → β} {encodeInput : α → List UInt8}
    {encodeOutput : β → List UInt8} {argument : α} {startState : riscv.State} {call : Call}
    (compiles : compile P = some compiled)
    (computes : (encodeInput argument).length ≤ 2 ^ 20 →
      P.meaning (encodeInput argument) = some (encodeOutput (f argument)))
    (startsRight : StartCorrect riscv startState call compiled.code (encodeInput argument))
    (outputFits : (encodeOutput (f argument)).length ≤ call.outputLength) :
    ∃ finishState, Proven.Top.Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (∀ address, Outside address (call.outputAddress, (encodeOutput (f argument)).length) →
        Outside address (call.workAddress, call.workLength) →
        (riscv.observe finishState).memory address = (riscv.observe startState).memory address) ∧
      (∀ a : Nat, (a < call.outputAddress.toNat ∨ call.outputAddress.toNat + (encodeOutput (f argument)).length ≤ a) →
        (a < call.workAddress.toNat ∨ call.workAddress.toNat + call.workLength ≤ a) →
        finishState.mem[a]? = startState.mem[a]?) ∧
      riscv.configured finishState ∧
      ((memoryNeeded compiled (encodeInput argument) ≤ call.workLength ∧
          (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
          readMemory (riscv.observe finishState) call.outputAddress (encodeOutput (f argument)).length =
            some (encodeOutput (f argument)) ∧
          KeptRegisters riscv startState finishState ∧
          ((∀ r, P.result (encodeInput argument) = some r →
              r.vs = [.w (BitVec.ofNat 64 (encodeOutput (f argument)).length)]) →
            (riscv.observe finishState).register riscv.mapping.outputLength =
              (encodeOutput (f argument)).length.toUInt64)) ∨
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
  obtain ⟨r, hrun, hvsr, hmem⟩ := alloc_runs ha (Prog.result_some hres)
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
    outL := (encodeOutput (f argument)).length
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
    outR := ⟨ro1, Nat.le_trans (Nat.add_le_add_left outputFits _) ro2⟩
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
    show r.mem.out.length ≤ (encodeOutput (f argument)).length; omega
  have := C.emit_ok he hW configured hpcReg
    (by show getX startState 10 = _; rw [getX_of (configured.x10.symm.trans h10) rfl])
    (by show getX startState 11 = _; rw [getX_of (configured.x11.symm.trans h11) rfl])
    (by show getX startState 12 = _; rw [getX_of (configured.x12.symm.trans h12) rfl])
    (by show getX startState 13 = _; rw [getX_of (configured.x13.symm.trans h13) rfl])
    (by show 16 ≤ (getX startState 2).toNat / 8 * 8; rw [hsp]; omega)
    hrun hout
  obtain ⟨steps, finishState, hsteps, hok, hpcF, hU, hcase⟩ := this
  refine ⟨finishState, runs_of_steps steps _ _ hsteps, ?_, ?_, fun a h1 h2 => hU a h1 h2, hok, ?_⟩
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
    rcases hcase with ⟨pk, a0, bo, hkc, hfr, hlen⟩ | ⟨pk, a0⟩
    · change peak (r.ev ++ [Ctx.base Q]) ≤ call.workLength / 8 at pk
      refine .inl ⟨by omega, ?_, ?_, kept_of configured hok hkc hfr, fun hvs => ?_⟩
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
      · have hv := hlen _ (by rw [hvsr, hvs r0 rfl]; rfl)
        have : (riscv.observe finishState).register 11 = UInt64.ofBitVec (getX finishState 11) :=
          obs_reg hok 11 (by decide)
        change (riscv.observe finishState).register 11 = _
        rw [this]
        have hv' : getX finishState 11 = BitVec.ofNat 64 (encodeOutput (f argument)).length := hv
        rw [hv']; rfl
    · change call.workLength / 8 < peak (r.ev ++ [Ctx.base Q]) at pk
      exact .inr ⟨by omega, by rw [hx10 _ a0]; rfl⟩

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
  obtain ⟨finishState, hruns, hpc, hframe, -, -, hcase⟩ := machine_runL compiles computes startsRight outputFits
  refine ⟨finishState, hruns, hpc, fun a h1 h2 => hframe a (outside_prefix outputFits h1) h2, ?_⟩
  rcases hcase with ⟨h1, h2, h3, -⟩ | h
  · exact .inl ⟨h1, h2, h3⟩
  · exact .inr h

/-- **What happens** (`CompileRunsWeak`): the code returns to the caller, changes nothing outside the output and work
blocks, and the status register holds `oomFlag` exactly when the run's memory exceeds the work block. -/
theorem ir_compile_runs : CompileRunsWeak riscv compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits
  obtain ⟨finishState, hruns, hpc, hframe, hcase⟩ := machine_run compiles (fun _ => computes argument) startsRight outputFits
  refine ⟨finishState, hruns, hpc, hframe, ?_⟩
  unfold OutOfMemory
  rcases hcase with ⟨hle, hne, -⟩ | ⟨hlt, heq⟩
  · exact ⟨fun h => absurd h hne, fun h => absurd h (Nat.not_lt.2 hle)⟩
  · exact ⟨fun _ => hlt, fun _ => heq⟩

/-- **What comes out** (`CompileCorrectWeak`): with `memoryNeeded ≤ workLength` the code returns with the right output
and no flag. -/
theorem ir_compile_correct : CompileCorrectWeak riscv compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits enoughMemory
  obtain ⟨finishState, hruns, hpc, hframe, hcase⟩ := machine_run compiles (fun _ => computes argument) startsRight outputFits
  rcases hcase with ⟨-, hne, hread⟩ | ⟨hlt, -⟩
  · exact ⟨finishState, hruns, hpc, hne, hread⟩
  · exact absurd enoughMemory (Nat.not_le.2 hlt)

/-! ## The strengthened statements (`CompileCorrect`) -/

/-- an IR program whose `main` returns the output length: its meaning counts only when `main` returns `[w n]` with
`n` the length of the output -/
structure ProgL where
  prog : Prog VReg

/-- the meaning of a `ProgL`: the output, when `main` returned its length -/
noncomputable def ProgL.meaning (P : ProgL) (input : List UInt8) : Option (List UInt8) :=
  (P.prog.result input).bind fun r => r.mem.output.bind fun o =>
    if r.vs = [.w (BitVec.ofNat 64 o.length)] then some o else none

noncomputable instance : Proven.Top.Program ProgL := ⟨ProgL.meaning⟩

/-- the IR compiler on `ProgL` (the same code) -/
noncomputable def compileL (P : ProgL) : Option CompiledA := compile P.prog

theorem meaningL_inv {P : ProgL} {input o : List UInt8} (h : P.meaning input = some o) :
    P.prog.meaning input = some o ∧
      ∀ r, P.prog.result input = some r → r.vs = [.w (BitVec.ofNat 64 o.length)] := by
  unfold ProgL.meaning at h
  cases hr : P.prog.result input with
  | none => rw [hr] at h; exact nomatch h
  | some r =>
    rw [hr] at h; simp only [Option.bind_some] at h
    cases ho : r.mem.output with
    | none => rw [ho] at h; exact nomatch h
    | some o' =>
      rw [ho] at h; simp only [Option.bind_some] at h
      split at h
      · next hv =>
        cases h
        refine ⟨?_, fun r' hr' => ?_⟩
        · show (P.prog.result input).bind (fun r => r.mem.output) = _
          rw [hr]; exact ho
        · cases hr'; exact hv
      · exact nomatch h

/-- **What comes out, strengthened** (`CompileCorrect`): with enough memory the code returns with the right output,
its length in `a1`, the callee-saved registers kept, `Cfg`, and nothing changed outside the result and the work
block -/
theorem ir_compile_correctL : CompileCorrect riscv compileL := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits enoughMemory
  have hc := computes argument
  obtain ⟨hm, hvs⟩ := meaningL_inv hc
  obtain ⟨finishState, hruns, hpc, hframe, -, hcfg, hcase⟩ :=
    machine_runL (P := program.prog) compiles (fun _ => hm) startsRight outputFits
  rcases hcase with ⟨-, hne, hread, hkept, hlen⟩ | ⟨hlt, -⟩
  · exact ⟨finishState, hruns, hpc, hne, hread, hlen hvs, hframe, hkept, hcfg⟩
  · exact absurd enoughMemory (Nat.not_le.2 hlt)

/-- **What comes out, strengthened, with the full memory frame** (`CompileCorrectRV`, the adapter's hypothesis) -/
theorem ir_compile_correctRV : CompileCorrectRV compileL := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits enoughMemory
  obtain ⟨hm, hvs⟩ := meaningL_inv (computes argument)
  obtain ⟨finishState, hruns, hpc, -, hnat, hcfg, hcase⟩ :=
    machine_runL (P := program.prog) compiles (fun _ => hm) startsRight outputFits
  rcases hcase with ⟨-, hne, hread, hkept, hlen⟩ | ⟨hlt, -⟩
  · exact ⟨finishState, hruns, hpc, hne, hread, hlen hvs, hnat, hkept, hcfg⟩
  · exact absurd enoughMemory (Nat.not_le.2 hlt)

end Proven.Ir
