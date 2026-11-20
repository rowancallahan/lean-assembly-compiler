/- Nano/V2Self/Proof/Main/MainTop: C's end-to-end theorem in the owner's top-level vocabulary (`Spec/Top.lean` +
`Compiler/AllocSpec.lean`), the same shape as compiler #1's `compile_correctL : CompileCorrect riscv compile`.
* `SrcC`: a source text; `Program SrcC` runs it by its MEANING: lex (Lex2Spec), parse (ParSpec), `Sem κC` (no result when
  the text is not a program or the run hits Gen's buffer capacity);
* `compileC`: C's driver `mC` (when it emits code and the text is at most 2^20 bytes); `memoryNeeded` = the work bound
  of `ImplementsC` (chosen);
* `C_correctL : BndStage → GenStage → CompileCorrect riscv compileC` (the parser stage is F's `ParInv.parserSound`,
  the ownership stage O's `OwnP.own_stage`). -/
import Nano.V2Self.Proof.Parser.MainTyP
import Nano.V2Self.Proof.Main.Main
import Nano.V2Self.Proof.Parser.ParInvRun
import Nano.V2Self.Proof.Own.OwnStage
import Riscv.Back.Top
import Compiler.AllocSpec
import Nano.V2Self.Proof.Machine.RunsDef
import Nano.V2Self.Proof.Main.Compile

open LeanRV64D
namespace NanoMain
open Proven Proven.Top Proven.Top.Alloc ParSpec

/-- **the end-to-end theorem with progress**: as `compiler_correct`, and the meaning never gets stuck, so for every input
the emitted code's run shows the program's output, the capacity trap, or (below the work bound) out-of-memory -/
theorem compiler_correct' (HP : ParStage) (HO : OwnStage) (HB : BndStage) (HG : GenStage) (x : List UInt8) (hx : x.length ≤ 2 ^ 20)
    (h : mC x ≠ []) :
    ∃ ts p, LexSpec.Lexes x ts ∧ ParsesProgram ts p ∧ LinearK p ∧ ImplementsC (mC x) (Sem κC p) ∧
      ∀ inp, Sem κC p inp ≠ .error .stuck := by
  obtain ⟨ts, p, h1, h2, hl, h3⟩ := compiler_correct HP HO HB HG x hx h
  exact ⟨ts, p, h1, h2, hl, h3, parsed_not_stuck h2 κC⟩


/-- the definite out-of-memory return: a0 = −1, a1 = 0, only the work block changed (output untouched) -/
def OomOutM (s : St) (ra : BitVec 64) (output work : Region) (s' : St) : Prop :=
  s'.regs.get? .PC = some ra ∧ abiSavedKept s s' ∧ Cfg s' ∧ s'.regs.get? .x10 = some a0Oom ∧
    s'.regs.get? .x11 = some 0 ∧ unchangedOutside s s' [work]

/-- **the work bound is exact**: same premises as `ImplementsCW`; when `f` has a result and the work block is below
`space x`, the run ends in the out-of-memory return (with `ImplementsCW`: out of memory iff below the bound) -/
def ExactCW (B : List UInt8) (f : List UInt8 → Except Stop (List UInt8)) (space : List UInt8 → Nat)
    (maxLen : Nat := 2 ^ 20) : Prop :=
  ∀ (x : List UInt8) (s : St) (entry ra : BitVec 64) (input output work : Region),
    let codeR : Region := ⟨entry.toNat, B.length⟩
    x.length ≤ maxLen → Cfg s → s.regs.get? .PC = some entry → entry.toNat % 4 = 0 → B.length % 4 = 0 →
    bytesAt s entry.toNat B.length = B.map (some ·.toBitVec) →
    s.regs.get? .x10 = some (BitVec.ofNat 64 input.base) →
    s.regs.get? .x11 = some (BitVec.ofNat 64 x.length) →
    s.regs.get? .x12 = some (BitVec.ofNat 64 work.base) →
    s.regs.get? .x13 = some (BitVec.ofNat 64 output.base) →
    s.regs.get? .x2 = some (BitVec.ofNat 64 (work.base + work.len)) →
    s.regs.get? .x1 = some ra → ra.toNat % 4 = 0 → disjoint ⟨ra.toNat, 4⟩ codeR →
    bytesAt s input.base x.length = x.map (some ·.toBitVec) →
    input.len = x.length → (∀ y, f x = .ok y → y.length ≤ output.len) → work.base % 8 = 0 →
    (∀ r ∈ [input, output, work, codeR], r.inRAM) → [input, output, work, codeR].Pairwise disjoint →
    Mapped s output → Mapped s work →
    ∀ y, f x = .ok y → work.len < space x → runsTo s (OomOutM s ra output work)

/-- codegen with C's explicit work bound -/
def GenStageM : Prop :=
  ∀ (c : List UInt8) (ts : List UInt64) (p : List DefA), ParsesProgram ts p → ts.length < 2 ^ 24 → LinearK p →
    C.g41 c (serialize p) ≠ [] → ImplementsCW (C.g41 c (serialize p)) (Sem κC p) (fun x => max 16 (Msp p x))


theorem a0Ok_ne (y : List UInt8) : UInt64.ofBitVec (a0Ok y) ≠ oomFlag := by
  unfold a0Ok oomFlag; split <;> decide

theorem kept_of {s s' : St} (hkept : abiSavedKept s s') : KeptRegisters riscv s s' := by
  intro number hnumber
  change (riscvObserve s').register number = (riscvObserve s).register number
  change number ∈ [2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27] at hnumber
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hnumber
  simp only [abiSavedKept, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hkept
  obtain ⟨k2, k3, k4, k8, k9, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27⟩ := hkept
  rcases hnumber with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [riscvObserve, riscvRegister, k2, k3, k4, k8, k9, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27]

/-- as `compiler_correct`, with the explicit work bound -/
theorem compiler_correctM (HB : BndStage) (HG : GenStageM) (x : List UInt8) (hx : x.length ≤ 2 ^ 20) (h : mC x ≠ []) :
    ∃ ts p, LexSpec.Lexes x ts ∧ ParsesProgram ts p ∧ LinearK p ∧
      ImplementsCW (mC x) (Sem κC p) (fun inp => max 16 (Msp p inp)) :=
  compiler_correctG HB (fun B p => ImplementsCW B (Sem κC p) (fun inp => max 16 (Msp p inp))) HG x hx h

/-- **C is correct** (owner's top-level statement), from the size-bound and codegen stage theorems -/
theorem C_correctL (HB : BndStage) (HG : GenStageM) : CompileCorrect riscv compileC := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight outputFits
    enough
  obtain ⟨x⟩ := program
  unfold compileC at compiles
  split at compiles
  · rename_i hc
    have hcomp := Option.some.inj compiles
    subst hcomp
    obtain ⟨hne, hx⟩ := hc
    obtain ⟨ts, p, hL, hP, -, hI⟩ := compiler_correctM HB HG x hx hne
    have hpo := pOf_eq hL hP
    have hW : ImplementsCW (mC x) (Sem κC p) (spaceC x) := by unfold spaceC; rw [hpo]; exact hI
    have hrun : Sem κC p (encodeInput argument) = .ok (encodeOutput (f argument)) := by
      have := computes argument
      change srcRun ⟨x⟩ (encodeInput argument) = _ at this
      simp only [srcRun, hpo, Option.bind_some] at this
      exact toOption_some this
    have hmem : spaceC x (encodeInput argument) ≤ call.workLength := by
      simpa [memoryNeeded, peak, inUse] using enough
    -- the start state, as in `implements1_top`
    obtain ⟨configured, codeLoaded, inputLoaded, inputLength, inputSmall, returnRegister, inputRegister,
      lengthRegister, workRegister, workTopRegister, outputRegister, codeAligned, returnAligned, workAligned,
      returnOutsideCode, inRam, disjoint, outputPresent, workPresent⟩ := startsRight
    change Cfg startState at configured
    have eObserve : riscv.observe = riscvObserve := rfl
    have eMapping : riscv.mapping = riscvMapping := rfl
    have eStart : riscv.ramStart = 0x80000000 := rfl
    have eEnd : riscv.ramEnd = 0x100000000 := rfl
    simp only [eObserve, eMapping, eStart, eEnd, riscvMapping, Call.blocks] at *
    generalize hpc : (riscvObserve startState).programCounter = pc at *
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at inRam
    obtain ⟨⟨ri1, ri2⟩, ⟨ro1, ro2⟩, ⟨rw1, rw2⟩, ⟨rc1, rc2⟩⟩ := inRam
    have hreg := fun (register : Register) hregister => isSome_of_cfg configured (register := register) hregister
    have hpcReg := register_of (hreg .PC (by simp)) hpc
    have hentry : (BitVec.ofNat 64 pc.toNat).toNat = pc.toNat := by simp
    have hra : (BitVec.ofNat 64 call.returnAddress.toNat).toNat = call.returnAddress.toNat := by simp
    have hcode := (readMemory_riscv startState (address := pc) (length := (mC x).length) _ (by omega)).1 codeLoaded
    have hinput := (readMemory_riscv startState (address := call.inputAddress) _ (by omega)).1 inputLoaded
    have run := hW (encodeInput argument) startState (BitVec.ofNat 64 pc.toNat) (BitVec.ofNat 64 call.returnAddress.toNat)
      ⟨call.inputAddress.toNat, call.inputLength⟩ ⟨call.outputAddress.toNat, call.outputLength⟩
      ⟨call.workAddress.toNat, call.workLength⟩ inputSmall configured hpcReg (by rw [hentry]; exact codeAligned)
      (mC_len x) (by rw [hentry]; exact hcode)
      (register_of (hreg .x10 (by simp)) inputRegister)
      (by have := register_of (hreg .x11 (by simp)) lengthRegister
          rw [this, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)])
      (register_of (hreg .x12 (by simp)) workRegister)
      (register_of (hreg .x13 (by simp)) outputRegister)
      (by have := register_of (hreg .x2 (by simp)) workTopRegister
          rw [this, toNat_add_offset (bound := call.workLength + 1) (by omega) (by omega)])
      (register_of (hreg .x1 (by simp)) returnRegister) (by rw [hra]; exact returnAligned)
      (by rw [hra, hentry]; exact returnOutsideCode) hinput inputLength
      (by intro y hy; rw [hrun] at hy; cases hy; exact outputFits) workAligned
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
    obtain ⟨steps, finishState, hsteps, hpcFinish, hkept, hcfg, hout⟩ := run
    rw [hrun] at hout
    rcases hout with ⟨h10, h11, hbytes, hunchanged⟩ | ⟨hoom, -⟩
    rotate_left
    · simp only at hoom; omega
    refine ⟨finishState, runs_of_steps steps _ _ hsteps, ?_, ?_, ?_, ?_, ?_, ?_, hcfg⟩
    · simp [riscvObserve, hpcFinish]
    · simp only [riscvObserve, riscvRegister, h10, Option.map_some, Option.getD_some]; exact a0Ok_ne _
    · exact (readMemory_riscv finishState (address := call.outputAddress) _ (by omega)).2 hbytes
    · simp only [riscvObserve, riscvRegister, h11, Option.map_some, Option.getD_some]; rfl
    · intro address hout hwork
      simp only [riscvObserve]
      rw [hunchanged address.toNat (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hout, hwork⟩)]
    · exact kept_of hkept
  · cases compiles

end NanoMain
