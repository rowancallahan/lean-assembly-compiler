/- Nano/V2Self/Proof/MainTop: C's end-to-end theorem in the owner's top-level vocabulary (`Spec/Top.lean` +
`Compiler/AllocSpec.lean`), the same shape as compiler #1's `compile_correctL : CompileCorrectL riscv compile`.
* `Src`: a source text; `Program Src` runs it by its MEANING: lex (Lex2Spec), parse (ParSpec), `Sem κC` (no result when
  the text is not a program or the run hits Gen's buffer capacity);
* `compileC`: C's driver `mC` (when it emits code and the text is at most 2^20 bytes); `memoryNeeded` = the work bound
  of `ImplementsC` (chosen);
* `C_correctL : OwnStage → GenStage → CompileCorrectL riscv compileC` (the parser stage is F's `ParInv.parserSound`). -/
import Nano.V2Self.Proof.MainTyP
import Nano.V2Self.Proof.ParInvRun
import Riscv.Back.Top
import Compiler.AllocSpec

open LeanRV64D
namespace NanoMain
open Proven Proven.Top Proven.Top.Alloc ParSpec

theorem lexes_det : ∀ {x : List UInt8} {t t' : List UInt64}, LexSpec.Lexes x t → LexSpec.Lexes x t' → t = t'
  | _, _, _, .nil, h => by
    cases h with
    | nil => rfl
    | cons hs _ => simp [LexSpec.step] at hs
  | _, _, _, .cons hs h1, h => by
    cases h with
    | nil => simp [LexSpec.step] at hs
    | cons hs' h2 =>
      rw [hs] at hs'; simp only [Option.some.injEq, Prod.mk.injEq] at hs'; obtain ⟨rfl, rfl⟩ := hs'
      rw [lexes_det h1 h2]

/-- a source text -/
structure Src where
  text : List UInt8

open Classical in
/-- the program a text denotes (Lex2Spec, then ParSpec) -/
noncomputable def pOf (x : List UInt8) : Option (List DefA) :=
  if h : ∃ p, ∃ ts, LexSpec.Lexes x ts ∧ ParsesProgram ts p then some (Classical.choose h) else none

theorem pOf_eq {x : List UInt8} {ts : List UInt64} {p : List DefA} (hl : LexSpec.Lexes x ts) (hp : ParsesProgram ts p) :
    pOf x = some p := by
  have h : ∃ p, ∃ ts, LexSpec.Lexes x ts ∧ ParsesProgram ts p := ⟨p, ts, hl, hp⟩
  unfold pOf; rw [dif_pos h]
  obtain ⟨ts', hl', hp'⟩ := Classical.choose_spec h
  rw [lexes_det hl hl'] at hp
  unfold ParsesProgram at hp hp'; rw [hp'] at hp; cases hp; rfl

/-- **the meaning of a text** on an input -/
noncomputable def srcRun (s : Src) (inp : List UInt8) : Option (List UInt8) :=
  (pOf s.text).bind fun p => (Sem κC p inp).toOption

noncomputable instance : Program Src := ⟨srcRun⟩

open Classical in
/-- the work bound of C's code for a text (from `ImplementsC`) -/
noncomputable def spaceC (x : List UInt8) : List UInt8 → Nat :=
  match pOf x with
  | some p => if h : ImplementsC (mC x) (Sem κC p) then Classical.choose h else fun _ => 0
  | none => fun _ => 0

/-- **C as a compiler** -/
noncomputable def compileC (s : Src) : Option CompiledA :=
  if mC s.text ≠ [] ∧ s.text.length ≤ 2 ^ 20 then some ⟨mC s.text, 1, fun inp => [.alloc (spaceC s.text inp)]⟩
  else none

theorem g40_len : ∀ (n : Nat) (c : List UInt8) (w : Buf) (i : UInt64) (o : List UInt8), o.length % 4 = 0 →
    (C.g40 n c w i o).length % 4 = 0
  | 0, _, _, _, _, h => by simpa [C.g40] using h
  | n + 1, c, w, i, o, h => by
    simp only [C.g40]
    split
    · exact g40_len n c w _ _ (by simp [put]; omega)
    · exact h

theorem mC_len (x : List UInt8) : (mC x).length % 4 = 0 := by
  unfold mC C.g41 C.g42
  generalize C.o41 (C.y16 (C.s10 x)) = a
  split
  · rfl
  split
  · generalize C.g53 a = q
    obtain ⟨x2, w⟩ := q
    simp only
    split
    · rfl
    · generalize C.g39 _ _ _ _ _ _ _ = q2
      obtain ⟨r1, o⟩ := q2
      simp only
      split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · exact g40_len _ _ _ _ _ rfl
  · rfl

theorem toOption_some {r : Except Stop (List UInt8)} {y : List UInt8} (h : r.toOption = some y) : r = .ok y := by
  cases r <;> simp [Except.toOption] at h; rw [h]

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

/-- the parser stage, discharged (F) -/
theorem parStage : ParStage := fun _ hW hts => ParInv.parserSound hW hts

/-- **C is correct** (owner's top-level statement), from the ownership and codegen stage theorems -/
theorem C_correctL (HO : OwnStage) (HG : GenStage) : CompileCorrectL riscv compileC := by
  have HP := parStage
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight outputFits
    enough
  obtain ⟨x⟩ := program
  unfold compileC at compiles
  split at compiles
  · rename_i hc
    have hcomp := Option.some.inj compiles
    subst hcomp
    obtain ⟨hne, hx⟩ := hc
    obtain ⟨ts, p, hL, hP, -, hI, -⟩ := compiler_correct' HP HO HG x hx hne
    have hpo := pOf_eq hL hP
    have hW : ImplementsCW (mC x) (Sem κC p) (spaceC x) := by
      unfold spaceC; rw [hpo]; simp only; rw [dif_pos hI]; exact Classical.choose_spec hI
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
