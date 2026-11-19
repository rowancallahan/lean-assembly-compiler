/- Opus box E: **`CompileRuns` for C** (the owner's stronger statement): with ANY work block, the code returns to the
caller, changes memory only in the work block and the result prefix of the output block, keeps the callee-saved
registers, and reports out-of-memory (a0 = −1) EXACTLY when the work block is smaller than `memoryNeeded` (C's
explicit exact bound `spaceC = max 16 ∘ Msp`).  Premise: `ShiftInv` (D), the position-independence of running out
of room. -/
import Nano.V2Self.Proof.Machine.RunsThr
open LeanRV64D
namespace NanoMain
open Proven Proven.Top Proven.Top.Alloc ParSpec Templates

/-- below the exact bound, Gen's code ends in the out-of-memory return (given `ShiftInv`) -/
theorem gen_exact (HS : ShiftInv) (c : List UInt8) (ts : List UInt64) (p : List DefA) (hp : ParsesProgram ts p)
    (hts : ts.length < 2 ^ 24) (hL : LinearK p) (h : C.g41 c (serialize p) ≠ []) :
    ExactCW (C.g41 c (serialize p)) (Sem κC p) (fun x => max 16 (Msp p x)) := by
  intro x s entry ra input output work codeR hxl hc hpc he4 _ hB h10 h11 h12 h13 h2 h1 hra4 _ hin hil hout hw8 hram
    hdis hMo hMw y _ hlt
  obtain ⟨Ks, hO, hK2⟩ := hL
  have h16 := Msp_ge p x
  exact gen_runs_oom HS c hp hts Ks hO hK2 (ParSerLen.ser_lt hp hts) h
    (dbStage capStage c ts p hp hts ⟨Ks, hO, hK2⟩ h) x s entry ra input output work hxl hc hpc he4 hB h10 h11 h12
    h13 h2 h1 hra4 hin hil hout hw8 hram hdis hMo hMw (by simp only at hlt; omega)

theorem a0Oom_flag : UInt64.ofBitVec a0Oom = oomFlag := by decide

/-- **C runs correctly with any work block, and reports out of memory exactly below `memoryNeeded`** -/
theorem C_runs (HS : ShiftInv) : CompileRuns riscv compileC := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight outputFits
  obtain ⟨x⟩ := program
  unfold compileC at compiles
  split at compiles
  · rename_i hc
    have hcomp := Option.some.inj compiles
    subst hcomp
    obtain ⟨hne, hx⟩ := hc
    obtain ⟨ts, p, hL, hP, -, hI, hX⟩ := compiler_correctG bndStage
      (fun B p => ImplementsCW B (Sem κC p) (fun inp => max 16 (Msp p inp)) ∧
        ExactCW B (Sem κC p) (fun inp => max 16 (Msp p inp)))
      (fun c ts p hp hts hL h => ⟨gen_implementsM c hp hts hL h, gen_exact HS c ts p hp hts hL h⟩) x hx hne
    have hpo := pOf_eq hL hP
    have hW : ImplementsCW (mC x) (Sem κC p) (spaceC x) := by unfold spaceC; rw [hpo]; exact hI
    have hXW : ExactCW (mC x) (Sem κC p) (spaceC x) := by unfold spaceC; rw [hpo]; exact hX
    have hrun : Sem κC p (encodeInput argument) = .ok (encodeOutput (f argument)) := by
      have := computes argument
      change srcRun ⟨x⟩ (encodeInput argument) = _ at this
      simp only [srcRun, hpo, Option.bind_some] at this
      exact toOption_some this
    have hMN : memoryNeeded ⟨mC x, 1, fun inp => [.alloc (spaceC x inp)]⟩ (encodeInput argument) =
        spaceC x (encodeInput argument) := by simp [memoryNeeded, peak, inUse]
    unfold OutOfMemory; rw [hMN]
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
    by_cases hlt : call.workLength < spaceC x (encodeInput argument)
    · -- below the bound: the out-of-memory return
      have run := hXW (encodeInput argument) startState (BitVec.ofNat 64 pc.toNat) (BitVec.ofNat 64 call.returnAddress.toNat)
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
        _ hrun hlt

      obtain ⟨steps, finishState, hsteps, hpcFinish, hkept, hcfg, h10, -, hunchanged⟩ := run
      refine ⟨finishState, runs_of_steps steps _ _ hsteps, ?_, ?_, ?_, kept_of hkept, hcfg⟩
      · simp [riscvObserve, hpcFinish]
      · intro address _ hwork
        simp only [riscvObserve]
        rw [hunchanged address.toNat (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
          exact hwork)]
      · simp only [riscvObserve, riscvRegister, h10, Option.map_some, Option.getD_some, a0Oom_flag]
        exact ⟨fun _ => hlt, fun _ => trivial⟩
    · -- at or above the bound: the normal return
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
      · exact absurd hoom hlt
      refine ⟨finishState, runs_of_steps steps _ _ hsteps, ?_, ?_, ?_, kept_of hkept, hcfg⟩
      · simp [riscvObserve, hpcFinish]
      · intro address hout hwork
        simp only [riscvObserve]
        rw [hunchanged address.toNat (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          exact ⟨hout, hwork⟩)]
      · simp only [riscvObserve, riscvRegister, h10, Option.map_some, Option.getD_some]
        exact ⟨fun h => absurd h (a0Ok_ne _), fun h => absurd h hlt⟩
  · cases compiles

end NanoMain
