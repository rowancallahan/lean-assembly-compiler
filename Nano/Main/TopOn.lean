/- C's top-level theorems for ANY target (`JT.JTarget` with its `Laws`): `C_correct_on : CompileCorrectP T.M T.loader (compileGen gen)`
and `C_runs_on : CompileRunsP T.M T.loader (compileGen gen)`, for any code generator `gen` from source text to the target's
code bytes that meets `GenOK`: when it emits code for a source `x`, that code is `tbytes T Cj` for the J program `Cj` of
`x` (the one C's driver `mC` derives).  `GenOK` asks nothing about instruction widths or jump ranges of the target
(those are `T`'s business, in `tbytes`/`valid`).  Still RISC-V-shaped in it (until Gen's proof is factored over an
abstract emitter): `Cj` is identified through Gen's RV words (`mC x = g40 … (Cj.map encG)`), and `gen x ≠ []` must
imply `mC x ≠ []`.  A post-translator `enc` of Gen's RV bytes (`EncOK`, e.g. rv2arm) is the instance `enc ∘ mC`
(`genOK_of_enc`, `compileOn enc = compileGen (enc ∘ mC)`).  The target's RAM must start at or above 2^31 (`hwin`: the exact
work bound `Msp` and `ShiftInv` are stated for work blocks there). -/
import Nano.Run.HostOom
import Nano.Main.ParCapBnd
import Nano.SelfHost.Bridge.MainShift4
namespace NanoMain
open Proven.Top Proven.Top.Alloc ParSpec Templates JT

/-- a compiler whose code bytes are `gen` of the source text (memory bound: C's `spaceC`) -/
noncomputable def compileGen (gen : List UInt8 → List UInt8) (s : SrcC) : Option CompiledA :=
  if gen s.text ≠ [] ∧ s.text.length ≤ 2 ^ 20 then some ⟨gen s.text, 1, fun inp => [.alloc (spaceC s.text inp)]⟩
  else none

/-- C as a compiler whose code bytes are `enc` of Gen's bytes -/
noncomputable def compileOn (enc : List UInt8 → List UInt8) (s : SrcC) : Option CompiledA :=
  if enc (mC s.text) ≠ [] ∧ s.text.length ≤ 2 ^ 20 then some ⟨enc (mC s.text), 1, fun inp => [.alloc (spaceC s.text inp)]⟩
  else none

/-- `enc` turns Gen's bytes for its J program `Cj` into the target's code bytes for `Cj` -/
def EncOK (T : JTarget) (enc : List UInt8 → List UInt8) : Prop :=
  enc [] = [] ∧
  ∀ (c : List UInt8) (Cj : List CallProbe.J), Cj.length < 2 ^ 18 →
    (∀ j ∈ Cj, SimW.JOK j) →
    enc (C.g40 16777216 c (Cj.map CallProbe.encG) 0 []) ≠ [] →
    enc (C.g40 16777216 c (Cj.map CallProbe.encG) 0 []) = tbytes T Cj ∧ T.valid Cj

/-- `gen` emits, for a source `x` it accepts, the target's code bytes of `x`'s J program `Cj` (the program whose RV
words are C's output `mC x`).  `Cj.length < 2^18` and `JOK` are facts Gen provides (usable by a `gen`), not demands. -/
def GenOK (T : JTarget) (gen : List UInt8 → List UInt8) : Prop :=
  ∀ x, gen x ≠ [] → mC x ≠ [] ∧
    ∀ (c : List UInt8) (Cj : List CallProbe.J), Cj.length < 2 ^ 18 → (∀ j ∈ Cj, SimW.JOK j) →
      mC x = C.g40 16777216 c (Cj.map CallProbe.encG) 0 [] → gen x = tbytes T Cj ∧ T.valid Cj

theorem compileOn_gen (enc : List UInt8 → List UInt8) : compileOn enc = compileGen (enc ∘ mC) := rfl

/-- a post-translator of Gen's bytes is a generator -/
theorem genOK_of_enc {T : JTarget} {enc : List UInt8 → List UInt8} (hE : EncOK T enc) : GenOK T (enc ∘ mC) :=
  fun x h => ⟨fun e => h (by rw [Function.comp_apply, e]; exact hE.1), fun c Cj hc hw hg => by
    rw [Function.comp_apply, hg]
    exact hE.2 c Cj hc hw (by rw [← hg]; exact h)⟩

/-- the facts codegen provides for Gen's bytes `B` of program `p` -/
def GenFacts (B : List UInt8) (p : List DefA) : Prop :=
  ∃ c ts, B = C.g41 c (serialize p) ∧ ParsesProgram ts p ∧ ts.length < 2 ^ 24 ∧ LinearK p ∧ C.g41 c (serialize p) ≠ []

/-- the source text's program, its codegen facts and its meaning on the argument -/
theorem src_facts {x : List UInt8} (hne : mC x ≠ []) (hx : x.length ≤ 2 ^ 20) {α β : Type} {f : α → β}
    {encodeInput : α → List UInt8} {encodeOutput : β → List UInt8}
    (computes : Computes (⟨x⟩ : SrcC) f encodeInput encodeOutput) (argument : α) :
    ∃ p, GenFacts (mC x) p ∧ spaceC x = (fun inp => max 16 (Msp p inp)) ∧
      Sem κC p (encodeInput argument) = .ok (encodeOutput (f argument)) := by
  obtain ⟨ts, p, hL, hP, -, hQ⟩ := compiler_correctG bndStage GenFacts
    (fun c ts p hp hts hl h => ⟨c, ts, rfl, hp, hts, hl, h⟩) x hx hne
  have hpo := pOf_eq hL hP
  refine ⟨p, hQ, by unfold spaceC; rw [hpo], ?_⟩
  have := computes argument
  change srcRun ⟨x⟩ (encodeInput argument) = _ at this
  simp only [srcRun, hpo, Option.bind_some] at this
  exact toOption_some this

theorem ok_ne_oom (y : List UInt8) : (if y = [] then (1 : UInt64) else 0) ≠ oomFlag := by
  split <;> decide

variable {T : JTarget}

/-- `CompileCorrect` for the start states that also meet a loader contract `ld` (Spec's statement when `ld` is `True`) -/
def CompileCorrectP {P : Type} [Program P] (machine : Machine) (ld : machine.State → Call → List UInt8 → List UInt8 → Prop)
    (compile : P → Option CompiledA) : Prop :=
  ∀ {α β : Type} (program : P) (compiled : CompiledA) (f : α → β) (encodeInput : α → List UInt8)
    (encodeOutput : β → List UInt8) (argument : α) (startState : machine.State) (call : Call),
    compile program = some compiled →
    Computes program f encodeInput encodeOutput →
    StartCorrect machine startState call compiled.code (encodeInput argument) →
    ld startState call compiled.code (encodeInput argument) →
    (encodeOutput (f argument)).length ≤ call.outputLength →
    memoryNeeded compiled (encodeInput argument) ≤ call.workLength →
    ∃ finishState, Runs machine startState finishState ∧
      (machine.observe finishState).programCounter = call.returnAddress ∧
      (machine.observe finishState).register machine.mapping.status ≠ oomFlag ∧
      readMemory (machine.observe finishState) call.outputAddress (encodeOutput (f argument)).length
        = some (encodeOutput (f argument)) ∧
      (machine.observe finishState).register machine.mapping.outputLength = (encodeOutput (f argument)).length.toUInt64 ∧
      (∀ address, Outside address (call.outputAddress, (encodeOutput (f argument)).length) →
        Outside address (call.workAddress, call.workLength) →
        (machine.observe finishState).memory address = (machine.observe startState).memory address) ∧
      KeptRegisters machine startState finishState ∧ machine.configured finishState

/-- `CompileRuns` for the start states that also meet a loader contract `ld` -/
def CompileRunsP {P : Type} [Program P] (machine : Machine) (ld : machine.State → Call → List UInt8 → List UInt8 → Prop)
    (compile : P → Option CompiledA) : Prop :=
  ∀ {α β : Type} (program : P) (compiled : CompiledA) (f : α → β) (encodeInput : α → List UInt8)
    (encodeOutput : β → List UInt8) (argument : α) (startState : machine.State) (call : Call),
    compile program = some compiled →
    Computes program f encodeInput encodeOutput →
    StartCorrect machine startState call compiled.code (encodeInput argument) →
    ld startState call compiled.code (encodeInput argument) →
    (encodeOutput (f argument)).length ≤ call.outputLength →
    ∃ finishState, Runs machine startState finishState ∧
      (machine.observe finishState).programCounter = call.returnAddress ∧
      (∀ address, Outside address (call.outputAddress, (encodeOutput (f argument)).length) →
        Outside address (call.workAddress, call.workLength) →
        (machine.observe finishState).memory address = (machine.observe startState).memory address) ∧
      ((machine.observe finishState).register machine.mapping.status = oomFlag ↔
        OutOfMemory compiled (encodeInput argument) call.workLength) ∧
      KeptRegisters machine startState finishState ∧ machine.configured finishState

theorem cc_of_P {P : Type} [Program P] {machine : Machine} {compile : P → Option CompiledA}
    (h : CompileCorrectP machine (fun _ _ _ _ => True) compile) : CompileCorrect machine compile :=
  fun program compiled f eI eO a s call h1 h2 h3 h4 h5 => h program compiled f eI eO a s call h1 h2 h3 trivial h4 h5

theorem cr_of_P {P : Type} [Program P] {machine : Machine} {compile : P → Option CompiledA}
    (h : CompileRunsP machine (fun _ _ _ _ => True) compile) : CompileRuns machine compile :=
  fun program compiled f eI eO a s call h1 h2 h3 h4 => h program compiled f eI eO a s call h1 h2 h3 trivial h4

/-- the normal return when the work block holds at least `Msp` bytes -/
theorem run_ok (L : T.Laws) {gen : List UInt8 → List UInt8} (hE : GenOK T gen) (hwin : 2 ^ 31 ≤ T.M.ramStart)
    {src : List UInt8} {p : List DefA} (hG : GenFacts (mC src) p) {s : T.M.State} {call : Call} {x y : List UInt8}
    (hne : gen src ≠ []) (sc : StartCorrect T.M s call (gen src) x) (hld : T.loader s call (gen src) x) (hSem : Sem κC p x = .ok y) (hy : y.length ≤ call.outputLength)
    (hmem : max 16 (Msp p x) ≤ call.workLength) :
    ∃ s', Runs T.M s s' ∧ (T.M.observe s').programCounter = call.returnAddress ∧
      (T.M.observe s').register T.M.mapping.status ≠ oomFlag ∧
      readMemory (T.M.observe s') call.outputAddress y.length = some y ∧
      (T.M.observe s').register T.M.mapping.outputLength = y.length.toUInt64 ∧
      (∀ a, Outside a (call.outputAddress, y.length) → Outside a (call.workAddress, call.workLength) →
        (T.M.observe s').memory a = (T.M.observe s).memory a) ∧
      KeptRegisters T.M s s' ∧ T.M.configured s' := by
  obtain ⟨c, ts, hB, hP, hts, hL, h⟩ := hG
  obtain ⟨Ks, hO, hK2⟩ := hL
  obtain ⟨-, -, -, -, c1, c2, -, -, -, -, -, -, -, -, -⟩ := blocks_of L sc
  have r32 := L.ram.2
  have wa := sc.workAligned
  have hl16 := Nat.le_max_left 16 (Msp p x)
  have hlM := Nat.le_max_right 16 (Msp p x)
  rcases gen_HDM hP ⟨Ks, hO, hK2⟩ x sc.inputSmall call.workAddress.toNat call.workLength wa (by omega) (by omega)
    (by omega) with ⟨y', hS', hS⟩ | ⟨hS', -⟩ | ⟨-, hlt⟩
  · rw [hSem] at hS'; cases hS'
    obtain ⟨s', r, pc, st, ol, rd, fr, kp, cf⟩ := host_ok L c hP Ks hO hK2 (ParSerLen.ser_lt hP hts) h
      (dbStage capStage c ts p hP hts ⟨Ks, hO, hK2⟩ h) _
      (fun Cj hc hg hw => (hE src hne).2 c Cj hc hw (hB.trans hg)) sc hld y hSem hy (by omega) hS
    exact ⟨s', r, pc, by rw [st]; exact ok_ne_oom y, rd, ol, fr, kp, cf⟩
  · rw [hSem] at hS'; cases hS'
  · omega

/-- **C is correct on any target** (owner's `CompileCorrect`) -/
theorem C_correct_on (L : T.Laws) (gen : List UInt8 → List UInt8) (hE : GenOK T gen) (hwin : 2 ^ 31 ≤ T.M.ramStart) :
    CompileCorrectP T.M T.loader (compileGen gen) := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight loads
    outputFits enough
  obtain ⟨x⟩ := program
  unfold compileGen at compiles
  split at compiles
  · rename_i hc
    cases Option.some.inj compiles
    obtain ⟨p, hG, hsp, hSem⟩ := src_facts (hE x hc.1).1 hc.2 computes argument
    have hmem : max 16 (Msp p (encodeInput argument)) ≤ call.workLength := by
      have := enough; simp only [memoryNeeded, peak, inUse, hsp] at this; simpa using this
    exact run_ok L hE hwin hG hc.1 startsRight loads hSem outputFits hmem
  · cases compiles

/-- **C runs correctly on any target, with any work block** (owner's `CompileRuns`) -/
theorem C_runs_on (L : T.Laws) (gen : List UInt8 → List UInt8) (hE : GenOK T gen) (hwin : 2 ^ 31 ≤ T.M.ramStart) :
    CompileRunsP T.M T.loader (compileGen gen) := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight loads
    outputFits
  obtain ⟨x⟩ := program
  unfold compileGen at compiles
  split at compiles
  · rename_i hc
    cases Option.some.inj compiles
    obtain ⟨p, hG, hsp, hSem⟩ := src_facts (hE x hc.1).1 hc.2 computes argument
    have hMN : memoryNeeded ⟨gen x, 1, fun inp => [.alloc (spaceC x inp)]⟩ (encodeInput argument) =
        max 16 (Msp p (encodeInput argument)) := by simp [memoryNeeded, peak, inUse, hsp]
    unfold OutOfMemory; rw [hMN]
    by_cases hlt : call.workLength < max 16 (Msp p (encodeInput argument))
    · -- below the bound: out of memory
      obtain ⟨c, ts, hB, hP, hts, hL, h⟩ := hG
      obtain ⟨Ks, hO, hK2⟩ := hL
      have hBe : ∀ Cj : List CallProbe.J, Cj.length < 2 ^ 18 →
          C.g41 c (serialize p) = C.g40 16777216 c (Cj.map CallProbe.encG) 0 [] →
          (∀ j ∈ Cj, SimW.JOK j) → gen x = tbytes T Cj ∧ T.valid Cj :=
        fun Cj hc' hg hw => (hE x hc.1).2 c Cj hc' hw (hB.trans hg)
      obtain ⟨-, -, -, -, c1, c2, -, -, -, -, -, -, -, -, -⟩ := blocks_of L startsRight
      have r32 := L.ram.2
      have wa := startsRight.workAligned
      have fin : ∀ s', (T.M.observe s').register T.M.mapping.status = oomFlag →
          (∀ a, Outside a (call.workAddress, call.workLength) →
            (T.M.observe s').memory a = (T.M.observe startState).memory a) →
          ((T.M.observe s').register T.M.mapping.status = oomFlag ↔ call.workLength < max 16 (Msp p (encodeInput argument))) ∧
          (∀ a, Outside a (call.outputAddress, (encodeOutput (f argument)).length) →
            Outside a (call.workAddress, call.workLength) →
            (T.M.observe s').memory a = (T.M.observe startState).memory a) :=
        fun s' hst hfr => ⟨⟨fun _ => hlt, fun _ => hst⟩, fun a _ hw => hfr a hw⟩
      by_cases hsm : (call.workAddress.toNat + call.workLength) / 8 * 8 < call.workAddress.toNat + 16
      · obtain ⟨s', r, pc, st, fr, kp, cf⟩ := host_tiny L c hP Ks hO hK2 (ParSerLen.ser_lt hP hts) h
          (dbStage capStage c ts p hP hts ⟨Ks, hO, hK2⟩ h) _ hBe startsRight loads hsm
        exact ⟨s', r, pc, (fin s' st fr).2, (fin s' st fr).1, kp, cf⟩
      · have hl16 : 16 ≤ Msp p (encodeInput argument) := Msp_ge p _
        have hxl := startsRight.inputSmall
        obtain ⟨s', r, pc, st, fr, kp, cf⟩ := host_room L c hP Ks hO hK2 (ParSerLen.ser_lt hP hts) h
          (dbStage capStage c ts p hP hts ⟨Ks, hO, hK2⟩ h) _ hBe startsRight loads (by omega) (fun Tb => by
            have e : (call.workAddress.toNat + call.workLength) / 8 * 8 =
                call.workAddress.toNat + 16 + (call.workLength / 8 * 8 - 16) := by omega
            have := lt_room shiftInv hP hts ⟨Ks, hO, hK2⟩ hxl (T := Tb) (hb := call.workAddress.toNat + 16)
              (u := call.workLength / 8 * 8 - 16) (by omega) (by omega) (by omega) (by unfold Msp at hlt; omega)
            unfold RS at this; rw [e]; exact this)
        exact ⟨s', r, pc, (fin s' st fr).2, (fin s' st fr).1, kp, cf⟩
    · -- at or above the bound: the normal return
      obtain ⟨s', r, pc, st, -, -, fr, kp, cf⟩ := run_ok L hE hwin hG hc.1 startsRight loads hSem outputFits (by omega)
      exact ⟨s', r, pc, fr, ⟨fun h => absurd h st, fun h => absurd h hlt⟩, kp, cf⟩
  · cases compiles

end NanoMain
