/- **The chaining adapter**: a compiler with the strengthened statement `CompileCorrect riscv compile`
(`Spec/Alloc.lean`) yields `Implements1With encA encB code f space maxLen retLen` for every program it compiles
(code bytes `wordBytes code`), whenever `space` bounds `memoryNeeded`.  `Implements1With` is the form
`Nano.Link.link_stage` chains (with `retLen = true`).  The reverse of `implements1_top` (`Riscv/Back/Top.lean`). -/
import Nano.Base.Riscv.Back.Top
import Nano.Base.Compiler.AllocSpec
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

namespace Proven.Top
open Proven Proven.Top.Alloc

theorem retires_of_step {state next : St} (h : riscv.step state = some next) : Retires state next := by
  change riscvStep state = some next at h
  unfold riscvStep at h
  split at h
  · next w s₁ next' h1 h2 => cases h; exact ⟨⟨w, s₁, h1⟩, h2⟩
  · exact nomatch h

theorem steps_of_runs : ∀ {state finish : riscv.State}, Runs riscv state finish → ∃ n, Steps n state finish
  | _, _, .stop => ⟨0, rfl⟩
  | _, _, .step hstep hr => let ⟨n, hn⟩ := steps_of_runs hr; ⟨n + 1, _, retires_of_step hstep, hn⟩

theorem ofBitVec_inj {a b : BitVec 64} (h : UInt64.ofBitVec a = UInt64.ofBitVec b) : a = b :=
  congrArg UInt64.toBitVec h

theorem obs_get {o : Option (BitVec 64)} {v : BitVec 64} (h : o = some v) :
    (o.map UInt64.ofBitVec).getD 0 = UInt64.ofBitVec v := by rw [h]; rfl

theorem ofBitVec_ofNat (n : Nat) : UInt64.ofBitVec (BitVec.ofNat 64 n) = n.toUInt64 := rfl

theorem toUInt64_toNat {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- the observed value of an integer register of a configured state -/
theorem obs_reg {s : St} (h : Cfg s) : ∀ (j : Fin 32), j ≠ 0 →
    (riscvObserve s).register j.val = UInt64.ofBitVec (getX s j)
  | ⟨0, _⟩, hj => absurd rfl hj
  | ⟨1, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x1]
  | ⟨2, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x2]
  | ⟨3, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x3]
  | ⟨4, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x4]
  | ⟨5, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x5]
  | ⟨6, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x6]
  | ⟨7, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x7]
  | ⟨8, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x8]
  | ⟨9, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x9]
  | ⟨10, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x10]
  | ⟨11, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x11]
  | ⟨12, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x12]
  | ⟨13, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x13]
  | ⟨14, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x14]
  | ⟨15, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x15]
  | ⟨16, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x16]
  | ⟨17, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x17]
  | ⟨18, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x18]
  | ⟨19, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x19]
  | ⟨20, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x20]
  | ⟨21, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x21]
  | ⟨22, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x22]
  | ⟨23, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x23]
  | ⟨24, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x24]
  | ⟨25, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x25]
  | ⟨26, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x26]
  | ⟨27, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x27]
  | ⟨28, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x28]
  | ⟨29, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x29]
  | ⟨30, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x30]
  | ⟨31, _⟩, _ => by simp [riscvObserve, riscvRegister, h.x31]
  | ⟨n + 32, hn⟩, _ => absurd hn (by omega)

/-- **`CompileCorrect` on RISC-V with the frame on every address of the Sail memory map.** `Spec/Top.lean` observes
memory at `UInt64` addresses only, while `Implements1With` (`unchangedOutside`) frames every `Nat` key of the Sail
memory map; this statement adds that (the RISC-V back ends prove it, `Ir.machine_runL`). -/
def CompileCorrectRV {P : Type} [Program P] (compile : P → Option CompiledA) : Prop :=
  ∀ {α β : Type} (program : P) (compiled : CompiledA) (f : α → β) (encodeInput : α → List UInt8)
    (encodeOutput : β → List UInt8) (argument : α) (startState : St) (call : Call),
    compile program = some compiled →
    Computes program f encodeInput encodeOutput →
    StartCorrect riscv startState call compiled.code (encodeInput argument) →
    (encodeOutput (f argument)).length ≤ call.outputLength →
    memoryNeeded compiled (encodeInput argument) ≤ call.workLength →
    ∃ finishState : St, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
      readMemory (riscv.observe finishState) call.outputAddress (encodeOutput (f argument)).length
        = some (encodeOutput (f argument)) ∧
      (riscv.observe finishState).register riscv.mapping.outputLength =
        (encodeOutput (f argument)).length.toUInt64 ∧
      (∀ a : Nat, (a < call.outputAddress.toNat ∨ call.outputAddress.toNat + (encodeOutput (f argument)).length ≤ a) →
        (a < call.workAddress.toNat ∨ call.workAddress.toNat + call.workLength ≤ a) →
        finishState.mem[a]? = startState.mem[a]?) ∧
      KeptRegisters riscv startState finishState ∧ Cfg finishState

theorem CompileCorrectRV.correctL {P : Type} [Program P] {compile : P → Option CompiledA}
    (h : CompileCorrectRV compile) : CompileCorrect riscv compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call hc hf hs ho hm
  obtain ⟨finish, hr, hpc, hflag, hread, hlen, hframe, hkept, hcfg⟩ :=
    h program compiled f encodeInput encodeOutput argument startState call hc hf hs ho hm
  refine ⟨finish, hr, hpc, hflag, hread, hlen, fun address h1 h2 => ?_, hkept, hcfg⟩
  unfold Outside at h1 h2; dsimp only at h1 h2
  show (finish.mem[address.toNat]?).map UInt8.ofBitVec = (startState.mem[address.toNat]?).map UInt8.ofBitVec
  rw [hframe address.toNat h1 h2]

/-- **The adapter**: `CompileCorrectRV` (`CompileCorrect` with the full memory frame) for a compiler gives `Implements1With` for each compiled program -/
theorem implements_of_compileL {P : Type} [Program P] {compile : P → Option CompiledA}
    (correct : CompileCorrectRV compile) {program : P} {compiled : CompiledA} {code : List (BitVec 32)}
    {α β : Type} {encA : α → List UInt8} {encB : β → List UInt8} {f : α → β} {space : Nat → Nat}
    {maxLen : Nat} {retLen : Bool}
    (compiles : compile program = some compiled) (hcode : compiled.code = wordBytes code)
    (computes : Computes program f encA encB)
    (hspace : ∀ a, (encA a).length ≤ maxLen → memoryNeeded compiled (encA a) ≤ space (encA a).length)
    (hmax : maxLen ≤ 2 ^ 20) :
    Implements1With encA encB code f space maxLen retLen := by
  intro a s entry ra input output work
  dsimp only
  intro hx hcfg hpc hal hcodeB h10 h11 h12 h13 h2 h1 hra hrac hin hil hyo
    hsp hwal hram hdisj hmo hmw
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Region.inRAM] at hram
  obtain ⟨⟨ri1, ri2⟩, ⟨ro1, ro2⟩, ⟨rw1, rw2⟩, ⟨rc1, rc2⟩⟩ := hram
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true, Proven.disjoint] at hdisj
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34, -⟩ := hdisj
  have hcl : (wordBytes code).length = 4 * code.length := wordBytes_length code
  let call : Call := ⟨UInt64.ofBitVec ra, input.base.toUInt64, (encA a).length, work.base.toUInt64, work.len,
    output.base.toUInt64, output.len⟩
  have hpcObs : (riscvObserve s).programCounter = UInt64.ofBitVec entry := obs_get hpc
  have hen : (UInt64.ofBitVec entry).toNat = entry.toNat := rfl
  have tI : input.base.toUInt64.toNat = input.base := toUInt64_toNat (by omega)
  have tO : output.base.toUInt64.toNat = output.base := toUInt64_toNat (by omega)
  have tW : work.base.toUInt64.toNat = work.base := toUInt64_toNat (by omega)
  have hstart : StartCorrect riscv s call compiled.code (encA a) := {
    configured := hcfg
    codeLoaded := by
      show readMemory (riscvObserve s) (riscvObserve s).programCounter compiled.code.length = some compiled.code
      rw [hpcObs, hcode]
      refine (readMemory_riscv s _ (by rw [hen, hcl]; omega)).2 ?_
      rw [hen, hcl, wordBytes_codeBytes]; exact hcodeB
    inputLoaded := by
      show readMemory (riscvObserve s) input.base.toUInt64 (encA a).length = some (encA a)
      refine (readMemory_riscv s _ (by rw [tI]; omega)).2 ?_
      rw [tI]; exact hin
    inputLength := rfl
    inputSmall := by omega
    returnRegister := obs_get h1
    inputRegister := obs_get h10
    lengthRegister := obs_get h11
    workRegister := obs_get h12
    workTopRegister := by
      show ((s.regs.get? .x2).map UInt64.ofBitVec).getD 0 = work.base.toUInt64 + work.len.toUInt64
      rw [obs_get h2, ofBitVec_ofNat, Nat.toUInt64_eq, Nat.toUInt64_eq, Nat.toUInt64_eq, UInt64.ofNat_add]
    outputRegister := obs_get h13
    codeAligned := by show (riscvObserve s).programCounter.toNat % 4 = 0; rw [hpcObs, hen]; exact hal
    returnAligned := hra
    workAligned := by show work.base.toUInt64.toNat % 8 = 0; rw [tW]; exact hwal
    returnOutsideCode := by
      show Apart (UInt64.ofBitVec ra, 4) ((riscvObserve s).programCounter, compiled.code.length)
      rw [hpcObs, hcode]; unfold Apart; dsimp only; rw [hen, hcl]
      have : (UInt64.ofBitVec ra).toNat = ra.toNat := rfl
      rw [this]; exact hrac
    inRam := by
      show ∀ block ∈ [(input.base.toUInt64, (encA a).length), (output.base.toUInt64, output.len),
        (work.base.toUInt64, work.len), ((riscvObserve s).programCounter, compiled.code.length)],
        0x80000000 ≤ block.1.toNat ∧ block.1.toNat + block.2 ≤ 0x100000000
      rw [hpcObs, hcode]
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, tI, tO, tW, hen, hcl]
      omega
    disjoint := by
      show [(input.base.toUInt64, (encA a).length), (output.base.toUInt64, output.len),
        (work.base.toUInt64, work.len), ((riscvObserve s).programCounter, compiled.code.length)].Pairwise Apart
      rw [hpcObs, hcode]
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        List.Pairwise.nil, and_true, Apart, tI, tO, tW, hen, hcl]
      rw [← hil]
      exact ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34, fun _ h => h.elim⟩
    outputPresent := fun i hi => by
      show ((s.mem[(output.base.toUInt64 + i.toUInt64).toNat]?).map UInt8.ofBitVec).isSome
      rw [toNat_add_offset (bound := output.len) (by rw [tO]; omega) hi, tO, Option.isSome_map]
      exact hmo i hi
    workPresent := fun i hi => by
      show ((s.mem[(work.base.toUInt64 + i.toUInt64).toNat]?).map UInt8.ofBitVec).isSome
      rw [toNat_add_offset (bound := work.len) (by rw [tW]; omega) hi, tW, Option.isSome_map]
      exact hmw i hi }
  obtain ⟨finish, hruns, hpcF, -, hread, hlen, hframe, hkept, hcfgF⟩ :=
    correct program compiled f encA encB a s call compiles computes hstart hyo (Nat.le_trans (hspace a hx) hsp)
  obtain ⟨n, hn⟩ := steps_of_runs hruns
  refine ⟨n, finish, hn, ?_, ?_, ?_, ?_, hcfgF, fun _ => ?_⟩
  · have hs := isSome_of_cfg hcfgF (register := .PC) (by simp)
    cases e : finish.regs.get? .PC with
    | none => rw [e] at hs; exact nomatch hs
    | some v =>
      have : (riscvObserve finish).programCounter = UInt64.ofBitVec v := obs_get e
      have e2 : UInt64.ofBitVec v = UInt64.ofBitVec ra := this.symm.trans hpcF
      rw [ofBitVec_inj e2]
  · have := (readMemory_riscv finish (address := output.base.toUInt64) (encB (f a)) (by rw [tO]; omega)).1 hread
    rw [tO] at this; rw [this]
  · intro addr haddr
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at haddr
    obtain ⟨ho, hw⟩ := haddr
    exact hframe addr (by rw [tO]; exact ho) (by rw [tW]; exact hw)
  · have kx : ∀ (j : Fin 32), j ≠ 0 → j.val ∈ riscv.mapping.kept → getX finish j = getX s j := fun j hj hm => by
      have := hkept j.val hm
      change (riscvObserve finish).register j.val = (riscvObserve s).register j.val at this
      rw [obs_reg hcfgF j hj, obs_reg hcfg j hj] at this
      exact ofBitVec_inj this
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hcfgF.x2, hcfg.x2, kx 2 (by decide) (by decide)]
    · rw [hcfgF.x3, hcfg.x3, kx 3 (by decide) (by decide)]
    · rw [hcfgF.x4, hcfg.x4, kx 4 (by decide) (by decide)]
    · rw [hcfgF.x8, hcfg.x8, kx 8 (by decide) (by decide)]
    · rw [hcfgF.x9, hcfg.x9, kx 9 (by decide) (by decide)]
    · rw [hcfgF.x18, hcfg.x18, kx 18 (by decide) (by decide)]
    · rw [hcfgF.x19, hcfg.x19, kx 19 (by decide) (by decide)]
    · rw [hcfgF.x20, hcfg.x20, kx 20 (by decide) (by decide)]
    · rw [hcfgF.x21, hcfg.x21, kx 21 (by decide) (by decide)]
    · rw [hcfgF.x22, hcfg.x22, kx 22 (by decide) (by decide)]
    · rw [hcfgF.x23, hcfg.x23, kx 23 (by decide) (by decide)]
    · rw [hcfgF.x24, hcfg.x24, kx 24 (by decide) (by decide)]
    · rw [hcfgF.x25, hcfg.x25, kx 25 (by decide) (by decide)]
    · rw [hcfgF.x26, hcfg.x26, kx 26 (by decide) (by decide)]
    · rw [hcfgF.x27, hcfg.x27, kx 27 (by decide) (by decide)]
  · have h11 : (riscvObserve finish).register 11 = UInt64.ofBitVec (getX finish 11) := obs_reg hcfgF 11 (by decide)
    change (riscvObserve finish).register 11 = _ at hlen
    rw [h11] at hlen
    rw [hcfgF.x11, show getX finish 11 = BitVec.ofNat 64 (encB (f a)).length from ofBitVec_inj hlen]

end Proven.Top
