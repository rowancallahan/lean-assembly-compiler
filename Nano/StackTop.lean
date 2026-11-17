/- **L2: the stack generator on RISC-V.**  `nanoCompileA p = some ⟨nanoGen p, 8, events⟩` (`nanoGen p = asm (genR p)`,
`Nano/Gen.lean`) for programs whose variables are in scope and whose stack depth fits the 8-bit offsets
(`depth p ≤ 256`); the events of a run are one allocation of `depth p` 8-byte cells, so `memoryNeeded = 8 · depth p`.

* `nano_stack_runs : CompileRuns riscv nanoCompileA` (returns, frame kept, `oomFlag` exactly when out of memory);
* `nano_stack_correct : CompileCorrect riscv nanoCompileA` (with `memoryNeeded` bytes: the result, no flag),
for the `Program Prog` instance of `Nano/Proof.lean` (`nanoRun`: 8-byte little-endian argument words, `Prog.eval`,
the result as 8 little-endian bytes).  Proof: the record machine runs `genR p` (`genR_ok`/`genR_oom`,
`Nano/StackRun.lean`), the Sail model refines it (`sim_star`/`sim_halt`, `Nano/StackSim.lean`). -/
import Nano.StackSim
import Nano.Proof

set_option linter.unusedVariables false
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

namespace Nano
open Proven Proven.Top Proven.Top.Alloc Nano.R Nano.F Nano.S

/-- programs the stack generator handles: variables in scope, stack depth within the 8-bit slot offsets -/
def stackOk (p : Prog) : Bool := ScE p.2 p.1 && decide (depth p ≤ 256)

/-- **the stack-path compiler** (code `nanoGen p = asm (genR p)`) -/
def nanoCompileA (p : Prog) : Option CompiledA :=
  if stackOk p then some ⟨nanoGen p, 8, fun _ => [.alloc (depth p)]⟩ else none

theorem nanoCompileA_code {p : Prog} {c : CompiledA} (h : nanoCompileA p = some c) : c.code = nanoGen p := by
  unfold nanoCompileA at h; split at h
  · cases h; rfl
  · cases h

theorem nanoCompileA_inv {p : Prog} {c : CompiledA} (h : nanoCompileA p = some c) :
    ScE p.2 p.1 = true ∧ depth p ≤ 256 ∧ c = ⟨nanoGen p, 8, fun _ => [.alloc (depth p)]⟩ := by
  unfold nanoCompileA at h; split at h
  · next hok => cases h; simp only [stackOk, Bool.and_eq_true, decide_eq_true_eq] at hok; exact ⟨hok.1, hok.2, rfl⟩
  · cases h

theorem memoryNeeded_eq {p : Prog} (input : List UInt8) :
    memoryNeeded ⟨nanoGen p, 8, fun _ => [.alloc (depth p)]⟩ input = 8 * depth p := by
  simp [memoryNeeded, peak, inUse]

/-! ## bytes -/

theorem allFam_len4 : ∀ (l : List UInt8), allFam l = true → l.length % 4 = 0
  | [], _ => rfl
  | _ :: _ :: _ :: _ :: rest, h => by
    simp only [allFam, Bool.and_eq_true] at h; have := allFam_len4 rest h.2; simp; omega
  | [_], h => by simp [allFam] at h
  | [_, _], h => by simp [allFam] at h
  | [_, _, _], h => by simp [allFam] at h

theorem leN_get : ∀ (k n i : Nat), i < k → (leN k n)[i]? = some (UInt8.ofNat (n / 256 ^ i))
  | k + 1, n, 0, _ => by simp [leN]; apply UInt8.toNat_inj.mp; simp [UInt8.toNat_ofNat']
  | k + 1, n, i + 1, h => by
    simp only [leN, List.getElem?_cons_succ]; rw [leN_get k (n / 256) i (by omega)]
    rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (256 ^ i)]

theorem byteOf_eq (v : BitVec 64) (i : Nat) : byteOf v i = UInt8.ofNat (v.toNat / 256 ^ i) := by
  apply UInt8.toNat_inj.mp
  simp [byteOf, UInt8.toNat_ofNat', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem mem_of_bytesAt {t : Proven.St} {a : Nat} {bytes : List UInt8}
    (h : bytesAt t a bytes.length = bytes.map (some ·.toBitVec)) :
    ∀ i (hi : i < bytes.length), t.mem[a + i]? = some bytes[i].toBitVec := fun i hi => by
  have := congrArg (·[i]?) h
  simp only [bytesAt, List.getElem?_map, List.getElem?_range hi, Option.map_some] at this
  rw [List.getElem?_eq_getElem hi] at this; simpa using this

theorem present_mem {t : Proven.St} {address : UInt64} {length : Nat}
    (hP : Present (riscvObserve t) address length) (hb : address.toNat + length ≤ 2 ^ 64) :
    ∀ i, i < length → ∃ b, t.mem[address.toNat + i]? = some b := fun i hi => by
  have := hP i hi
  simp only [riscvObserve, toNat_add_offset hb hi] at this
  cases h : t.mem[address.toNat + i]? with
  | none => rw [h] at this; simp at this
  | some b => exact ⟨b, rfl⟩

/-- **the machine run** of `nanoGen p` from `StartCorrect`, both outcomes -/
theorem stack_run {p : Prog} {compiled : CompiledA} {input out : List UInt8} {startState : riscv.State}
    {call : Call} (compiles : nanoCompileA p = some compiled) (computes : nanoRun p input = some out)
    (startsRight : StartCorrect riscv startState call compiled.code input) (outputFits : out.length ≤ call.outputLength) :
    ∃ finishState, Runs riscv startState finishState ∧
      (riscv.observe finishState).programCounter = call.returnAddress ∧
      (∀ address, Outside address (call.outputAddress, call.outputLength) →
        Outside address (call.workAddress, call.workLength) →
        (riscv.observe finishState).memory address = (riscv.observe startState).memory address) ∧
      ((memoryNeeded compiled input ≤ call.workLength ∧
          (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
          readMemory (riscv.observe finishState) call.outputAddress out.length = some out) ∨
        (call.workLength < memoryNeeded compiled input ∧
          (riscv.observe finishState).register riscv.mapping.status = oomFlag)) := by
  obtain ⟨hsc, hd, rfl⟩ := nanoCompileA_inv compiles
  rw [memoryNeeded_eq]
  -- the meaning
  unfold nanoRun at computes
  cases hw : wordsOf p.1 input with
  | none => rw [hw] at computes; cases computes
  | some args =>
  rw [hw] at computes; simp only [Option.bind_some] at computes
  obtain ⟨hal, hil, h3⟩ := wordsOf_spec _ _ _ hw
  have hout : out = leN 8 (den p.2 args.reverse).toNat := by
    unfold Prog.eval at computes; rw [if_pos hal] at computes; simp at computes; exact computes.symm
  subst hout
  rw [leN_length] at outputFits ⊢
  -- the start state
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
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    List.Pairwise.nil, and_true, Apart] at disjoint
  obtain ⟨⟨d12, d13, d14⟩, ⟨d23, d24⟩, d34⟩ := disjoint
  try dsimp only at codeLoaded rc2 d14 d24 d34
  have hreg := fun (register : Register) hregister => isSome_of_cfg configured (register := register) hregister
  have hpcReg := register_of (hreg .PC (by simp)) hpc
  have h2 := register_of (hreg .x2 (by simp)) workTopRegister
  have h10 := register_of (hreg .x10 (by simp)) inputRegister
  have h12 := register_of (hreg .x12 (by simp)) workRegister
  have h13 := register_of (hreg .x13 (by simp)) outputRegister
  have h1 := register_of (hreg .x1 (by simp)) returnRegister
  have g1 : getX startState 1 = BitVec.ofNat 64 call.returnAddress.toNat := getX_of (configured.x1.symm.trans h1) rfl
  have g10 : getX startState 10 = BitVec.ofNat 64 call.inputAddress.toNat :=
    getX_of (configured.x10.symm.trans h10) rfl
  have g12 : getX startState 12 = BitVec.ofNat 64 call.workAddress.toNat :=
    getX_of (configured.x12.symm.trans h12) rfl
  have g13 : getX startState 13 = BitVec.ofNat 64 call.outputAddress.toNat :=
    getX_of (configured.x13.symm.trans h13) rfl
  have g2 : getX startState 2 = BitVec.ofNat 64 (call.workAddress.toNat + call.workLength) := by
    rw [getX_of (configured.x2.symm.trans h2) rfl, toNat_add_offset (bound := call.workLength + 1) (by omega)
      (by omega)]
  -- the code
  have hP4 := allFam_len4 _ (af_genR p)
  have hlen : (nanoGen p).length = (genR p).length := by
    show (asm (genR p)).length = _; rw [asm_length]; omega
  have hcode := (readMemory_riscv startState (address := pc) (length := (nanoGen p).length) _
    (by omega)).1 codeLoaded
  have hcode' := mem_of_bytesAt hcode
  have hinput := mem_of_bytesAt ((readMemory_riscv startState (address := call.inputAddress) _ (by omega)).1
    inputLoaded)
  -- the context
  let C : Ctx := {
    t0 := startState
    pc0 := pc.toNat
    P := genR p
    W := call.workAddress.toNat
    SP := call.workAddress.toNat + call.workLength
    I := call.inputAddress.toNat
    IL := input.length
    O := call.outputAddress.toNat
    RA := call.returnAddress.toNat }
  have hC : C.Ok := {
    p4 := hP4
    code := fun k hk => hcode' k hk
    pcal := codeAligned
    pclo := rc1
    pchi := by simp only [C]; rw [← hlen]; exact rc2
    cW := by simp only [C]; rw [← hlen]; omega
    cO := by simp only [C]; rw [← hlen]; omega
    wlo := rw1
    whi := rw2
    olo := ro1
    ohi := by simp only [C]; omega
    ilo := ri1
    ihi := by simp only [C]; rw [← inputLength]; exact ri2
    wsp := by simp only [C]; omega
    fam := af_genR p
    ra := ⟨returnAligned, UInt64.toNat_lt _⟩ }
  -- the record start state
  let s0 : R.St := {
    x := fun j => if h : j < 32 then getX startState ⟨j, h⟩ else 0
    m := fun a => if C.In a then UInt8.ofBitVec ((startState.mem[a]?).getD 0) else 0
    pc := 0
    g := ⟨C.I, C.IL, C.O⟩ }
  have s0get : ∀ j : Fin 32, s0.get j.val = getX startState j := fun j => by
    show (if j.val = 0 then 0 else if h : j.val < 32 then getX startState ⟨j.val, h⟩ else 0) = _
    by_cases hj : j.val = 0
    · rw [if_pos hj]; have : j = 0 := Fin.ext hj; subst this; rfl
    · rw [if_neg hj, dif_pos j.isLt]
  have s0m : ∀ a b, C.In a → startState.mem[a]? = some b → s0.m a = UInt8.ofBitVec b := fun a b hin hb => by
    show (if C.In a then _ else _) = _; rw [if_pos hin, hb]; rfl
  have hR0 : Rel C s0 startState := {
    cfg := configured
    pc := by rw [hpcReg]; rfl
    x := fun j => (s0get j).symm
    r12 := (s0get 12).trans g12
    r2 := (s0get 2).trans g2
    r1 := (s0get 1).trans g1
    g := rfl
    mem := fun a ha => by
      have hb : ∃ b, startState.mem[a]? = some b := by
        rcases ha with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩
        · obtain ⟨b, hb⟩ := present_mem workPresent (by omega) (a - call.workAddress.toNat) (by simp [C] at a1 a2; omega)
          exact ⟨b, by rw [← hb]; congr 1; simp [C] at a1; omega⟩
        · obtain ⟨b, hb⟩ := present_mem outputPresent (by omega) (a - call.outputAddress.toNat) (by simp [C] at a1 a2; omega)
          exact ⟨b, by rw [← hb]; congr 1; simp [C] at a1; omega⟩
        · have := hinput (a - call.inputAddress.toNat) (by simp [C] at a1 a2; omega)
          exact ⟨_, by rw [← this]; congr 1; simp [C] at a1; omega⟩
      obtain ⟨b, hb⟩ := hb
      rw [hb, s0m a b ha hb]
    frame := fun _ _ _ => rfl }
  -- the record machine's start
  have hinp : ∀ j (hj : j < args.length), unle (rdL s0.m (call.inputAddress.toNat + 8 * j) 8) = args[j].toNat := by
    intro j hj
    have hrd : rdL s0.m (call.inputAddress.toNat + 8 * j) 8 = (input.drop (8 * j)).take 8 := by
      apply List.ext_getElem (by simp [rdL]; omega)
      intro i h1 h2
      simp only [rdL, List.length_map, List.length_range] at h1
      simp only [rdL, List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
      have hi := hinput (8 * j + i) (by omega)
      rw [s0m _ _ (.inr (.inr ⟨by simp only [C]; omega, by simp only [C]; omega⟩))
        (by rw [← hi]; congr 1; omega)]
    have := h3 j (by omega)
    rw [List.getElem?_eq_getElem hj] at this
    rw [Option.some.inj this, hrd, UInt64.toNat_ofNat', Nat.mod_eq_of_lt]
    have := Proven.Mach.Ind.unle_lt ((input.drop (8 * j)).take 8)
    have hl : ((input.drop (8 * j)).take 8).length ≤ 8 := by simp; omega
    have : 256 ^ ((input.drop (8 * j)).take 8).length ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) hl
    have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
    omega
  have hI : Init p s0 call.inputAddress.toNat call.outputAddress.toNat call.workAddress.toNat
      (call.workAddress.toNat + call.workLength) args := {
    pc := rfl
    r2 := (s0get 2).trans g2
    r10 := (s0get 10).trans g10
    r12 := (s0get 12).trans g12
    r13 := (s0get 13).trans g13
    gI := rfl
    gIL := hil
    gO := rfl
    len := hal
    inp := hinp
    wal := workAligned
    w8 := by omega
    wsp := by omega
    sp64 := by omega
    dis := by omega
    i64 := by omega
    o64 := by omega }
  -- from the record machine's halt to the Sail finish
  have finish : ∀ s', Star (genR p) s0 s' → step (genR p) s' = .halt s' → ∃ tf, Runs riscv startState tf ∧
      (riscvObserve tf).programCounter = call.returnAddress ∧
      (∀ address, Outside address (call.outputAddress, call.outputLength) →
        Outside address (call.workAddress, call.workLength) →
        (riscvObserve tf).memory address = (riscvObserve startState).memory address) ∧
      (riscvObserve tf).register 10 = UInt64.ofBitVec (s'.get 10) ∧
      (∀ a, C.In a → tf.mem[a]? = some (s'.m a).toBitVec) := by
    intro s' xs hh
    obtain ⟨t', rt, hR'⟩ := sim_star hC xs hR0
    obtain ⟨tf, rf, cf, pcf, xf, mf⟩ := sim_halt hC hR' hh
    refine ⟨tf, runs_snoc rt (step_of_retires rf), ?_, fun address hO hW => ?_, ?_, fun a ha => ?_⟩
    · simp only [riscvObserve, pcf, Option.map_some, Option.getD_some]
      apply UInt64.toNat_inj.mp; simp [C]
    · simp only [riscvObserve]; unfold Outside at hO hW; dsimp only at hO hW
      rw [mf, hR'.frame address.toNat (by simp only [C]; omega) (by simp only [C]; omega)]
    · simp only [riscvObserve, riscvRegister, cf.x10, Option.map_some, Option.getD_some, xf 10]
      rw [hR'.x 10]; rfl
    · rw [mf]; exact hR'.mem a ha
  have hW8 := workAligned
  by_cases hfit : call.workAddress.toNat + 8 * depth p ≤ (call.workAddress.toNat + call.workLength) / 8 * 8
  · obtain ⟨s', xs, hh, hm, h10', h1'⟩ := genR_ok hI hsc hd hfit
    obtain ⟨tf, hr, hpcf, hfr, hx10, hmem⟩ := finish s' xs hh
    refine ⟨tf, hr, hpcf, hfr, .inl ⟨by omega, ?_, ?_⟩⟩
    · have e10 : s0.get 10 = BitVec.ofNat 64 call.inputAddress.toNat := (s0get 10).trans g10
      rw [hx10, h10', e10]
      intro e
      have := congrArg UInt64.toNat e
      have h2 : oomFlag.toNat = 2 ^ 64 - 1 := rfl
      simp only [UInt64.toNat_ofBitVec, BitVec.toNat_ofNat] at this
      omega
    · refine (readMemory_riscv tf _ (by omega)).2 ?_
      apply List.ext_getElem (by simp [bytesAt, leN_length])
      intro i h1 h2
      simp only [bytesAt, List.length_map, List.length_range] at h1
      simp only [bytesAt, List.getElem_map, List.getElem_range]
      rw [hmem _ (.inr (.inl ⟨by simp only [C]; omega, by simp only [C]; omega⟩)),
        hm _ (by omega) (by omega)]
      have := leN_get 8 (den p.2 args.reverse).toNat i h1
      rw [List.getElem?_eq_getElem (by rw [leN_length]; exact h1)] at this
      rw [Option.some.inj this, byteOf_eq, show call.outputAddress.toNat + i - call.outputAddress.toNat = i by omega]; rfl
  · obtain ⟨s', xs, hh, h10', h1'⟩ := genR_oom hI hsc hd (by omega)
    obtain ⟨tf, hr, hpcf, hfr, hx10, -⟩ := finish s' xs hh
    refine ⟨tf, hr, hpcf, hfr, .inr ⟨by omega, ?_⟩⟩
    rw [hx10, h10']; rfl

/-- **L2, what happens** (`CompileRuns`): the stack code returns to the caller, changes nothing outside the output and
work blocks, and the status register holds `oomFlag` exactly when the work block is smaller than `8 · depth p`. -/
theorem nano_stack_runs : CompileRuns riscv nanoCompileA := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits
  obtain ⟨finishState, hruns, hpc, hframe, hcase⟩ := stack_run compiles (computes argument) startsRight outputFits
  refine ⟨finishState, hruns, hpc, hframe, ?_⟩
  unfold OutOfMemory
  rcases hcase with ⟨hle, hne, -⟩ | ⟨hlt, heq⟩
  · exact ⟨fun h => absurd h hne, fun h => absurd h (Nat.not_lt.2 hle)⟩
  · exact ⟨fun _ => hlt, fun _ => heq⟩

/-- **L2, what comes out** (`CompileCorrect`): with `memoryNeeded` bytes of work the stack code returns with the
program's result (`Prog.eval` on the argument words) in the output block and no flag. -/
theorem nano_stack_correct : CompileCorrect riscv nanoCompileA := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits enoughMemory
  obtain ⟨finishState, hruns, hpc, hframe, hcase⟩ := stack_run compiles (computes argument) startsRight outputFits
  rcases hcase with ⟨-, hne, hread⟩ | ⟨hlt, -⟩
  · exact ⟨finishState, hruns, hpc, hne, hread⟩
  · exact absurd enoughMemory (Nat.not_le.2 hlt)

end Nano
