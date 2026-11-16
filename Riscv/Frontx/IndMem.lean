/- The inductive path (`Compiler/Ind.lean`, NOTES §17/§21) with run-time memory: `CompileCorrect riscv compile` and
`CompileRuns riscv compile` (`Compiler/AllocSpec.lean`) for the compiler `compile : IndProg → Option CompiledA`.

* `IndProg`: an inductive-path program (shapes, the functions `pg :: hs`, the second input, the word argument,
  the output format); its meaning `IndProg.run` reads the input as the byte format of its values (`inBytesA`)
  and gives the output bytes (`Kd.out`) of the Lean semantics `Pg.sem`.
* `compile`: the program `indProgM` (unchanged), compiled with the run-time checks (`memCode`), cells of 8 bytes,
  and the events of its source run (`TExec`, from the canonical start: the input, a zero output block, the
  program's globals zero): the entry stub's two cells, then the heap growth and the frames of the run.
* `memoryNeeded_le`: the old bound (`Ind.spaceA … cellsSup`) bounds `memoryNeeded`, so the old theorems'
  space hypothesis implies the new one. -/
import Riscv.Back.MemTop
import Riscv.Frontx.Ind

set_option linter.unusedVariables false

namespace Proven.Frontx.IndMem
open Proven Proven.Mach Proven.Mach.Ind Proven.Mach.Riscv Proven.Top Proven.Top.Alloc

/-- an inductive-path program -/
structure IndProg where
  sh : Shape
  shO : Shape
  rk : Kd
  pg : Pg rk
  hs : List (Σ k : Kd, Pg k)
  bi : BIn
  ain : Bool
  a0 : BitVec 64
  nb : Nat
  nl : Nat

/-- the canonical start of the source run: the input, a zero output block of `m` bytes, globals zero but the
input length -/
def canon (input : List UInt8) (m : Nat) : Mach.BState :=
  ⟨stubEnv fun i => if i = 1 then BitVec.ofNat 64 input.length else 0,
    [input.map (·.toBitVec), List.replicate m 0], [[]]⟩

namespace IndProg
variable (p : IndProg)

/-- the program with calls -/
def P : Prog := indProgM p.sh p.shO p.pg p.hs p.bi p.ain p.a0 p.nb p.nl

/-- the values an input may encode: well-formed trees (and the word) -/
def Valid (x : C × C × BitVec 64) : Prop := x.1.wf p.sh ∧ (p.bi = .inp → x.2.1.wf p.sh)

def bytes (x : C × C × BitVec 64) : List UInt8 := inBytesA p.sh p.bi p.ain x.1 x.2.1 x.2.2

def out (x : C × C × BitVec 64) : List UInt8 :=
  Kd.out p.shO p.nb p.rk (p.pg.sem x.1 (if p.ain then x.2.2 else p.a0) (p.bi.val x.2.1))

/-- **the meaning**: the output of the values the input encodes -/
noncomputable def run (input : List UInt8) : Option (List UInt8) :=
  open Classical in if h : ∃ x, p.Valid x ∧ input = p.bytes x then some (p.out (Classical.choose h)) else none


/-- **the memory events**: the entry stub's two cells, then those of the source run from the canonical start -/
noncomputable def events (input : List UInt8) : List MemEvent :=
  open Classical in
  if h : ∃ E σ', TExec p.P (.call 1 0 []) (canon input ((p.run input).getD []).length) E σ' then
    Classical.choose h ++ [.alloc 2]
  else [.alloc 2]

/-- the conditions the compiler checks (the last: inputs up to `2 ^ 20` bytes allocate fewer than `2 ^ 50` cells,
so the source run's pointers fit 64 bits; one function with `M` cells per node: `al_le`) -/
def Good : Prop :=
  p.sh.length < 255 ∧ p.shO.length < 255 ∧ 16 ≤ p.nl ∧ Chain (⟨p.rk, p.pg⟩ :: p.hs) ∧
    okL (⟨p.rk, p.pg⟩ :: p.hs) = true ∧ (∀ t, p.bi = .ctor t → t < 256) ∧ p.nb ≤ 8 ∧ WfMem p.P 1 0 ∧
    progClean p.P = true ∧
    ∀ x, p.Valid x → (p.bytes x).length ≤ 2 ^ 20 → p.pg.al x.1 (if p.ain then x.2.2 else p.a0) (p.bi.val x.2.1) < 2 ^ 50

end IndProg

noncomputable instance : Program IndProg := ⟨IndProg.run⟩

/-- **the compiler**: the inductive-path program with run-time memory checks -/
noncomputable def compile (p : IndProg) : Option CompiledA :=
  open Classical in if p.Good then some ⟨wordBytes (memCode p.P 1 0), 8, p.events⟩ else none

theorem compile_inv {p : IndProg} {c : CompiledA} (h : compile p = some c) :
    p.Good ∧ c = ⟨wordBytes (memCode p.P 1 0), 8, p.events⟩ := by
  unfold compile at h
  split at h
  · exact ⟨by assumption, (Option.some.inj h).symm⟩
  · exact nomatch h

theorem res_clean : (!unread.contains 1) = true := by decide

/-- the source run from any globals and output block: a `TExec` run with the output and a bound on its cells -/
theorem run_ok {p : IndProg} (hg : p.Good) {x : C × C × BitVec 64} (hv : p.Valid x) (hI : (p.bytes x).length ≤ 2 ^ 20)
    (env : Mach.BEnv) (O : List (BitVec 8)) (hO : (p.out x).length ≤ O.length) (hO' : O.length < 2 ^ 60) :
    ∃ E σ', TExec p.P (.call 1 0 []) ⟨stubEnv env, [(p.bytes x).map (·.toBitVec), O], [[]]⟩ E σ' ∧
      σ'.heap = [(p.bytes x).map (·.toBitVec), wr O 0 (p.out x)] ∧
      peak (E ++ [.alloc 2]) ≤ 2 + (8 + 4 * (p.bytes x).length +
          4 * p.pg.al x.1 (if p.ain then x.2.2 else p.a0) (p.bi.val x.2.1)) +
        (56 + 8 * (p.nl + 1) * ((p.bytes x).length + (1 + p.hs.length) * (1 + (8 + 4 * (p.bytes x).length +
          4 * p.pg.al x.1 (if p.ain then x.2.2 else p.a0) (p.bi.val x.2.1))))) / 8 := by
  obtain ⟨hsh, hshO, hnl, hch, hok, hbi, hnb, hwf, hcl, hal⟩ := hg
  have hal' := hal x hv hI
  generalize hN : 8 + 4 * (p.bytes x).length + 4 * p.pg.al x.1 (if p.ain then x.2.2 else p.a0) (p.bi.val x.2.1) = N
  have hNs : N < 2 ^ 60 := by omega
  obtain ⟨σb, hx, hh, -⟩ := ind_okM p.sh p.shO p.pg p.hs p.bi p.ain p.a0 p.nb p.nl hsh hshO hnl hch hok hbi hnb
    x.1 x.2.1 x.2.2 hv.1 hv.2 O (List.replicate N 0) (stubEnv env) 1 (by decide) (by unfold IndProg.bytes at hI; omega)
    (by simpa using hNs) (by rw [List.length_replicate]; unfold IndProg.bytes at hN; omega) hO' hO
  have t : Tr ⟨stubEnv env, [(p.bytes x).map (·.toBitVec), O], [List.replicate N 0]⟩
      ⟨stubEnv env, [(p.bytes x).map (·.toBitVec), O], [[]]⟩ (List.replicate N 0) [] :=
    ⟨rfl, rfl, rfl, fun _ _ => rfl, by simp [stubEnv, Mach.BEnv.set, hvar], by simp, fun j hj => by
      rw [List.getElem?_replicate]; simp at hj; simp [hj]⟩
  obtain ⟨E, σs, Wb', Ws', hx', t', -, hb⟩ := texec_of_cexec hcl hx (by simp [CStmt.clean, unread]) t
  refine ⟨E, σs, hx', by rw [t'.heap]; exact hh, ?_⟩
  have hpk := (hb 2).2
  have hl := t'.le
  have hwl : Wb'.length = N := by
    have e := cexec_wlen hx
    rw [t'.wb] at e; simp at e; exact e
  simp only [List.length_nil, Nat.sub_zero, List.length_replicate] at hpk
  simp only [IndProg.bytes] at hpk ⊢
  omega

theorem run_some {p : IndProg} {input out : List UInt8} (h : p.run input = some out) :
    ∃ x, p.Valid x ∧ input = p.bytes x ∧ out = p.out x := by
  unfold IndProg.run at h
  split at h
  · next hx => exact ⟨_, (Classical.choose_spec hx).1, (Classical.choose_spec hx).2, (Option.some.inj h).symm⟩
  · exact nomatch h

/-- the canonical run and any run from the same input have the same events -/
theorem events_eq {p : IndProg} (hg : p.Good) {x : C × C × BitVec 64} (hv : p.Valid x)
    (hI : (p.bytes x).length ≤ 2 ^ 20) (hrun : p.run (p.bytes x) = some (p.out x)) (hout : (p.out x).length < 2 ^ 60)
    {env : Mach.BEnv} (he1 : env 1 = BitVec.ofNat 64 (p.bytes x).length) (he8 : ∀ i, 8 ≤ i → env i = 0)
    {O : List (BitVec 8)} {E : List MemEvent} {σ' : Mach.BState}
    (hx : TExec p.P (.call 1 0 []) ⟨stubEnv env, [(p.bytes x).map (·.toBitVec), O], [[]]⟩ E σ') :
    p.events (p.bytes x) = E ++ [.alloc 2] := by
  have hex : ∃ E σ', TExec p.P (.call 1 0 []) (canon (p.bytes x) ((p.run (p.bytes x)).getD []).length) E σ' := by
    rw [hrun]
    obtain ⟨E', σ'', hx', -⟩ := run_ok hg hv hI (fun i => if i = 1 then BitVec.ofNat 64 (p.bytes x).length else 0)
      (List.replicate (p.out x).length 0) (by simp) (by simpa using hout)
    exact ⟨E', σ'', hx'⟩
  unfold IndProg.events
  rw [dif_pos hex]
  obtain ⟨σc, hc⟩ := Classical.choose_spec hex
  have q : Eqv (canon (p.bytes x) ((p.run (p.bytes x)).getD []).length)
      ⟨stubEnv env, [(p.bytes x).map (·.toBitVec), O], [[]]⟩ := by
    refine ⟨fun i hi => ?_, by simp [canon, stubEnv, Mach.BEnv.set, hvar], by simp [canon], rfl⟩
    simp only [canon, stubEnv, Mach.BEnv.set, hvar]
    by_cases h1 : i = 1
    · subst h1; simp [he1]
    · have : i = 4 ∨ i = 5 ∨ i = 6 ∨ 8 ≤ i := by simp [unread] at hi; omega
      rcases this with rfl | rfl | rfl | h8
      · simp
      · simp
      · simp
      · have : i ≠ 7 ∧ i ≠ 6 ∧ i ≠ 5 ∧ i ≠ 4 := by omega
        simp [this, h1, he8 i h8]
  have := (texec_det hg.2.2.2.2.2.2.2.2.1 hc (by simp [CStmt.clean, unread]) hx q).1
  rw [this]


end Proven.Frontx.IndMem

namespace Proven.Frontx.IndMem
open Proven Proven.Mach Proven.Mach.Ind Proven.Mach.Riscv Proven.Top Proven.Top.Alloc

theorem readMemory_take {st : MachineState} {a : UInt64} {n k : Nat} {l : List UInt8}
    (h : readMemory st a n = some l) (hk : k ≤ n) : readMemory st a k = some (l.take k) := by
  unfold readMemory at h ⊢
  rw [mapM_some] at h ⊢
  have e : List.range k = (List.range n).take k := by rw [List.take_range, Nat.min_eq_left hk]
  rw [e, List.map_take, h, ← List.map_take]

/-- the machine run of a compiled program: its source run (from the machine's output block and globals), the
events of `compile`, the machine's facts -/
theorem machine_run {p : IndProg} {compiled : CompiledA} {α β : Type} {f : α → β} {encodeInput : α → List UInt8}
    {encodeOutput : β → List UInt8} {argument : α} {startState : riscv.State} {call : Call}
    (compiles : compile p = some compiled) (computes : Computes p f encodeInput encodeOutput)
    (startsRight : StartCorrect riscv startState call compiled.code (encodeInput argument))
    (outputFits : (encodeOutput (f argument)).length ≤ call.outputLength) :
    ∃ (σ' : Mach.BState) (out0 : List (BitVec 8)) (finishState : riscv.State),
      σ'.heap = [(encodeInput argument).map (·.toBitVec), wr out0 0 (encodeOutput (f argument))] ∧
      out0.length = call.outputLength ∧
      Runs riscv startState finishState ∧ (riscv.observe finishState).programCounter = call.returnAddress ∧
      (∀ address, Outside address (call.outputAddress, call.outputLength) →
        Outside address (call.workAddress, call.workLength) →
        (riscv.observe finishState).memory address = (riscv.observe startState).memory address) ∧
      ((memoryNeeded compiled (encodeInput argument) ≤ call.workLength ∧
          (riscv.observe finishState).register riscv.mapping.status ≠ oomFlag ∧
          readMemory (riscv.observe finishState) call.outputAddress call.outputLength =
            some ((σ'.heap[1]?.getD []).map UInt8.ofBitVec)) ∨
        (call.workLength < memoryNeeded compiled (encodeInput argument) ∧
          (riscv.observe finishState).register riscv.mapping.status = oomFlag)) := by
  obtain ⟨hg, rfl⟩ := compile_inv compiles
  have hrun := computes argument
  obtain ⟨x, hv, hin, hout⟩ := run_some hrun
  have hstart := startsRight
  obtain ⟨env, out0, he1, he8, hl0, mach⟩ := memSpec hg.2.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2.2.1 res_clean hstart
  have hsmall := hstart.inputSmall
  have hram := hstart.inRam
  simp only [Call.blocks, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hram
  have hol : call.outputLength < 2 ^ 32 := by
    obtain ⟨h1, h2⟩ := hram.2.1
    have e : riscv.ramEnd = 0x100000000 := rfl
    have e' : riscv.ramStart = 0x80000000 := rfl
    rw [e] at h2; rw [e'] at h1
    have := call.outputAddress.toNat_lt
    omega
  rw [hin] at hsmall he1 mach hrun
  rw [hout] at outputFits hrun ⊢
  have hO : (p.out x).length ≤ out0.length := by omega
  obtain ⟨E, σ', hx, hh, -⟩ := run_ok hg hv hsmall env out0 hO (by omega)
  have hev := events_eq hg hv hsmall hrun (by omega) he1 he8 hx
  obtain ⟨finishState, hruns, hpc, hframe, hcase⟩ := mach hx
  refine ⟨σ', out0, finishState, by rw [hh, hin], hl0, hruns, hpc, hframe, ?_⟩
  have hmn : memoryNeeded ⟨wordBytes (memCode p.P 1 0), 8, p.events⟩ (encodeInput argument) =
      8 * peak (E ++ [.alloc 2]) := by
    show 8 * peak (p.events (encodeInput argument)) = _
    rw [hin, hev]
  rw [hmn]
  exact hcase

/-- **What happens** (`CompileRuns`, `Compiler/AllocSpec.lean`) for the inductive path with run-time memory: the
code returns to the caller, changes nothing outside the output and work blocks, and the status register holds
`oomFlag` exactly when the run's memory (`memoryNeeded`, from its events) exceeds the work block. -/
theorem compile_runs : CompileRuns riscv compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits
  obtain ⟨σ', out0, finishState, -, -, hruns, hpc, hframe, hcase⟩ :=
    machine_run compiles computes startsRight outputFits
  refine ⟨finishState, hruns, hpc, hframe, ?_⟩
  unfold OutOfMemory
  rcases hcase with ⟨hle, hne, -⟩ | ⟨hlt, heq⟩
  · exact ⟨fun h => absurd h hne, fun h => absurd h (Nat.not_lt.2 hle)⟩
  · exact ⟨fun _ => hlt, fun _ => heq⟩

/-- **What comes out** (`CompileCorrect`, `Compiler/AllocSpec.lean`) for the inductive path with run-time memory:
with `memoryNeeded ≤ workLength` the code returns with the right output and no flag. -/
theorem compile_correct : CompileCorrect riscv compile := by
  intro α β program compiled f encodeInput encodeOutput argument startState call compiles computes startsRight
    outputFits enoughMemory
  obtain ⟨σ', out0, finishState, hh, hl0, hruns, hpc, hframe, hcase⟩ :=
    machine_run compiles computes startsRight outputFits
  rcases hcase with ⟨-, hne, hread⟩ | ⟨hlt, -⟩
  · refine ⟨finishState, hruns, hpc, hne, ?_⟩
    have := readMemory_take hread outputFits
    rw [this, hh]
    congr 1
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
    rw [← List.map_take, Proven.Frontx.Ind.wr_take _ _ (by omega), List.map_map]
    exact List.map_id' _
  · exact absurd enoughMemory (Nat.not_le.2 hlt)

/-- **The old bound bounds the new one**: the work space of the inductive-path theorems (`Ind.spaceA` with the
worst-case cell count `cellsSup`, `implements1_indS`) is at least `memoryNeeded`, so their hypothesis
`space ≤ workLength` gives `memoryNeeded ≤ workLength` (`compile_correct`'s hypothesis). -/
theorem memoryNeeded_le {p : IndProg} {c : CompiledA} (hc : compile p = some c) {input o : List UInt8}
    (hrun : p.run input = some o) (hI : input.length ≤ 2 ^ 20) (ho : o.length < 2 ^ 60) :
    memoryNeeded c input ≤
      Proven.Frontx.Ind.spaceA (1 + p.hs.length) p.nl (cellsSup p.sh p.pg p.bi p.ain p.a0) input.length := by
  obtain ⟨hg, rfl⟩ := compile_inv hc
  obtain ⟨x, hv, rfl, rfl⟩ := run_some hrun
  obtain ⟨E, σ', hx, -, hpk⟩ := run_ok hg hv hI (fun i => if i = 1 then BitVec.ofNat 64 (p.bytes x).length else 0)
    (List.replicate (p.out x).length 0) (by simp) (by simpa using ho)
  have hev := events_eq hg hv hI hrun ho (env := fun i => if i = 1 then BitVec.ofNat 64 (p.bytes x).length else 0)
    (by simp) (fun i hi => by simp; omega) hx
  show 8 * peak (p.events (p.bytes x)) ≤ _
  rw [hev]
  have hA := al_le_cellsSup p.sh hg.1 p.pg p.bi p.ain p.a0 x.1 x.2.1 x.2.2 hv.1 hv.2
    (by unfold IndProg.bytes at hI; omega)
  generalize p.pg.al x.1 (if p.ain then x.2.2 else p.a0) (p.bi.val x.2.1) = al at hpk hA
  generalize hn : (p.bytes x).length = n at hpk hA ⊢
  unfold IndProg.bytes at hn
  rw [hn] at hA
  unfold Proven.Frontx.Ind.spaceA Proven.Frontx.Ind.wnA
  generalize cellsSup p.sh p.pg p.bi p.ain p.a0 n = A at hA ⊢
  have h1 : (p.nl + 1) * (n + (1 + p.hs.length) * (1 + (8 + 4 * n + 4 * al))) ≤
      (p.nl + 1) * (n + (1 + p.hs.length) * (1 + (8 + 4 * n + 4 * A))) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _)
  have h2 : 8 * (p.nl + 1) * (n + (1 + p.hs.length) * (1 + (8 + 4 * n + 4 * al))) ≤
      8 * (p.nl + 1) * (n + (1 + p.hs.length) * (1 + (8 + 4 * n + 4 * A))) := by
    rw [Nat.mul_assoc, Nat.mul_assoc]; exact Nat.mul_le_mul_left _ h1
  omega

end Proven.Frontx.IndMem
