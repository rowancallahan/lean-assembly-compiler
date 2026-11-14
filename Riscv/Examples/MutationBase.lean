/- Mutation testing, part 1: generic tools to show that the specification REJECTS wrong code.

* `retires_det`, `steps_det`: the model's step relation is deterministic (`Retires` ends with
  `try_step 0 false s = .ok false s'`, a function of `s`).
* `park`: the word `jal x0, 0` (an infinite self-loop) placed at the return address `ra`.  Once the PC
  reaches `ra`, every later state has the same memory and the same `x` registers.
* `runsTo_unique`: if `s` runs to a `P`-state and to a `Q`-state, both parked at `ra`, then the two states have
  the same memory and `x` registers.  So two theorems "the code at `pc` returns with output `u`" and "... with
  output `v`" about the same initial state force `u = v`: one concrete input on which the mutant's output differs
  from the specified one refutes the specification for the mutant.
* `AStmt.run`: a fuel interpreter for the byte-array language with `run_sound` (gives `AExec` derivations
  for concrete runs by `decide +kernel`). -/
import Riscv.Examples.VacuityBase
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

set_option linter.unusedVariables false

namespace Proven.Vacuity

/-! ## Determinism -/

theorem retires_det {s a b : St} (ha : Retires s a) (hb : Retires s b) : a = b := by
  have e := ha.2.symm.trans hb.2
  injection e

theorem steps_det : ∀ {n : Nat} {s a b : St}, Steps n s a → Steps n s b → a = b
  | 0, _, _, _, ha, hb => by simp only [Steps] at ha hb; rw [ha, hb]
  | n + 1, _, _, _, ⟨u, hu, ha⟩, ⟨v, hv, hb⟩ => by
    cases retires_det hu hv; exact steps_det ha hb

theorem steps_split : ∀ {n k : Nat} {s c : St}, Steps (n + k) s c → ∃ u, Steps n s u ∧ Steps k u c
  | 0, k, s, c, h => ⟨s, rfl, by simpa using h⟩
  | n + 1, k, s, c, h => by
    rw [show n + 1 + k = (n + k) + 1 by omega] at h
    obtain ⟨u, hu, hk⟩ := h
    obtain ⟨v, hv, hvk⟩ := steps_split hk
    exact ⟨v, ⟨u, hu, hv⟩, hvk⟩

/-! ## Parking at the return address -/

/-- `jal x0, 0`: jump to itself -/
def park : BitVec 32 := wJ 0 0

theorem park_eq : park = 0x0000006f#32 := by decide

theorem joff_zero : joff 0 = 0 := by decide

/-- from a parked state, every later state has the same memory, `x` registers, PC, and `Cfg` -/
theorem parked_stays {ra : BitVec 64} (hok : pcOK ra) :
    ∀ (k : Nat) {u c : St}, Cfg u → u.regs.get? .PC = some ra → instrAt u ra park → Steps k u c →
      c.mem = u.mem ∧ (∀ j, getX c j = getX u j)
  | 0, u, c, h, hpc, hi, hs => by simp only [Steps] at hs; subst hs; exact ⟨rfl, fun _ => rfl⟩
  | k + 1, u, c, h, hpc, hi, ⟨u₁, hr, hs⟩ => by
    obtain ⟨s', hn⟩ := step_jal_0 h hpc hok 0 hi
    have e := retires_det hr hn.ret; subst e
    have hpc' : u₁.regs.get? .PC = some ra := by rw [hn.pc, joff_zero]; simp
    have hi' : instrAt u₁ ra park := by unfold instrAt at hi ⊢; rw [hn.mem]; exact hi
    obtain ⟨m, x⟩ := parked_stays hok k hn.cfg hpc' hi' hs
    refine ⟨m.trans hn.mem, fun j => (x j).trans ?_⟩
    rw [hn.x j]; simp

/-- the final states of two runs from `s`, both parked at `ra`, agree on memory and `x` registers -/
theorem runsTo_unique {s : St} {P Q : St → Prop} {ra : BitVec 64} (hok : pcOK ra)
    (hP : runsTo s P) (hQ : runsTo s Q)
    (hP' : ∀ t, P t → Cfg t ∧ t.regs.get? .PC = some ra ∧ instrAt t ra park)
    (hQ' : ∀ t, Q t → Cfg t ∧ t.regs.get? .PC = some ra ∧ instrAt t ra park) :
    ∃ t₁ t₂, P t₁ ∧ Q t₂ ∧ t₁.mem = t₂.mem ∧ ∀ j, getX t₁ j = getX t₂ j := by
  obtain ⟨n₁, t₁, s₁, p₁⟩ := hP
  obtain ⟨n₂, t₂, s₂, p₂⟩ := hQ
  refine ⟨t₁, t₂, p₁, p₂, ?_⟩
  rcases Nat.le_total n₁ n₂ with hle | hle
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    obtain ⟨u, hu, hk⟩ := steps_split s₂
    cases steps_det hu s₁
    obtain ⟨c₁, c₂, c₃⟩ := hP' _ p₁
    obtain ⟨m, x⟩ := parked_stays hok k c₁ c₂ c₃ hk
    exact ⟨m.symm, fun j => (x j).symm⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    obtain ⟨u, hu, hk⟩ := steps_split s₁
    cases steps_det hu s₂
    obtain ⟨c₁, c₂, c₃⟩ := hQ' _ p₂
    exact parked_stays hok k c₁ c₂ c₃ hk

theorem instrAt_of_mem {s t : St} {a : BitVec 64} {w : BitVec 32}
    (hm : ∀ i < 4, t.mem[a.toNat + i]? = s.mem[a.toNat + i]?) (h : instrAt s a w) : instrAt t a w :=
  ⟨by have := hm 0 (by omega); simp at this; rw [this]; exact h.1, by rw [hm 1 (by omega)]; exact h.2.1,
    by rw [hm 2 (by omega)]; exact h.2.2.1, by rw [hm 3 (by omega)]; exact h.2.2.2⟩

/-! ## An interpreter for `AStmt` (for concrete source runs of mutants) -/

def AStmt.run : Nat → AStmt → AState → Option AState
  | 0, _, _ => none
  | _ + 1, .assign v e, σ => some ⟨σ.env.set v (e.denote σ.env), σ.heap⟩
  | _ + 1, .load v b i, σ =>
    if hb : b < σ.heap.length then
      if hi : (i.denote σ.env).toNat < σ.heap[b].length then
        some ⟨σ.env.set v (σ.heap[b][(i.denote σ.env).toNat].setWidth 64), σ.heap⟩
      else none
    else none
  | _ + 1, .store b i e, σ =>
    if hb : b < σ.heap.length then
      if hi : (i.denote σ.env).toNat < σ.heap[b].length then
        some ⟨σ.env, σ.heap.set b (σ.heap[b].set (i.denote σ.env).toNat ((e.denote σ.env).setWidth 8))⟩
      else none
    else none
  | n + 1, .seq p q, σ => (AStmt.run n p σ).bind (AStmt.run n q)
  | n + 1, .loop c b, σ =>
    if c.denote σ.env = 0 then some σ else (AStmt.run n b σ).bind (AStmt.run n (.loop c b))

theorem AStmt.run_sound : ∀ (n : Nat) (p : AStmt) (σ σ' : AState), AStmt.run n p σ = some σ' → AExec p σ σ'
  | 0, _, _, _, h => by simp [AStmt.run] at h
  | n + 1, .assign v e, σ, σ', h => by simp only [AStmt.run, Option.some.injEq] at h; subst h; exact .assign
  | n + 1, .load v b i, σ, σ', h => by
    simp only [AStmt.run] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact .load ‹_› ‹_›
      · simp at h
    · simp at h
  | n + 1, .store b i e, σ, σ', h => by
    simp only [AStmt.run] at h
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; exact .store ‹_› ‹_›
      · simp at h
    · simp at h
  | n + 1, .seq p q, σ, σ', h => by
    simp only [AStmt.run, Option.bind_eq_some_iff] at h
    obtain ⟨σ₁, h1, h2⟩ := h
    exact .seq (run_sound n p σ σ₁ h1) (run_sound n q σ₁ σ' h2)
  | n + 1, .loop c b, σ, σ', h => by
    simp only [AStmt.run] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact .loopF ‹_›
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨σ₁, h1, h2⟩ := h
      exact .loopT ‹_› (run_sound n b σ σ₁ h1) (run_sound n (.loop c b) σ₁ σ' h2)

/-- a concrete run that ends with heap `H` gives an `AExec` derivation ending with heap `H` -/
theorem AStmt.exec_of_run {n : Nat} {p : AStmt} {σ : AState} {H : Heap}
    (h : (AStmt.run n p σ).map AState.heap = some H) : ∃ σ', AExec p σ σ' ∧ σ'.heap = H := by
  cases e : AStmt.run n p σ with
  | none => rw [e] at h; simp at h
  | some σ' => rw [e] at h; simp at h; exact ⟨σ', AStmt.run_sound n p σ σ' e, h⟩

end Proven.Vacuity
