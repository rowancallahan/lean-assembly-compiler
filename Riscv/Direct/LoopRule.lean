/- Generic reasoning rules on `runsTo` (pure Lean, no model unfolding): monotonicity, sequencing, and a
loop rule with a user-supplied invariant and `Nat` measure. -/
import Riscv.Direct.Compiler

namespace Proven

theorem runsTo_of {s : St} {P : St → Prop} (h : P s) : runsTo s P := ⟨0, s, rfl, h⟩

theorem runsTo_mono {s : St} {P Q : St → Prop} (h : runsTo s P) (hpq : ∀ s, P s → Q s) : runsTo s Q :=
  let ⟨n, s', hs, hp⟩ := h; ⟨n, s', hs, hpq s' hp⟩

/-- sequencing -/
theorem runsTo_trans {s : St} {P Q : St → Prop} (h : runsTo s P) (hq : ∀ s', P s' → runsTo s' Q) :
    runsTo s Q :=
  let ⟨_, s', hs, hp⟩ := h
  let ⟨_, s'', hs', hq'⟩ := hq s' hp
  ⟨_, s'', Steps.trans hs hs', hq'⟩

theorem runsTo_of_reach {s s' : St} {P : St → Prop} (h : Reach s s') (hp : P s') : runsTo s P :=
  let ⟨n, hs⟩ := h; ⟨n, s', hs, hp⟩

/-- **Loop rule.**  If from every state satisfying `Inv` the machine runs either to a state satisfying
`Post` (exit), or back to a state satisfying `Inv` with a strictly smaller measure (iterate), then from
every `Inv` state it runs to `Post`. -/
theorem runsTo_loop {Inv Post : St → Prop} (μ : St → Nat)
    (body : ∀ s, Inv s → runsTo s fun s' => Post s' ∨ (Inv s' ∧ μ s' < μ s)) :
    ∀ s, Inv s → runsTo s Post := by
  intro s
  induction h : μ s using Nat.strongRecOn generalizing s with
  | ind n ih =>
    intro hi
    refine runsTo_trans (body s hi) fun s' hs' => ?_
    rcases hs' with hp | ⟨hi', hlt⟩
    · exact runsTo_of hp
    · exact ih _ (h ▸ hlt) s' rfl hi'

/-- the loop rule with explicit head and exit PCs (`Inv` holds only at the head) -/
theorem runsTo_while {Inv Post : St → Prop} (head exit : BitVec 64) (μ : St → Nat)
    (_hhead : ∀ s, Inv s → s.regs.get? .PC = some head)
    (body : ∀ s, Inv s → runsTo s fun s' =>
      (s'.regs.get? .PC = some exit ∧ Post s') ∨ (Inv s' ∧ μ s' < μ s)) :
    ∀ s, Inv s → runsTo s fun s' => s'.regs.get? .PC = some exit ∧ Post s' :=
  runsTo_loop μ body

end Proven
