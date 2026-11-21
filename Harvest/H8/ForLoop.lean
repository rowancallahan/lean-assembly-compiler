/- Harvest/H8/ForLoop: `for x in e do` with `break`/`continue`/`return` (Lean: `forIn` in `Id`, 4.34.1 Init/Data/List/Control.lean,
Init/Data/Range/Basic.lean) against a nano-style total loop executor. -/
namespace H8

/-- loop body result: nano's `continue`, `break`, `return c` (the three exits of a `for` body) -/
inductive Ex (γ β : Type) | cont (b : β) | brk (b : β) | ret (c : γ)

/-- candidate: run a body over a list; `break` stops with the state, `return` stops with the value, else continue -/
def runL {α γ β} (f : α → β → Ex γ β) : List α → β → Sum γ β
  | [], b => .inr b
  | a :: l, b => match f a b with
    | .cont b' => runL f l b'
    | .brk b' => .inr b'
    | .ret c => .inl c

/-- Lean's encoding of the same body (what `for … do … return …` elaborates to): `ForInStep` over state `MProd (Option γ) β` -/
def leanStep {α γ β} (f : α → β → Ex γ β) (a : α) (r : MProd (Option γ) β) : Id (ForInStep (MProd (Option γ) β)) :=
  match f a r.2 with
  | .cont b' => pure (.yield ⟨none, b'⟩)
  | .brk b' => pure (.done ⟨none, b'⟩)
  | .ret c => pure (.done ⟨some c, r.2⟩)

def decode {γ β} (r : MProd (Option γ) β) : Sum γ β := match r.1 with | some c => .inl c | none => .inr r.2

/-- `for a in xs do (break | continue | return)` over a list: Lean's `forIn` = candidate `runL` -/
theorem forIn_list_eq {α γ β} (f : α → β → Ex γ β) (xs : List α) (b : β) :
    decode (Id.run (forIn xs (⟨none, b⟩ : MProd (Option γ) β) (leanStep f))) = runL f xs b := by
  induction xs generalizing b with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forIn_cons, runL]
    cases h : f a b with
    | cont b' => simp only [leanStep, h]; exact ih b'
    | brk b' => simp only [leanStep, h]; rfl
    | ret c => simp only [leanStep, h]; rfl

/-- same for `for i in [lo:hi]` (step 1): the list is `lo, …, hi-1` (`Std.Legacy.Range`, `forIn_eq_forIn_range'`) -/
theorem forIn_range_eq {γ β} (f : Nat → β → Ex γ β) (lo hi : Nat) (b : β) :
    decode (Id.run (forIn [lo:hi] (⟨none, b⟩ : MProd (Option γ) β) (leanStep f)))
      = runL f (List.range' lo (hi - lo)) b := by
  rw [← forIn_list_eq, Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size]

/-- plain fold form (no break/return): `for a in xs do x := g a x` is `List.foldl` -/
theorem for_fold_lean {α β} (xs : List α) (b : β) (g : α → β → β) :
    (Id.run do
      let mut x := b
      for a in xs do x := g a x
      return x) = xs.foldl (fun x a => g a x) b := by
  induction xs generalizing b with
  | nil => rfl
  | cons a l ih => simp_all [Id.run]

end H8
