import Nano.V2.Sem
/- nano v2 small backend: the LOOP-HEADER INVARIANT (round 2 §6) for structured stack code, generically: an
invariant `Inv n s` at HEAD (n = the fuel), the test exposes the fuel in t0, the zero branch and one body run
(after the decrement) re-establish `Inv m` at the backward jump or produce the loop's outcome.  By induction on the
fuel; used by the expression contract for `Ex.loop` (and by the epilogue's copy loop). -/
namespace Nano.V2B

/-- what the zero branch may end in -/
def ZOut (Q : Res → Prop) : Res → Prop
  | .ok s => Q (.ok s)
  | .jmp .exit s => Q (.ok s)
  | .jmp .head _ => False
  | .jmp t s => (t = .oom ∨ t = .cap) ∧ Q (.jmp t s)

/-- what one body run may end in: the backward jump (re-establishing the invariant at fuel `m`), the exit, an abort -/
def BOut (Inv : St → Prop) (Q : Res → Prop) : Res → Prop
  | .ok _ => False
  | .jmp .head s => Inv s
  | .jmp .exit s => Q (.ok s)
  | .jmp t s => (t = .oom ∨ t = .cap) ∧ Q (.jmp t s)

theorem loop_ok {c : Cfg} {test dec : List I} {z body : SC} (Inv : Nat → St → Prop) (Aft : Nat → St → Prop)
    (Q : Res → Prop)
    (hT : ∀ n s, Inv n s → ∃ s1, runL c test s = some s1 ∧ (s1.get 5 = 0 ↔ n = 0) ∧ Aft n s1)
    (hZ : ∀ s1, Aft 0 s1 → ∃ r, SC.Ex c z s1 r ∧ ZOut Q r)
    (hB : ∀ m s1, Aft (m + 1) s1 → ∃ s2, runL c dec s1 = some s2 ∧ ∃ r, SC.Ex c body s2 r ∧ BOut (Inv m) Q r) :
    ∀ n s, Inv n s → ∃ r, SC.Ex c (.loop test dec z body) s r ∧ Q r := by
  intro n
  induction n with
  | zero =>
    intro s hI
    obtain ⟨s1, e1, h0, hA⟩ := hT 0 s hI
    have g0 : s1.get 5 = 0 := h0.2 rfl
    obtain ⟨r, ez, hq⟩ := hZ s1 hA
    match r, ez, hq with
    | .ok s2, ez, hq => exact ⟨_, .loopZ e1 g0 ez, hq⟩
    | .jmp .exit s2, ez, hq => exact ⟨_, .loopZX e1 g0 ez, hq⟩
    | .jmp .oom s2, ez, hq => exact ⟨_, .loopZA e1 g0 ez (.inl rfl), hq.2⟩
    | .jmp .cap s2, ez, hq => exact ⟨_, .loopZA e1 g0 ez (.inr rfl), hq.2⟩
  | succ m ih =>
    intro s hI
    obtain ⟨s1, e1, h0, hA⟩ := hT (m + 1) s hI
    have g0 : s1.get 5 ≠ 0 := fun h => by have := h0.1 h; omega
    obtain ⟨s2, e2, r, eb, hq⟩ := hB m s1 hA
    match r, eb, hq with
    | .jmp .head s3, eb, hq =>
      obtain ⟨r', e', q'⟩ := ih s3 hq
      exact ⟨r', .loopH e1 g0 e2 eb e', q'⟩
    | .jmp .exit s3, eb, hq => exact ⟨_, .loopX e1 g0 e2 eb, hq⟩
    | .jmp .oom s3, eb, hq => exact ⟨_, .loopA e1 g0 e2 eb (.inl rfl), hq.2⟩
    | .jmp .cap s3, eb, hq => exact ⟨_, .loopA e1 g0 e2 eb (.inr rfl), hq.2⟩

end Nano.V2B
