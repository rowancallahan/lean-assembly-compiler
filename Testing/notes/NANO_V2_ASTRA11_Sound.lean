namespace NanoSound
variable {S T A P B Q : Type}

theorem collect_sound
    (run : Nat → Q → Option T) (inv : Q → Prop) (good : T → Prop)
    (zero : ∀ q t, inv q → run 0 q = some t → good t)
    (step : ∀ n q t, inv q → run (n+1) q = some t →
      good t ∨ ∃ q', inv q' ∧ run n q' = some t)
    (n : Nat) (q : Q) (t : T) (hi : inv q) (hr : run n q = some t) :
    good t := by
  induction n generalizing q with
  | zero => exact zero q t hi hr
  | succ n ih =>
    rcases step n q t hi hr with done | ⟨q', hi', hr'⟩
    · exact done
    · exact ih q' hi' hr'

theorem lexer_ok
    (run : Nat → Q → Option T) (init : S → Q) (fuel : S → Nat)
    (Inv : S → Q → Prop) (Lexes : S → T → Prop)
    (start : ∀ s, Inv s (init s))
    (zero : ∀ s q t, Inv s q → run 0 q = some t → Lexes s t)
    (step : ∀ s n q t, Inv s q → run (n+1) q = some t →
      Lexes s t ∨ ∃ q', Inv s q' ∧ run n q' = some t)
    (s : S) (t : T) (h : run (fuel s) (init s) = some t) : Lexes s t :=
  collect_sound run (Inv s) (Lexes s) (zero s) (step s)
    (fuel s) (init s) t (start s) h

theorem compiler_ok
    (lex : S → Option T) (parse : T → Option A) (emit : A → Option B)
    (lexes : S → T → Prop) (rep : A → P → Prop)
    (denotes : S → P → Prop) (implements : B → P → Prop)
    (hl : ∀ s t, lex s = some t → lexes s t)
    (hp : ∀ s t a, lexes s t → parse t = some a →
      ∃ p, rep a p ∧ denotes s p)
    (hg : ∀ a p b, rep a p → emit a = some b → implements b p)
    (s : S) (b : B)
    (h : ((lex s).bind fun t => (parse t).bind emit) = some b) :
    ∃ p, denotes s p ∧ implements b p := by
  cases ht : lex s with
  | none => simp [ht] at h
  | some t =>
    cases ha : parse t with
    | none => simp [ht, ha] at h
    | some a =>
      obtain ⟨p, hr, hd⟩ := hp s t a (hl s t ht) ha
      exact ⟨p, hd, hg a p b hr (by simpa [ht, ha] using h)⟩
end NanoSound
