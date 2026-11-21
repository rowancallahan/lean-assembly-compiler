/- Harvest/H10/Ws: whitespace and comments of Lean 4.34.1's `whitespace` / `finishCommentBlock`
(Lean/Parser/Basic.lean:536-583, both `partial`) against nano's `LexSpec.step` rules.
Lean's code is `partial`, so the "Lean side" is a TOTAL fuel MIRROR transcribed line by line (`fcb`, `lws`); the
mirror<->Lean link is by transcription + the differential runs in README (not a kernel fact).  The nano<->mirror
statements are kernel theorems.  Three nano deviations found and shown (F1, F2): nano accepts what Lean rejects. -/
import Nano.Lexer.Lex2Spec
namespace H10
open LexSpec

abbrev ch (b : UInt8) : Char := Char.ofNat b.toNat
theorem all_bytes {p : UInt8 → Prop} (h : ∀ i : Fin 256, p (UInt8.ofNat i.val)) (b : UInt8) : p b := by
  have := h ⟨b.toNat, b.toNat_lt⟩
  simpa using this

/-- Lean `finishCommentBlock nesting` (Basic.lean:537) with fuel; `none` = "unterminated comment".  A byte scan equals the
`Char` scan: `-` `/` `!` are ASCII and never inside a UTF-8 multi-byte sequence. -/
def fcb : Nat → Nat → List UInt8 → Option (List UInt8)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | f + 1, n, c :: r =>
    if ch c = '-' then
      match r with
      | [] => none
      | d :: r' => if ch d = '/' then (if n = 1 then some r' else fcb f (n - 1) r') else fcb f n r
    else if ch c = '/' then
      match r with
      | [] => none
      | d :: r' => if ch d = '-' then fcb f (n + 1) r' else fcb f n r
    else fcb f n r

/-- Lean `whitespace` (Basic.lean:563) with fuel: `some rest` = stops at `rest` (a token, a doc-comment opener, the end),
`none` = error (tab, lone CR, unterminated comment).  CRLF is normalised to LF before parsing (`mkInputContext`), so a CR
that reaches here is an error. -/
def lws : Nat → List UInt8 → Option (List UInt8)
  | 0, _ => none
  | _ + 1, [] => some []
  | f + 1, c :: r =>
    if ch c = '\t' ∨ ch c = '\r' then none
    else if (ch c).isWhitespace then lws f r
    else if ch c = '-' then
      (match r with
       | d :: r' => if ch d = '-' then lws f (r'.dropWhile fun x => !(ch x == '\n')) else some (c :: r)
       | [] => some (c :: r))
    else if ch c = '/' then
      (match r with
       | d :: r1 =>
         if ch d = '-' then
           (match r1 with
            | x :: r2 => if ch x = '-' ∨ ch x = '!' then some (c :: r) else (fcb (r2.length + 1) 1 r2).bind (lws f)
            | [] => none)
         else some (c :: r)
       | [] => some (c :: r))
    else some (c :: r)

-- ### W1 whitespace characters (refines LeanEquiv `ws_eq_lean`: Lean's `whitespace` REJECTS tab and CR)
/-- the bytes Lean's `whitespace` skips silently are exactly nano's space and newline -/
theorem ws_skip_eq : ∀ c : UInt8, (c == 32 || c == 10) = ((ch c).isWhitespace && ch c != '\t' && ch c != '\r') :=
  all_bytes (by decide +kernel)
/-- tab and CR are errors in Lean (no nano-accepted byte is one) -/
theorem ws_nano_not_tab_cr : ∀ c : UInt8, (c == 32 || c == 10) = true → ch c ≠ '\t' ∧ ch c ≠ '\r' :=
  all_bytes (by decide +kernel)

-- ### W2 `--` line comment: Lean `takeUntilFn (· = '\n')` leaves the newline
theorem line_eq : ∀ r : List UInt8, r.dropWhile (· != 10) = r.dropWhile (fun x => !(ch x == '\n')) := by
  intro r; congr 1; funext x; revert x; exact all_bytes (by decide +kernel)

-- ### W3 comment dispatch after the slash-dash (doc comment tokens, else a block comment)
theorem docopen_eq : ∀ x : UInt8, (x == 45 || x == 33) = (ch x = '-' ∨ ch x = '!' : Bool) :=
  all_bytes (by decide +kernel)

-- ### W4 nested block comments: `blockEnd` = `finishCommentBlock` when started at the first body byte
theorem fcb_nil (f n : Nat) : fcb f n [] = none := by cases f <;> rfl
theorem c45 : ∀ c : UInt8, (c = 45) ↔ ch c = '-' := fun c => by revert c; exact all_bytes (by decide +kernel)
theorem c47 : ∀ c : UInt8, (c = 47) ↔ ch c = '/' := fun c => by revert c; exact all_bytes (by decide +kernel)

theorem blockEnd_eq_fcb : ∀ (f d : Nat) (l : List UInt8), l.length < f → blockEnd d l = fcb f (d + 1) l := by
  intro f; induction f with
  | zero => intro d l h; omega
  | succ f ih =>
    intro d l h
    match l with
    | [] => simp [blockEnd, fcb]
    | [c] =>
      simp only [blockEnd, fcb, fcb_nil]
      split <;> try rfl
      split <;> rfl
    | c :: c' :: r =>
      simp only [List.length_cons] at h
      simp only [blockEnd, fcb]
      by_cases a : ch c = '-'
      · have a0 := (c45 c).2 a
        by_cases b : ch c' = '/'
        · have b0 := (c47 c').2 b
          rw [if_pos ⟨a0, b0⟩, if_pos a, if_pos b]
          by_cases e : d = 0
          · subst e; simp
          · obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
            simp only [if_neg (by omega : ¬ k + 1 + 1 = 1)]
            simp only [Nat.add_sub_cancel]
            exact ih k r (by omega)
        · have b0 : ¬ c' = 47 := fun x => b ((c47 c').1 x)
          rw [if_neg (by simp [b0]), if_pos a, if_neg b]
          have a1 : ¬ c = 47 := fun x => by have := (c47 c).1 x; rw [a] at this; exact absurd this (by decide)
          rw [if_neg (by simp [a1])]
          exact ih d (c' :: r) (by simp; omega)
      · have a0 : ¬ c = 45 := fun x => a ((c45 c).1 x)
        rw [if_neg (by simp [a0]), if_neg a]
        by_cases a2 : ch c = '/'
        · have a20 := (c47 c).2 a2
          rw [if_pos a2]
          by_cases b : ch c' = '-'
          · have b0 := (c45 c').2 b
            rw [if_pos ⟨a20, b0⟩, if_pos b]
            exact ih (d + 1) r (by omega)
          · have b0 : ¬ c' = 45 := fun x => b ((c45 c').1 x)
            rw [if_neg (by simp [b0]), if_neg b]
            exact ih d (c' :: r) (by simp; omega)
        · have a20 : ¬ c = 47 := fun x => a2 ((c47 c).1 x)
          rw [if_neg (by simp [a20]), if_neg a2]
          exact ih d (c' :: r) (by simp; omega)


-- ### W5 candidate rules (the fixes) and their equality with the mirror of Lean's `whitespace`
theorem c45' : ∀ c : UInt8, (ch c = '-') ↔ c = 45 := fun c => (c45 c).symm
theorem c47' : ∀ c : UInt8, (ch c = '/') ↔ c = 47 := fun c => (c47 c).symm
theorem c33 : ∀ c : UInt8, (ch c = '!') ↔ c = 33 := fun c => by revert c; exact all_bytes (by decide +kernel)
theorem c9 : ∀ c : UInt8, (ch c = '\t') ↔ c = 9 := fun c => by revert c; exact all_bytes (by decide +kernel)
theorem c13 : ∀ c : UInt8, (ch c = '\r') ↔ c = 13 := fun c => by revert c; exact all_bytes (by decide +kernel)
theorem c10 : ∀ c : UInt8, (ch c = '\n') ↔ c = 10 := fun c => by revert c; exact all_bytes (by decide +kernel)
theorem cws : ∀ c : UInt8, (ch c).isWhitespace = true ↔ (c = 32 ∨ c = 10 ∨ c = 9 ∨ c = 13) :=
  fun c => by revert c; exact all_bytes (by decide +kernel)

/-- Lean's block comment right after the slash-dash opener: the first body byte is CONSUMED UNEXAMINED
(`s.next c i` at Basic.lean:578), then `finishCommentBlock 1`. nano's `blockEnd 0 tail` examines it. -/
def blockEndX : List UInt8 → Option (List UInt8)
  | [] => none
  | _ :: r => blockEnd 0 r

theorem blockEndX_eq : ∀ l : List UInt8, blockEndX l = (match l with | [] => none | _ :: r => fcb (r.length + 1) 1 r) := by
  intro l; cases l with
  | nil => rfl
  | cons x r => exact blockEnd_eq_fcb (r.length + 1) 0 r (by omega)

/-- candidate fix of nano's `docWs`: tab and CR (no LF) are errors, a comment opener skips its first body byte -/
def docWsFix : Nat → List UInt8 → Option (List UInt8)
  | 0, _ => none
  | _ + 1, [] => some []
  | f + 1, c :: r =>
    if c = 9 ∨ c = 13 then none
    else if c = 32 ∨ c = 10 then docWsFix f r
    else if c = 45 ∧ r.head? = some 45 then docWsFix f (r.dropWhile (· != 10))
    else if c = 47 ∧ r.head? = some 45 ∧ r.tail.head? ≠ some 45 ∧ r.tail.head? ≠ some 33 then
      (blockEndX r.tail).bind (docWsFix f)
    else some (c :: r)

theorem docWsFix_eq_lws : ∀ (f : Nat) (l : List UInt8), docWsFix f l = lws f l := by
  intro f; induction f with
  | zero => intro l; rfl
  | succ f ih =>
    intro l
    match l with
    | [] => rfl
    | c :: r =>
      simp only [docWsFix, lws, c9, c13, cws, c45', c47', c33, ← line_eq]
      by_cases h1 : c = 9 ∨ c = 13
      · simp [h1]
      · by_cases h2 : c = 32 ∨ c = 10
        · have h2' : (c = 32 ∨ c = 10 ∨ c = 9 ∨ c = 13) := by rcases h2 with h | h <;> simp [h]
          simp [h1, h2, h2', ih]
        · have h2' : ¬ (c = 32 ∨ c = 10 ∨ c = 9 ∨ c = 13) := by
            rintro (h|h|h|h) <;> simp_all
          simp only [h1, h2, h2', if_false]
          by_cases h3 : c = 45
          · subst h3
            cases r with
            | nil => simp
            | cons d r' =>
              by_cases hd : d = 45
              · subst hd; simp [ih]
              · simp [hd]
          · by_cases h4 : c = 47
            · subst h4
              cases r with
              | nil => simp
              | cons d r1 =>
                by_cases hd : d = 45
                · subst hd
                  cases r1 with
                  | nil => simp [blockEndX]
                  | cons x r2 =>
                    by_cases hx : x = 45 ∨ x = 33
                    · rcases hx with h | h <;> simp [h]
                    · have hx1 : ¬ x = 45 := fun h => hx (Or.inl h)
                      have hx2 : ¬ x = 33 := fun h => hx (Or.inr h)
                      simp [hx1, hx2, blockEndX, blockEnd_eq_fcb (r2.length + 1) 0 r2 (by omega), funext ih]
                · simp [hd]
            · simp [h3, h4]; intro h; exact absurd h h2

-- ### F1, F2: nano's `step` accepts these, Lean's `whitespace` does not (observed in Lean 4.34.1 too: README)
def bs (s : String) : List UInt8 := s.toList.map fun c => c.toNat.toUInt8
/-- F1: a tab between a doc-comment opener and its body: nano accepts, Lean errors "tabs are not allowed" -/
theorem F1_nano_accepts : (step (bs "/--\tfoo -/\ndef x")).isSome = true := by decide +kernel
/-- the whitespace after the opener (`docWs` in nano, trailing whitespace of the doc-comment opener token in Lean) -/
theorem F1_docWs_accepts : (docWs 100 (bs "\tfoo -/\ndef x")).isSome = true := by decide +kernel
theorem F1_lean_rejects : lws 100 (bs "\tfoo -/\ndef x") = none := by decide +kernel
theorem F1_fix_rejects : docWsFix 100 (bs "\tfoo -/\ndef x") = none := by decide +kernel
/-- F2: slash-dash-slash-dash: Lean skips the third byte, so the first dash-slash closes the comment; nano nests -/
theorem F2_nano_rest : (step (bs "/-/- -/ -/\ndef x")).map (·.2) = some (bs "\ndef x") := by decide +kernel
theorem F2_lean_rest : lws 100 (bs "/-/- -/ -/\ndef x") = some (bs "-/\ndef x") := by decide +kernel
theorem F2_differ : (step (bs "/-/- -/ -/\ndef x")).map (·.2) ≠ lws 100 (bs "/-/- -/ -/\ndef x") := by decide +kernel

end H10
