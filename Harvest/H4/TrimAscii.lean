/- Harvest/H4/TrimAscii: `s.trimAscii.copy = s` for a string whose first and last character are not whitespace, proved by
rewriting with the (well-founded) definitions' equation lemmas, NOT by kernel reduction (`Pos.skipWhile`/`revSkipWhile`
are `termination_by`, so `decide`/`rfl` get stuck).  Lean/Init/Data/String/Slice.lean:426-480, 764-830. -/
import Lean
namespace H4
open String

/-- the first character is not whitespace (or the slice is empty): nothing is skipped at the start -/
theorem Slice.trimAsciiStart_eq (sl : String.Slice)
    (h : ∀ h : sl.startPos ≠ sl.endPos, ¬ (sl.startPos.get h).isWhitespace = true) :
    sl.trimAsciiStart = sl := by
  have hn : sl.startPos.skipWhile Char.isWhitespace = sl.startPos := by
    unfold String.Slice.Pos.skipWhile
    have : sl.startPos.skip? Char.isWhitespace = none := by
      simp only [String.Slice.Pos.skip?, String.Slice.skipPrefix?]
      show Option.map _ (if e : sl.startPos = sl.endPos then none
        else if Char.isWhitespace (sl.startPos.get e) then some (sl.startPos.next e) else none) = none
      by_cases e : sl.startPos = sl.endPos
      · simp [e]; rfl
      · have := h e
        simp [e, this]; rfl
    simp [this]
  simp [String.Slice.trimAsciiStart, String.Slice.dropWhile, String.Slice.skipPrefixWhile, hn,
    String.Slice.sliceFrom_startPos]

/-- the last character is not whitespace (or the slice is empty): nothing is skipped at the end -/
theorem Slice.trimAsciiEnd_eq (sl : String.Slice)
    (h : ∀ h : sl.endPos ≠ sl.startPos, ¬ ((sl.endPos.prev h).get (by simp)).isWhitespace = true) :
    sl.trimAsciiEnd = sl := by
  have hn : sl.endPos.revSkipWhile Char.isWhitespace = sl.endPos := by
    unfold String.Slice.Pos.revSkipWhile
    have : sl.endPos.revSkip? Char.isWhitespace = none := by
      simp only [String.Slice.Pos.revSkip?, String.Slice.skipSuffix?]
      rw [Option.map_eq_none_iff]
      have e : sl.sliceTo sl.endPos = sl := String.Slice.sliceTo_endPos
      generalize sl.sliceTo sl.endPos = t at e ⊢
      subst e
      show (if e : t.endPos = t.startPos then none
        else if Char.isWhitespace ((t.endPos.prev e).get (by simp)) then some (t.endPos.prev e) else none) = none
      by_cases e : t.endPos = t.startPos
      · simp [e]
      · have := h e
        simp [e, this]
    simp [this]
  simp [String.Slice.trimAsciiEnd, String.Slice.dropEndWhile, String.Slice.skipSuffixWhile, hn,
    String.Slice.sliceTo_endPos]

/-- **the lemma**: a string whose first and last characters are not whitespace is its own `trimAscii` -/
theorem trimAscii_copy (s : String)
    (h1 : ∀ h : s.toSlice.startPos ≠ s.toSlice.endPos, ¬ (s.toSlice.startPos.get h).isWhitespace = true)
    (h2 : ∀ h : s.toSlice.endPos ≠ s.toSlice.startPos,
      ¬ ((s.toSlice.endPos.prev h).get String.Slice.Pos.prev_ne_endPos).isWhitespace = true) :
    s.trimAscii.copy = s := by
  have a := Slice.trimAsciiStart_eq _ h1
  have : s.toSlice.trimAscii = s.toSlice := by
    simp only [String.Slice.trimAscii, a]
    exact Slice.trimAsciiEnd_eq _ h2
  simp [String.trimAscii, this]

/-- the side conditions are decidable on a literal, so a token literal is closed by one line -/
theorem fun_trim : "fun".trimAscii.copy = "fun" := trimAscii_copy _ (by decide +kernel) (by decide +kernel)
theorem anon_trim : "⟨".trimAscii.copy = "⟨" := trimAscii_copy _ (by decide +kernel) (by decide +kernel)

/-- use on Lean's token collection: the token of `Parser.symbolNoAntiquot "⟨"` (no kernel reduction of `trimAscii`).
LIMIT: tokens padded with spaces (`" :"`, `" with "`, the pretty-printing spaces of most notation) are not covered:
`trimAscii` then really removes characters, and a lemma for that needs `Pos` arithmetic on `s.toSlice` (not done). -/
theorem anon_token : "⟨" ∈ (Lean.Parser.symbolNoAntiquot "⟨").info.collectTokens [] := by
  simp [Lean.Parser.symbolNoAntiquot, anon_trim, Lean.Parser.symbolInfo]

/-! ## padded literals by certificates (no Pos lemmas: every positional fact is closed by kernel evaluation on the literal) -/

theorem skipWhile_step {sl : String.Slice} (pos nxt : sl.Pos) (h : pos.skip? Char.isWhitespace = some nxt)
    (hl : pos < nxt) : pos.skipWhile Char.isWhitespace = nxt.skipWhile Char.isWhitespace := by
  rw [String.Slice.Pos.skipWhile]; simp [h, hl]

theorem skipWhile_done {sl : String.Slice} (pos : sl.Pos) (h : pos.skip? Char.isWhitespace = none) :
    pos.skipWhile Char.isWhitespace = pos := by
  rw [String.Slice.Pos.skipWhile]; simp [h]

theorem revSkipWhile_step {sl : String.Slice} (pos prv : sl.Pos) (h : pos.revSkip? Char.isWhitespace = some prv)
    (hl : prv < pos) : pos.revSkipWhile Char.isWhitespace = prv.revSkipWhile Char.isWhitespace := by
  rw [String.Slice.Pos.revSkipWhile]; simp [h, hl]

theorem revSkipWhile_done {sl : String.Slice} (pos : sl.Pos) (h : pos.revSkip? Char.isWhitespace = none) :
    pos.revSkipWhile Char.isWhitespace = pos := by
  rw [String.Slice.Pos.revSkipWhile]; simp [h]

/-- **certificate form**: if the start trim stops at `p` and the end trim of the remaining slice stops at `q`, the trimmed
string is the copy of what is between (closed by `decide +kernel` on a literal) -/
theorem trimAscii_cert (s : String) (p : s.toSlice.Pos) (q : (s.toSlice.sliceFrom p).Pos) (t : String)
    (hp : s.toSlice.startPos.skipWhile Char.isWhitespace = p)
    (hq : (s.toSlice.sliceFrom p).endPos.revSkipWhile Char.isWhitespace = q)
    (hc : ((s.toSlice.sliceFrom p).sliceTo q).copy = t) : s.trimAscii.copy = t := by
  subst hp; subst hq; exact hc

/-- `" :"` (the padding of most notation): one space at the start -/
theorem colon_trim : " :".trimAscii.copy = ":" := by
  have e1 : (" :".toSlice.startPos).skip? Char.isWhitespace = some (" :".toSlice.startPos.next (by decide)) := by decide +kernel
  have e2 : (" :".toSlice.startPos.next (by decide)).skip? Char.isWhitespace = none := by decide +kernel
  refine trimAscii_cert " :" (" :".toSlice.startPos.next (by decide)) _ ":" ?_
    (revSkipWhile_done _ (by decide +kernel)) (by decide +kernel)
  rw [skipWhile_step _ _ e1 (by decide +kernel), skipWhile_done _ e2]

/-- `" with "`: one space at each end -/
theorem with_trim : " with ".trimAscii.copy = "with" := by
  let sl := " with ".toSlice
  have e1 : sl.startPos.skip? Char.isWhitespace = some (sl.startPos.next (by decide)) := by decide +kernel
  have e2 : (sl.startPos.next (by decide)).skip? Char.isWhitespace = none := by decide +kernel
  have hp : sl.startPos.skipWhile Char.isWhitespace = sl.startPos.next (by decide) := by
    rw [skipWhile_step _ _ e1 (by decide +kernel), skipWhile_done _ e2]
  let sl2 := sl.sliceFrom (sl.startPos.next (by decide))
  have f1 : sl2.endPos.revSkip? Char.isWhitespace = some (sl2.endPos.prev (by decide)) := by decide +kernel
  have f2 : (sl2.endPos.prev (by decide)).revSkip? Char.isWhitespace = none := by decide +kernel
  refine trimAscii_cert " with " (sl.startPos.next (by decide)) (sl2.endPos.prev (by decide)) "with" hp ?_
    (by decide +kernel)
  rw [revSkipWhile_step _ _ f1 (by decide +kernel), revSkipWhile_done _ f2]

/-- a padded notation token lands in `collectTokens` -/
theorem with_token : "with" ∈ (Lean.Parser.symbolNoAntiquot " with ").info.collectTokens [] := by
  simp [Lean.Parser.symbolNoAntiquot, with_trim, Lean.Parser.symbolInfo]

/-- `" => "`, the arrow of `fun x => e` -/
theorem arrow_trim : " => ".trimAscii.copy = "=>" := by
  let sl := " => ".toSlice
  have e1 : sl.startPos.skip? Char.isWhitespace = some (sl.startPos.next (by decide)) := by decide +kernel
  have e2 : (sl.startPos.next (by decide)).skip? Char.isWhitespace = none := by decide +kernel
  have hp : sl.startPos.skipWhile Char.isWhitespace = sl.startPos.next (by decide) := by
    rw [skipWhile_step _ _ e1 (by decide +kernel), skipWhile_done _ e2]
  let sl2 := sl.sliceFrom (sl.startPos.next (by decide))
  have f1 : sl2.endPos.revSkip? Char.isWhitespace = some (sl2.endPos.prev (by decide)) := by decide +kernel
  have f2 : (sl2.endPos.prev (by decide)).revSkip? Char.isWhitespace = none := by decide +kernel
  refine trimAscii_cert " => " (sl.startPos.next (by decide)) (sl2.endPos.prev (by decide)) "=>" hp ?_
    (by decide +kernel)
  rw [revSkipWhile_step _ _ f1 (by decide +kernel), revSkipWhile_done _ f2]

/-- the tokens of Lean's `fun`: the keyword and its ASCII/Unicode spelling `λ`, and the arrow -/
theorem fun_tokens :
    "fun" ∈ (Lean.Parser.unicodeSymbolNoAntiquot "λ" "fun" true).info.collectTokens [] ∧
    "λ" ∈ (Lean.Parser.unicodeSymbolNoAntiquot "λ" "fun" true).info.collectTokens [] ∧
    "=>" ∈ (Lean.Parser.symbolNoAntiquot " => ").info.collectTokens [] := by
  have l : "λ".trimAscii.copy = "λ" := trimAscii_copy _ (by decide +kernel) (by decide +kernel)
  simp [Lean.Parser.unicodeSymbolNoAntiquot, Lean.Parser.unicodeSymbolInfo, Lean.Parser.symbolNoAntiquot,
    Lean.Parser.symbolInfo, fun_trim, l, arrow_trim]

/-- `"← "` and `"<- "` (trailing space only), the two spellings of the `do` arrow -/
theorem larrow_trim : "← ".trimAscii.copy = "←" ∧ "<- ".trimAscii.copy = "<-" := by
  constructor
  · let sl := "← ".toSlice
    have hp : sl.startPos.skipWhile Char.isWhitespace = sl.startPos :=
      skipWhile_done _ (by decide +kernel)
    let sl2 := sl.sliceFrom sl.startPos
    have f1 : sl2.endPos.revSkip? Char.isWhitespace = some (sl2.endPos.prev (by decide)) := by decide +kernel
    have f2 : (sl2.endPos.prev (by decide)).revSkip? Char.isWhitespace = none := by decide +kernel
    refine trimAscii_cert "← " sl.startPos (sl2.endPos.prev (by decide)) "←" hp ?_ (by decide +kernel)
    rw [revSkipWhile_step _ _ f1 (by decide +kernel), revSkipWhile_done _ f2]
  · let sl := "<- ".toSlice
    have hp : sl.startPos.skipWhile Char.isWhitespace = sl.startPos :=
      skipWhile_done _ (by decide +kernel)
    let sl2 := sl.sliceFrom sl.startPos
    have f1 : sl2.endPos.revSkip? Char.isWhitespace = some (sl2.endPos.prev (by decide)) := by decide +kernel
    have f2 : (sl2.endPos.prev (by decide)).revSkip? Char.isWhitespace = none := by decide +kernel
    refine trimAscii_cert "<- " sl.startPos (sl2.endPos.prev (by decide)) "<-" hp ?_ (by decide +kernel)
    rw [revSkipWhile_step _ _ f1 (by decide +kernel), revSkipWhile_done _ f2]

theorem larrow_tokens :
    "←" ∈ (Lean.Parser.unicodeSymbolNoAntiquot "← " "<- " true).info.collectTokens [] ∧
    "<-" ∈ (Lean.Parser.unicodeSymbolNoAntiquot "← " "<- " true).info.collectTokens [] := by
  simp [Lean.Parser.unicodeSymbolNoAntiquot, Lean.Parser.unicodeSymbolInfo, larrow_trim.1, larrow_trim.2]

theorem arrow_firstTokens :
    (Lean.Parser.symbolNoAntiquot " => ").info.firstTokens = Lean.Parser.FirstTokens.tokens ["=>"] := by
  simp [Lean.Parser.symbolNoAntiquot, Lean.Parser.symbolInfo, arrow_trim]

end H4
