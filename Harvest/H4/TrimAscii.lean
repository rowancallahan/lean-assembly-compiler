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

end H4
