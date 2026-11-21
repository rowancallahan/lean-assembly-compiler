/- Harvest/H2/Escape: nano-style byte rules for string/char escapes against Lean 4.34.1's TOTAL definitions:
`Lean.Parser.isQuotableCharDefault` (Parser/Basic.lean:673), `isQuotableCharForStrInterpolant` (Parser/StrInterpolation.lean:14),
`Char.isHexDigit` (Init/Data/Char/Basic.lean:137), `Lean.Syntax.decodeQuotedChar` (Init/Meta/Defs.lean:1089),
`Lean.Syntax.decodeCharLit` (:1177), `Lean.Syntax.decodeStringGap` (:1112).
Imports Lean.Parser.StrInterpolation (Init + Lean parser constants only).
NOTE: `decodeQuotedChar`/`decodeCharLit`/`decodeStrLit` read the string through `String.Internal.get`, an `opaque` extern with no
kernel spec in 4.34.1, so they are NOT provable; Mirror.lean covers them with a list model + `#guard` differential tests.  Lean has `\x` + 2 hex digits and `\u` + EXACTLY 4 hex digits (no `\u{..}`). -/
import Lean.Parser.StrInterpolation
namespace H2
open Lean Lean.Syntax Lean.Parser

abbrev ch (b : UInt8) : Char := Char.ofNat b.toNat
abbrev str (l : List UInt8) : String := String.ofList (l.map ch)

theorem all_bytes {p : UInt8 → Prop} (h : ∀ i : Fin 256, p (UInt8.ofNat i.val)) (b : UInt8) : p b := by
  have := h ⟨b.toNat, b.toNat_lt⟩
  simpa using this

/-- nano candidate: value of a hex digit byte -/
def hexv (b : UInt8) : Option Nat :=
  if 48 ≤ b ∧ b ≤ 57 then some (b.toNat - 48)
  else if 97 ≤ b ∧ b ≤ 102 then some (b.toNat - 87)
  else if 65 ≤ b ∧ b ≤ 70 then some (b.toNat - 55) else none

/-- nano candidate: the one-byte escapes `\\ \" \' \r \n \t` -/
def esc (b : UInt8) : Option UInt8 :=
  match b with | 92 => some 92 | 34 => some 34 | 39 => some 39 | 114 => some 13 | 110 => some 10 | 116 => some 9 | _ => none

theorem hex_iff : ∀ b, (hexv b).isSome = (ch b).isHexDigit := all_bytes (by decide +kernel)
theorem quotable_iff : ∀ b, (esc b).isSome = isQuotableCharDefault (ch b) := all_bytes (by decide +kernel)
theorem quotable_interp_iff : ∀ b, ((esc b).isSome || b == 123) = isQuotableCharForStrInterpolant (ch b) :=
  all_bytes (by decide +kernel)

