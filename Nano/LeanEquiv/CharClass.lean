/- Nano/LeanEquiv/CharClass: nano's trusted byte classes (`LexSpec.isW`, `isD`, the whitespace test of `LexSpec.step`)
against Lean 4.34.1's own total definitions (`Lean.isIdRestAscii`, `Lean.isIdFirstAscii`, `Lean.isIdRest`,
`Lean.isIdFirst`, `Char.isDigit`, `Char.isWhitespace`; Init/Meta/Defs.lean:120-137, Init/Data/Char/Basic.lean:97-146).
Every statement is over all 256 bytes and closed by kernel evaluation.  README.md in this folder. -/
import Nano.Lexer.Lex2Spec
namespace LeanEquiv
open LexSpec

/-- the Lean character of a byte -/
abbrev ch (b : UInt8) : Char := Char.ofNat b.toNat

theorem all_bytes {p : UInt8 → Prop} (h : ∀ i : Fin 256, p (UInt8.ofNat i.val)) (b : UInt8) : p b := by
  have := h ⟨b.toNat, b.toNat_lt⟩
  simpa using this

/-- nano's word bytes are exactly Lean's ASCII identifier-rest bytes without `!` and `?` -/
theorem isW_eq_lean : ∀ b, isW b = (Lean.isIdRestAscii b && b != 33 && b != 63) :=
  all_bytes (by decide +kernel)

/-- every nano word byte continues a Lean identifier -/
theorem isW_imp_isIdRest : ∀ b, isW b = true → Lean.isIdRest (ch b) = true :=
  all_bytes (by decide +kernel)

/-- nano's digits are exactly Lean's -/
theorem isD_eq_lean : ∀ b, isD b = (ch b).isDigit :=
  all_bytes (by decide +kernel)

/-- the first byte of a nano identifier (a word byte, not a digit) is a Lean identifier-first byte, or the quote
(39): the one known difference (LEAN_RULES M7; Lean reads a character literal there) -/
theorem idFirst_eq_lean : ∀ b, (isW b && !isD b) = (Lean.isIdFirstAscii b || b == 39) :=
  all_bytes (by decide +kernel)

theorem idFirst_imp_isIdFirst : ∀ b, isW b = true → isD b = false → b ≠ 39 → Lean.isIdFirst (ch b) = true :=
  all_bytes (by decide +kernel)

/-- Lean's two versions (byte, `Char`) agree on ASCII, so the byte statements above are statements about `Char`s -/
theorem isIdRestAscii_eq_isIdRest : ∀ b, b < 128 → Lean.isIdRestAscii b = Lean.isIdRest (ch b) :=
  all_bytes (by decide +kernel)
theorem isIdFirstAscii_eq_isIdFirst : ∀ b, b < 128 → Lean.isIdFirstAscii b = Lean.isIdFirst (ch b) :=
  all_bytes (by decide +kernel)

/-- the bytes `step` skips (space, newline) are Lean whitespace; Lean's other two (tab, CR) nano rejects -/
theorem ws_eq_lean : ∀ b, (ch b).isWhitespace = (b == 32 || b == 10 || b == 9 || b == 13) :=
  all_bytes (by decide +kernel)

/-- subset forms: what nano skips is Lean whitespace; a nano digit is a Lean digit -/
theorem ws_imp_lean : ∀ b, (b == 32 || b == 10) = true → (ch b).isWhitespace = true :=
  all_bytes (by decide +kernel)
theorem isD_imp_isDigit (b : UInt8) (h : isD b = true) : (ch b).isDigit = true := isD_eq_lean b ▸ h

end LeanEquiv
