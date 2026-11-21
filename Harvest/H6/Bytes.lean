/- Harvest/H6/Bytes: the byte/char leaves of the term syntax nano does not have yet: `λ`/`fun`, `↦`/`=>`, `⟨ ⟩`, `·`.
Candidate nano rule = lexer byte strings for those tokens (what an `opTable` row would hold) + "these chars never extend an identifier".
Theorems are against `String.toUTF8` and Lean's `isIdFirst`/`isIdRest` (Init/Meta/Defs.lean:101-136), both total. -/
import Lean
namespace H6
open Lean

/-- UTF-8 bytes of the new tokens (candidate `opTable` rows) -/
def newTokBytes : List (String × List UInt8) :=
  [("λ", [0xCE, 0xBB]), ("↦", [0xE2, 0x86, 0xA6]), ("⟨", [0xE2, 0x9F, 0xA8]), ("⟩", [0xE2, 0x9F, 0xA9]), ("·", [0xC2, 0xB7]),
   ("fun", [102, 117, 110]), ("=>", [61, 62]), ("show", [115, 104, 111, 119]), ("from", [102, 114, 111, 109]),
   ("have", [104, 97, 118, 101])]

theorem newTokBytes_eq : newTokBytes.all (fun e => e.1.toUTF8.toList == e.2) = true := by decide +kernel

/-- the non-ASCII punctuation tokens never start or continue a Lean identifier: a nano lexer may cut a word at them -/
theorem punct_not_ident : ∀ c ∈ ['λ', '↦', '⟨', '⟩', '·'], isIdFirst c = false ∧ isIdRest c = false := by decide +kernel

/-- why `λ` is special: Greek letters are identifier letters (`isLetterLike`) except `λ`, `Π`, `Σ` (they are binder tokens) -/
theorem greek_exceptions : isLetterLike 'α' = true ∧ isLetterLike 'λ' = false ∧ isLetterLike 'Π' = false ∧
    isLetterLike 'Σ' = false := by decide +kernel

/-- keywords of this area as identifier-looking words: a nano word rule `isW`-run equal to one of them must be a keyword,
not a name (they are Lean tokens: `fun`, `from`, `show`, `have` are in the 168 reserved words of LEAN_RULES §3) -/
theorem kw_are_words : ["fun", "from", "show", "have"].all (fun s => s.toList.all fun c => isIdRest c) = true := by
  decide +kernel

end H6
