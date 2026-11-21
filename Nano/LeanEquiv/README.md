# Nano/LeanEquiv — nano's trusted syntax definitions proved against Lean 4.34.1's own definitions

Survey and plan: `Testing/notes/LEAN_EQUIV.md`. Only Lean definitions that are total (not `partial`, not `ParserFn`
state machines) can appear in a kernel-checked statement; the rest stays with the fuzzers.

| file | theorem | statement |
|---|---|---|
| `CharClass.lean` | `isW_eq_lean` | `isW b = (Lean.isIdRestAscii b && b != '!' && b != '?')` |
| | `isW_imp_isIdRest` | a nano word byte continues a Lean identifier (`Lean.isIdRest`) |
| | `isD_eq_lean` | `isD b = (Char.ofNat b.toNat).isDigit` |
| | `idFirst_eq_lean` | `(isW b && !isD b) = (Lean.isIdFirstAscii b || b == 39)`: nano also starts a name with `'` (open mismatch M7) |
| | `idFirst_imp_isIdFirst` | without byte 39, a nano identifier start is a Lean one |
| | `isIdRestAscii_eq_isIdRest`, `isIdFirstAscii_eq_isIdFirst` | Lean's byte and `Char` versions agree below 128 |
| | `ws_eq_lean` | Lean whitespace = space, newline, tab, CR (nano skips the first two, rejects the others) |
| | `ws_imp_lean`, `isD_imp_isDigit` | subset forms |
| `Prec.lean` | `binOps_eq_lean`, `binOps_complete` | each `ParSpec.opInfo` operator has the bytes, precedence and left associativity of Lean's `«term_+_»`-style `ParserDescr` |
| | `cmp_prod_lean` | `==`, `<` (50, operands 51) and `×` (35, right assoc) as Lean declares them |
| | `ite_lean` | `termIfThenElse` = `if ` term `then` term `else ` term, keywords = nano tags 32 33 34 |
| `Numeral.lean` | `numeral_sub_toNat?` | a nano numeral word is read by `String.toNat?` with the same value (`decVal w`) |
| | `numVal_eq`, `numVal_eq_lean` | `UInt64.ofNat (numVal w)` is Lean's `UInt64` literal of the digits' decimal value |
| `REVIEW.lean` | | `#print axioms` of all 17: `propext`, `Quot.sound`, `Classical.choice` (one theorem, from Std) |

Limits: the theorems are about tables and character sets. How Lean's tokenizer and Pratt loop *use* them is `partial`
code and is not covered. `decVal` (decimal value of digits) is nano-side; Lean's `decodeNatLitVal?` is `partial` inside.
Method: byte statements are reduced to `∀ i : Fin 256` (`all_bytes`) and closed by `decide +kernel`.
Check: `lake build Nano.LeanEquiv.REVIEW` (or `lean` per file with the spec oleans on `LEAN_PATH`). Imports the spec files and `Std.Data.String.ToNat`.
The boundary of what is proved: `Testing/notes/LEAN_EQUIV.md`, section "Where the proof stops".
