# Harvest H1: numeric and char literals (hex `0x`, bin `0b`, oct `0o`, `_` separators, char literals)

Lean 4.34.1 (tag v4.34.1). Files: `Lit.lean` (all theorems; imports `Std.Data.String.ToNat`, `Lean.Parser.Basic`, no nano code),
`REVIEW.lean` (`#print axioms`). Checked locally with `lean` 4.34.1: standard axioms only, no `sorry`/`native_decide`.
Statement form is the subset form: nano-style candidate accepts => Lean's total function agrees.

## Key finding: Lean's decoders are not provable targets
`Lean.Syntax.decodeNatLitVal?` and its `decodeBin/Octal/Hex/DecimalLitAux` are `partial` (Init/Meta/Defs.lean:923-978).
`decodeQuotedChar` / `decodeCharLit` (Init/Meta/Defs.lean:1089, 1177) are total but read the string through
`String.Internal.get` / `next`, which are `opaque` in 4.34.1: `decide +kernel` on `decodeQuotedChar "n" 0` is stuck (tried).
The tokenizer side (`numberFnAux`, `hexNumberFn`, `takeDigitsFn`, `charLitFnAux`, Lean/Parser/Basic.lean:817-990, 704) is
`ParserFn` state code, `takeDigitsFn` partial, `mkNodeToken` calls partial `whitespace`. So every proof below anchors to the
total Lean pieces those functions are built from (char predicates, `Nat.digitChar`/`toDigits`, `String.toNat?`, `Char.ofNat`,
`Char.quoteCore`, `isQuotableCharDefault`, `UInt64` literal semantics). The glue (prefix dispatch, digit-run loop) is fuzz-only.

## Catalog
| feature | Lean def (file:line) | candidate nano rule | theorem (`Lit.lean`) | status | value for nano | effort to fold in |
|---|---|---|---|---|---|---|
| hex digit class | `Char.isHexDigit` Init/Data/Char/Basic.lean:137 | `isHex` (0-9 a-f A-F) | `isHex_eq_lean` | proved+built | `0x` digits | low: 1 byte predicate |
| decimal digit class | `Char.isDigit` Init/Data/Char/Basic.lean:130 | `isD` | `isD_eq_lean` | proved+built | base for all radices | none (nano has `isD`) |
| bin/oct digit classes | inline `'0'` `'1'`, `'0' ≤ c ≤ '7'` Lean/Parser/Basic.lean:871,876 (no named def) | `isBin`, `isOct` | `bin_oct_dec_hex` (bin ⊆ oct ⊆ `Char.isDigit` ⊆ `isHexDigit`) | proved+built (inclusion only; exact set is transcribed from source) | `0b`, `0o` | low |
| hex digit value | `decodeHexDigit` (private, Init/Meta/Defs.lean:940) | `hexVal` | `hexVal_digitChar` (`Nat.digitChar (hexVal b) = (ch b).toLower`, `< 16`) | proved+built | `0x`, `\xHH`, `\uHHHH` | low |
| decimal with `_` | `String.Slice.isNat` / `toNat?` Init/Data/String/Slice.lean:976-1014 | `decUs` (digits, `_` only single, between digits) + `runVal 10` | `decUs_toNat?` | proved+built | `1_000_000` | low-medium: lexer + `decVal` skips `_` |
| wrap to `UInt64` for any radix | `instOfNat : OfNat UInt64 n` Init/Data/UInt/BasicAux | `runU r w` (wrapping fold, skips `_`) | `runU_eq`, `runU_lean` | proved+built | `0x`/`0b`/`0o`/`_` literals have Lean's `UInt64` value | low: same shape as `numVal` |
| radix value is the inverse of Lean's printer | `Nat.toDigits` Init/Data/Repr.lean:217, `Nat.digitChar` :180 | `runVal r` | `runVal_toDigits` (`2 ≤ r ≤ 16`) | proved+built | sanity: `0x` of printed `n` is `n`; not an equality with `decodeNatLitVal?` | none (check only) |
| char escape set | `isQuotableCharDefault` Lean/Parser/Basic.lean:673 | `escVal` (`\\ \" \' \r \n \t`) | `escVal_eq_lean` | proved+built | `'\n'` etc. | low |
| char literal body decode | `Char.quoteCore` Init/Data/Repr.lean:360 (Lean's printer of a char literal) | `litDec` (plain ASCII, one-letter escape, `\xHH` < 128) | `litDec_quoteCore` (all non-control ASCII), `litDec_hex` (the `\x` + `Nat.digitChar` digits `smallCharToHex` writes for controls and DEL) | proved+built; the controls' `quoteCore` output is not kernel-reducible (`String.Internal.append` opaque), so 7b states its digits directly | `'a'`, `'\n'`, `'\x41'` as a `UInt8`/`Char` value | medium: new token kind, `'` also starts nano names (open mismatch M7 in LeanEquiv) |
| byte vs `Char` width | `Char.utf8Size` Init/Data/Char/Basic.lean | reject bytes ≥ 128 in `'…'` | `utf8Size_byte` (`utf8Size (ch b) = 1 ↔ b < 128`) | proved+built | a byte literal ≥ 128 would be a different `Char`; rule must say ASCII only | none (a side condition) |
| `\uHHHH` | `decodeQuotedChar` uses `Char.ofNat` Init/Prelude.lean:2889 | `\u` rule must reject D800-DFFF | `ofNat_u16` (every 16-bit value is itself, except surrogates, which become `'\0'`) | proved+built | `'é'`; avoids a silent mismatch | low |
| `decodeNatLitVal?` equality (hex/bin/oct/dec with `_`) | Init/Meta/Defs.lean:964 + 4 `partial` aux | `runVal r` | none | not provable: `partial` | link stays with the fuzzer | n/a |
| tokenizer digit run (`takeDigitsFn`) | Lean/Parser/Basic.lean:817 | digit run: non-empty, last byte a digit, `_` anywhere else | none | not provable: `partial`, and `mkNodeToken` -> `whitespace` partial. Noted: it accepts `1__2` and `0x_1`, while `toNat?` rejects `1__2`, so `decUs` (single `_` between digits) is inside both | n/a | n/a |
| prefix dispatch `0x/0X 0b/0B 0o/0O`, then decimal | `numberFnAux` Lean/Parser/Basic.lean:925-945; `decodeNatLitVal?` :973-976 | `radix : 'x'→16, 'b'→2, 'o'→8` (either case) | none | not provable: `ParserFn` + partial; data only | all non-decimal literals | n/a |
| decimal followed by `.` `e` `E` | `decimalNumberFn` Lean/Parser/Basic.lean:831 | reject: becomes a scientific literal (or `1..2` range) | none | not provable (same reason) | hazard note: `1e5`, `1.5` are not `Nat` numerals; nano must not lex `1e` as numeral+ident | n/a |
| char literal tokenizer | `charLitFnAux` Lean/Parser/Basic.lean:704 | `'` c `'`, `'` `\` esc `'` | none | not provable (ParserFn, `mkNodeToken`). Note it accepts `'''` and a raw newline, so nano rejecting them is safe | n/a | n/a |
| string/`\u`/scientific decoders | `decodeStrLitAux`, `decodeScientificLitVal?` | not attempted (out of area) | none | not provable: `partial` | n/a | n/a |

## Open mismatches found (candidate must avoid)
1. `\uD800`-`\uDFFF`: Lean silently yields `'\0'` (`ofNat_u16`); reject.
2. Source bytes ≥ 128 inside `'…'` are UTF-8 sequences, not one `Char` (`utf8Size_byte`); reject.
3. Lean's tokenizer takes `1__2`, `0x_1`; `String.toNat?` takes only `1_2`; use the stricter `decUs` shape.
4. `0b1`, `0o7`, `0xe` start a prefixed numeral in Lean, but nano today lexes `0` then a name (`b1`): programs using such names after `0` already differ; check before enabling.
5. A decimal followed by `e`/`E`/`.` is a different token (scientific).

## Build
`lake build Harvest.H1.REVIEW` (lakefile entry `Harvest` is on branch `harvest-1` only). No other nano module is imported.
