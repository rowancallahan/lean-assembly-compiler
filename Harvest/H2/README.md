# Harvest H2 — string/char literal leaves proved (or bounded) against Lean 4.34.1

Standalone (imports `Lean.Parser.StrInterpolation`, `Lean.Message` only; no nano code). Method as `Nano/LeanEquiv`: byte statements `∀ b : UInt8` by `decide +kernel`.
Lean paths: `src/lean/` of the 4.34.1 toolchain. **Key finding:** every Lean decoder that takes a `String` (`decodeQuotedChar`, `decodeCharLit`,
`decodeStrLit`, `decodeStringGap`, `decodeInterpStrLit`) reads it through `String.Internal.get/next/atEnd`, which are `opaque` `@[extern]` constants
with no kernel-visible spec (`Init/Data/String/Bootstrap.lean:104`), so they are **not provable at all** (even the total ones); `decodeStrLitAux`,
`decodeRawStrLitAux`, `strLitFnAux`, `rawStrLitFnAux`, `interpolatedStrFn` are additionally `partial`. What is provable: the Char predicates, the
descriptor data, `Char.ofNat`/UTF-8 value semantics, and a transliterated list model checked by `#guard` differential tests (a trust gap, named below).
Also: Lean has `\xHH`, `\uHHHH` (exactly 4 digits) — **no `\u{…}`**; `\r` exists; `\0`, `\a`, `\e` do not.

| feature | Lean def (file:line) | candidate nano rule | theorem (file) | status | value for nano | effort |
|---|---|---|---|---|---|---|
| hex digit byte | `Char.isHexDigit` Init/Data/Char/Basic.lean:137 | `Escape.hexv` (value 0..15) | `hex_iff` (Escape) | proved+built (lean 4.34.1, axioms ⊆ std) | `\x`, `\u`, `0x` literals | 1 h |
| one-byte escapes `\\ \" \' \r \n \t` | `isQuotableCharDefault` Parser/Basic.lean:673 | `Escape.esc` (byte → byte) | `quotable_iff` (Escape) | proved | string/char literals with escapes | 1 h |
| escape set inside `s!"…"` | `isQuotableCharForStrInterpolant` Parser/StrInterpolation.lean:14 | `esc ∪ {`{`}` | `quotable_interp_iff` (Escape) | proved | interpolated strings | 1 h |
| decode of the one-char escapes (`\\ \" \' \r \n \t`; "e" is a placeholder, Lean has no `\e`) and `\xHH` (value < 128) | `decodeQuotedChar` Init/Meta/Defs.lean:1089 | `Mirror.dec` | `dec_sub_mirror` (Mirror) vs list transliteration `mirror`; `#guard` tests vs the real function (all 128 one-char, all 128² `\x` pairs, sampled `\u`) | **proved vs mirror**; real fn: tested only (opaque `String.Internal.get`) | exact escape semantics for string/char lits | 0.5 d (fold `dec` into LexSpec) |
| `\xHH` stored bytes | `Char.ofNat` + `String.utf8EncodeChar` | accept only HH < 0x80 | `x_ascii`, `x_high` (Value) | proved+built (lean 4.34.1, axioms ⊆ std) | no UTF-8 surprise: HH ≥ 0x80 is 2 bytes | 1 h |
| `\uHHHH` value | `Char.ofNat` Init/Prelude; Defs.lean:1107 | value = 4-digit number; reject D800–DFFF | `u_val`, `u_surrogate`, `u_len` (Value) | proved+built (lean 4.34.1, axioms ⊆ std) | `\u` escapes, UTF-8 data sizing; surrogate → NUL trap | 0.5 d |
| `s!` / `m!` token shape | `«termS!_»` Init/Data/ToString/Macro.lean:14; `Lean.«termM!_»` Message.lean:854 | `interpShape "s!"` | `s_bang`, `m_bang` (Interp) | proved+built | `s!"…{e}…"` as `"s!"` + chunks; max prec 1024 | 0.5 d + expansion semantics |
| `f!` | Init/Data/Format/Macro.lean:16 | same | — | same shape by source; not harvested (name `«termF!_»` not checked) | — | — |
| plain string literal scan/decode | `decodeStrLitAux` Defs.lean:1121 `partial`; `strLitFnAux` Parser/Basic.lean:719 `partial` | list model + `dec` per escape | none | **not provable**: `partial` + opaque `String.Internal.*`; only per-escape leaf above | string literals | fuzz (Testing) |
| char literal | `decodeCharLit` Defs.lean:1177 (total, but opaque get); `charLitFnAux` Parser/Basic.lean:704 | `'c'`, `'\<escape>'` via `dec` | none | **not provable** (opaque); `'` accepted by Lean parser as the char in `'''` | char literals | fuzz |
| raw strings `r#"…"#` | `decodeRawStrLitAux` :1144, `isRawStrLitStart`/`rawStrLitFnAux` Parser/Basic.lean `partial` | — | none | **not provable** (`partial`) | raw strings | fuzz |
| string gap `\⏎ ws*` | `decodeStringGap` :1112, `stringGapFn` `partial`; whitespace set = `Char.isWhitespace` | skip rule | none (whitespace set already `ws_eq_lean`) | **not provable**; parser requires exactly one newline, decoder accepts any whitespace | multi-line strings | fuzz |
| `String.quote`/`Char.quoteCore` (repr output) | Init/Data/Repr.lean | — | none | not provable generally: `String.Internal.append` opaque (`'\n'` case reduces, `\x01` gets stuck) | printing strings | n/a |

Build: all files compile with Lean 4.34.1 (`Harvest/H2/Review.lean` prints axioms: only `propext`, `Quot.sound`, `Classical.choice`; `Value.lean` takes ~2 min, 16-bit kernel sweeps).
Trust gap: `Mirror.mirror` is a hand transliteration of `decodeQuotedChar`; fidelity is `#guard`-tested, not proved (opaque `String.Internal.get`).
`dec` rejects `\xHH` with HH ≥ 0x80 by design (codepoint U+00HH is 2 UTF-8 bytes, `x_high`); `\u` needs a surrogate reject (`u_surrogate`).
