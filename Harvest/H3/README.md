# Harvest H3: identifiers (letter-like ranges, subscripts, «escaped» and dotted names, UTF-8 decoding)

Standalone (imports only Lean core), branch `harvest-3` off `lean-equiv`, Lean 4.34.1. Method as `Testing/notes/LEAN_EQUIV.md`:
a nano-style candidate (interval table / byte guard + arithmetic decode / string shape) and a theorem against Lean's own total
definition. Lean paths are under `src/lean/`. All files check locally with `lean`; `REVIEW.lean` prints the axioms (only `propext`,
`Quot.sound`, `Classical.choice`; two theorems use none). No `sorry`, no `native_decide`; `decide +kernel` only on bounded ranges.
Build: `lake build Harvest.H3.REVIEW` (lakefile entry `Harvest` added on this branch only).

| feature | Lean def (file:line) | candidate nano rule | theorem | status | value for nano | effort |
|---|---|---|---|---|---|---|
| letter-like chars | `isLetterLike` Init/Meta/Defs.lean:98 | `inIv llIv n`: 11 disjoint intervals (λ, Π, Σ, ×, ÷ holes removed) | `letterLike_eq` (equality, every `Char`) | proved | Greek/Latin-1/Coptic/letterlike/math-alphabet identifiers (`α`, `ℕ`, `𝔸`) | S: table + 1 decode step in lexer |
| subscript chars | `isSubScriptAlnum` :112 | `inIv subIv n` (4 intervals) | `subScript_eq` | proved | `x₁`, `xₐ`, `xᵢ` as identifier tails | S |
| identifier first | `isIdFirst` :120 | `idFirstC n` = ASCII alpha, `_`, table | `idFirst_eq`, `idFirstC_imp` | proved | complements `LeanEquiv.idFirst_eq_lean` (ASCII) to all code points | S |
| identifier rest | `isIdRest` :133 | `idRestC n` = alnum, `_ ' ! ?`, table, subscripts | `idRest_eq`, `idRestC_imp` | proved | same, tail chars | S |
| holes (λ Π Σ × ÷) | `isLetterLike` exceptions | table excludes them | `holes` | proved | `λ` stays the `fun` token, `×` the type operator: `λx` / `a×b` do not become names | free |
| UTF-8 2-byte decode | `ByteArray.utf8DecodeChar?` Init/Data/String/Decode.lean:1008 | `ok2` guard (C2..DF, 80..BF) + `dec2` shifts/masks | `dec2_eq` (guard ⇒ Lean decodes to `dec2`) | proved | reading `α`, `«` etc. from bytes | S |
| UTF-8 3-byte decode | same | `ok3` (E1..E2, cont, cont), `dec3` | `dec3_eq` | proved (first byte E1..E2 only: subscripts, Greek ext., letterlike block; E0/ED/EE/EF omitted: overlong/surrogate cases) | `x₁`, `ℕ` | S |
| UTF-8 4-byte decode | same | `ok4` (F0 9D 92..96 xx), `dec4` | `dec4_eq` | proved (math alphabets only) | `𝔸`, `𝕜` | S |
| byte rule ⇒ identifier char | `isIdRest` / `isIdFirst` after the decoder | `ok2/ok3` guard ∧ `idRestC (dec ..)` | `idRest2`, `idRest3`, `idFirst2` (+ worked `example`s α, `₁`, λ) | proved | the actual lexer-shaped statement: accepted bytes ⇒ Lean sees an id char | S |
| `«` `»` brackets | `idBeginEscape`/`idEndEscape` :139-142 | bytes `C2 AB` / `C2 BB` | `escOpen_lean`, `escClose_lean`, `esc_unique` (code points exactly 0xAB, 0xBB) | proved | `«my name»` components | S |
| escaped component text | `Name.escapePart` Init/Data/ToString/Name.lean:55 | `«`++s++`»`, no `»` inside | `escapePart_force`, `escapePart_force_none` | proved for `force = true` only (the `force = false` branch calls `partial needsNoEscapeAsciiRest`, kernel-opaque) | what an escaped name denotes / prints | S |
| dotted name text | `Name.toStringWithSep` :73 | components, each further one preceded by `.` (`joinDots`) | `toString_mkName` (escape off) | proved | `A.b.c` as one `Name`, round trip text | S |
| name root | `Name.getRoot` Init/Meta/Defs.lean:144 | first component | `getRoot_mkName` | proved | namespace/root-clash check (M8) | S |
| `.` not in a name | `isIdRest '.'` | none needed | `dot_not_idRest` | proved | components cannot contain `.`, so dotted split is unambiguous | free |
| lexing of identifiers (`identFnAux`, `mkIdResult`) | Parser/Basic.lean:975, :1027 | – | – | not provable: `partial`, `ParserState` | that Lean cuts the token where nano does: fuzz only | – |
| `x.1`, `x.«a»`, `a.b` after-dot rules | `identFnAux` | – | – | not provable: same | needs the loop; fuzz | – |
| keyword vs name | `isToken`, token table (IO.Ref) | – | – | not provable (stateful) | M6 stays open | – |
| macro scopes, `✝` inaccessible | `Name.isInaccessibleUserName` | nano rejects non-table bytes | – | irrelevant: `✝` (U+271D) is not in the table; follows from `idRest_eq` by `decide` if wanted | none | – |
| resolving a name | elaborator | – | – | not provable: environment | M4, M5, M8 | – |

Not harvested here (outside this area): token loop, comments, numerals (see `Nano/LeanEquiv`).
Notes: the 3/4-byte guards are narrower than UTF-8 on purpose: they cover exactly the blocks the tables use, and keep the kernel check
small (full 3-byte space exhausted memory in one try). Kernel time: `Utf8.lean` about 30 s.
