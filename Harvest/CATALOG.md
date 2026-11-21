# Harvest catalog (H1–H10), Lean 4.34.1

Merged from `Harvest/H{N}/README.md` on `harvest-{N}`. Nothing was re-built or re-checked here; statuses are the READMEs' claims, with the lead's runner-built list applied: **runner-built = H2, H3, H4 (incl. TrimAscii), H5, H7, H9; H1, H6, H8, H10 local-only.** Row ids are `H{n}:{row}` in README order. Statement form throughout: nano candidate rule accepts ⇒ Lean's total function agrees (nano ⊆ Lean).

"drafted" = checked by `#guard`/interpreter only, or not yet built. "not provable" = `partial`, `ParserFn`/closure, opaque, or elaborator/environment. "not attempted" = no theorem and no proof of impossibility.

## 1. Summary

| harvester | area | rows | proved+runner-built | local-only | drafted | not provable | not attempted |
|---|---|---|---|---|---|---|---|
| H1 | numeric/char literals | 17 | 0 | 11 | 0 | 6 | 0 |
| H2 | string/char escapes, `s!` | 13 | 7 | 0 | 0 | 5 | 1 |
| H3 | identifiers, UTF-8 | 19 | 14 | 0 | 0 | 5 | 0 |
| H4 | keywords, tokens, trimAscii | 16 | 12 | 0 | 1 | 3 | 0 |
| H5 | operator table | 14 | 10 | 0 | 0 | 2 | 2 |
| H6 | term syntax leaves | 16 | 0 | 11 | 2 | 3 | 0 |
| H7 | declarations | 17 | 10 | 0 | 2 | 5 | 0 |
| H8 | do-notation | 15 | 0 | 12 | 1 | 2 | 0 |
| H9 | patterns, match, termination | 18 | 15 | 0 | 0 | 3 | 0 |
| H10 | comments, whitespace, scopes | 11 | 0 | 8 | 1 | 2 | 0 |
| **total** | | **156** | **68** | **42** | **7** | **36** | **3** |
Thin spots (do not over-read "proved"): H9 `fun_alts_shape`, `two_disc_shape`, tuple/option/lit shapes are one-shape `rfl` facts about Lean's `match`, not grammar facts; H6 rows 9–11 are trivial `rfl` desugars; H7 `private_roundtrip` is 4 instances; H5 `Sem` witnesses are concrete inputs; H2 `dec_sub_mirror`, H10 whole W/F/scope rows, and H1 `litDec` rest on hand-transcribed mirrors (mirror↔Lean fidelity is `#guard`/differential-tested, not proved); H3 3/4-byte decoders cover only the blocks the tables use.

## 2. All rows, ranked

Ranking = value/effort for the next nano syntax PR. Runner-built rows come first (they can be folded in now), then local-only (need a runner build first), then drafted. Within a tier: small effort and wide unlock first; duplicates of an earlier row sink. Rows without a rank (—) are not provable/not attempted and listed for completeness.

| rank | feature | harvester/theorem | status | unlocks | effort | dependencies / caveat |
|---|---|---|---|---|---|---|
| 1 | reserved words are not names (190-word list) | H4:1 `reserved_not_ident` | proved+runner-built | closes M6 (168 accepted reserved names) | S | none; list is fuzz-derived + H4:5 |
| 2 | reserved word + `1`/`'` stays a name | H4:2 `reserved_ext_ok` | proved+runner-built | `fun1`, `at'` keep working | S | H4:1 |
| 3 | infix rows `\|\|\|` `^^^` `&&&` `+ - ++` `* / %` `<<< >>>` | H5:1 `infixTable_lean` | proved+runner-built | `^^^ / %` etc. beyond nano's 7 ops | S | `++` needs lists; shifts see H5:13 |
| 4 | non-assoc 50: `== != < > <= >= ≤ ≥ ∣` | H5:3 `infixTable_lean` | proved+runner-built | `!= > >= <=`; `a<b<c` is a parse error | S | none |
| 5 | UInt64 `x/0=0`, `x%0=x` | H5:12 `u64_div_zero, u64_mod_zero` | proved+runner-built | `/` `%` with no zero check | S | H5:1 |
| 6 | UInt64 `==` `<` `≤` ↔ Nat compare | H5:11 `u64_beq_iff, u64_lt_iff, u64_le_iff` | proved+runner-built | unsigned comparison lowering | S | H5:3 |
| 7 | `abbrev` = `def` + {inline, reducible} | H7:1 `abbrev_is_def, abbrev_attrs, abbrev_mods` | proved+runner-built | `abbrev` keyword as alias of `def` | S | none |
| 8 | UInt64 literal pattern | H9:5 `u64_lit_shape` | proved+runner-built | `match x with \| 0 => ..` on UInt64 | S | one shape only |
| 9 | literal chain + `_` | H9:2 `lits_shape` | proved+runner-built | multi-literal `match` = if-chain | S | one shape only |
| 10 | `none`/`some x` patterns | H9:7 `option_shape` | proved+runner-built | Option match | S | one shape only |
| 11 | operator = instance function (UInt64 ops, `&&` `\|\|` `!=` ...) | H5:10 `u64_* ... or_false (rfl)` | proved+runner-built | op id -> Lean function link | S | trivial (rfl) |
| 12 | tuple pattern | H9:6 `prod_shape` | proved+runner-built | `(a,b)` patterns = destructure | S | rfl, one shape |
| 13 | Nat `0 / n+1` alts | H9:1 `succ_shape` | proved+runner-built | `match n with \| 0 \| n+1` | S | Nat patterns; nano is UInt64-only |
| 14 | as-pattern `x@p` | H9:4 `as_shape` | proved+runner-built | `x@pat` | S | one shape only |
| 15 | offset `n+2` | H9:3 `succ2_shape` | proved+runner-built | `n+k` patterns | S | H9:1 |
| 16 | `!`/`?` words need no reserved entry | H4:3 `reserved_wordlike_or_punct` | proved+runner-built | `assert!` `by?` need no list row | S | H4:1 |
| 17 | list words are Lean-shaped (sanity) | H4:4 `reserved_lean_shaped` | proved+runner-built | sanity only | S | H4:1 |
| 18 | ident vs token at equal length | H4:11 `fun_is_token` | proved+runner-built | semantics behind M6 | S | restated copy of private `isToken` |
| 19 | hex digit byte | H2:1 `hex_iff` | proved+runner-built | `\x`, `\u`, `0x` digits | S | none |
| 20 | one-byte escapes `\\ \" \' \r \n \t` | H2:2 `quotable_iff` | proved+runner-built | string/char escapes | S | none |
| 21 | `\xHH` stored bytes: accept only HH<0x80 | H2:5 `x_ascii, x_high` | proved+runner-built | `\xHH` with no UTF-8 surprise | S | none |
| 22 | `\uHHHH` value; reject D800–DFFF | H2:6 `u_val, u_surrogate, u_len` | proved+runner-built | `\u` escapes | S | surrogate trap (§3) |
| 23 | right-assoc `^ :: ∘ <$>` | H5:2 `infixTable_lean` | proved+runner-built | exponent, cons, compose | S | `::` and `<$>` need lists/functors; `1 + 1 :: []` is a Lean type error |
| 24 | `&& \|\| ^^ ∧ ∨ ×` rows | H5:4 `infixTable_lean` | proved+runner-built | Bool connectives | S | short-circuit codegen (M); `^^` name not found, see H5:7 |
| 25 | pipes `<\|` (10,0,10), `\|>` (10,0,11) | H5:6 `pipes_lean, pipe_app (rfl)` | proved+runner-built | `f <\| x`, `x \|> f` | S | application exists; `\|>.` not covered |
| 26 | prefix `-` `~~~` `!` `¬` | H5:5 `prefixTable_lean` | proved+runner-built | unary `!`, `~~~` | M | new prefix production in ParSpec |
| 27 | `_` wildcard vs identifier | H9:16 `underscore_isIdFirst, underscore_isIdRest` | proved+runner-built | test `isWild` before name; `_x` stays a name | S | none |
| 28 | separators `\| , => @ +` end a word | H9:17 `sep_not_idRest, as_split` | proved+runner-built | `x@p`, `n+1` tokenise | S | none |
| 29 | exhaustiveness: `covers` (candidate model only) | H9:10 `covers_total` | proved+runner-built | nano may reject non-covered `match` (sound) | S | Lean's checker not modelled; thin |
| 30 | `termination_by f` measure decrease | H9:12 `decr_measure, decr_wf, decr_pred` | proved+runner-built | measure-decreasing recursion accepted | S | explicit measure only |
| 31 | lexicographic `termination_by (a,b)` | H9:13 `lexDecr_lex` | proved+runner-built | Ackermann-style recursion | S | H9:12 |
| 32 | WF fixpoint unfold equation | H9:14 `fix_unfolds` | proved+runner-built | unfold equation of WF defs | S | H9:12 |
| 33 | `fun \| p => e` desugar | H9:8 `fun_alts_shape` | proved+runner-built | `fun` with alts | S | one shape only; general desugar is a macro |
| 34 | multi-discriminant `\| p, q =>` | H9:9 `two_disc_shape` | proved+runner-built | `match a, b with` | M | one shape only |
| 35 | letter-like chars (equality, every Char) | H3:1 `letterLike_eq` | proved+runner-built | `α ℕ 𝔸` in names | S | needs UTF-8 decode step in lexer (H3:6-8) |
| 36 | subscript chars | H3:2 `subScript_eq` | proved+runner-built | `x₁ xₐ` | S | H3:1 |
| 37 | identifier first char (all code points) | H3:3 `idFirst_eq, idFirstC_imp` | proved+runner-built | non-ASCII idents | S | H3:1 |
| 38 | identifier rest char | H3:4 `idRest_eq, idRestC_imp` | proved+runner-built | non-ASCII ident tails | S | H3:1 |
| 39 | holes `λ Π Σ × ÷` excluded | H3:5 `holes` | proved+runner-built | `λx`, `a×b` not names | S | free |
| 40 | `.` is not an id char | H3:14 `dot_not_idRest` | proved+runner-built | dotted split unambiguous | S | free |
| 41 | UTF-8 2-byte decode | H3:6 `dec2_eq` | proved+runner-built | reading `α` `«` | S | narrow guard |
| 42 | UTF-8 3-byte decode (E1..E2 only) | H3:7 `dec3_eq` | proved+runner-built | `x₁`, `ℕ` | S | narrow guard: E0/ED/EE/EF omitted |
| 43 | UTF-8 4-byte decode (F0 9D 92..96 only) | H3:8 `dec4_eq` | proved+runner-built | `𝔸 𝕜` | S | narrow guard |
| 44 | byte rule ⇒ identifier char | H3:9 `idRest2, idRest3, idFirst2` | proved+runner-built | actual lexer-shaped statement | S | H3:6-8 |
| 45 | `«` `»` = C2 AB / C2 BB | H3:10 `escOpen_lean, escClose_lean, esc_unique` | proved+runner-built | `«my name»` | S | H3:6 |
| 46 | dotted name text | H3:12 `toString_mkName` | proved+runner-built | `A.b.c` as a Name | S | none |
| 47 | name root | H3:13 `getRoot_mkName` | proved+runner-built | namespace/root-clash check (M8) | S | H3:12 |
| 48 | escaped component text | H3:11 `escapePart_force, escapePart_force_none` | proved+runner-built | what `«…»` denotes | S | force=true only |
| 49 | reserved list ⊇ identifier atoms of 73 Init syntax constants | H4:5 `init_atoms_reserved` | proved+runner-built | list provenance from Lean data | S | H4:1; needs H4:6 infrastructure |
| 50 | longest-match table for future tokens (`\|>. <\|> <- ← => :: ++ ∘ ⟨ ⟩ #[ fun λ`) | H4:9 `find_longest, tab_sorted, tab_munch` | proved+runner-built | operator/token munching order | S | nano side only; Lean's `matchPrefix` is partial |
| 51 | prefix pairs needing care | H4:10 `prefixPairs_eq` | proved+runner-built | only 2 shadowing pairs | S | H4:9 |
| 52 | precedence rows `++ :: ∘ <\| \|> <\|> >>= <$>` | H4:12 `rows_eq_lean, assoc_table, pipes_weakest` | proved+runner-built | Lean's numbers for ParSpec.opInfo | M | parser cases + semantics per op (overlaps H5) |
| 53 | array literal `#[a, b]` shape | H4:13 `arrayLit_shape` | proved+runner-built | future `#[` literal | M | lists/arrays in nano |
| 54 | `String.trimAscii` of unpadded token literal | H4:6 `trimAscii_copy, fun_trim, anon_trim, anon_token` | proved+runner-built | token/firstTokens facts for `fun ⟨ do` | S | infrastructure (§5) |
| 55 | padded token literals (`" :"` `" with "` `" => "` `"← "`) | H4:7 `trimAscii_cert, colon_trim, with_trim, arrow_trim, larrow_trim, with_token, fun_tokens, larrow_tokens, arrow_firstTokens` | proved+runner-built | token facts for `fun ← =>` | S per literal | certificates per literal only (§5) |
| 56 | `example` view | H7:4 `example_view` | proved+runner-built | `example` as no-op item | S | none |
| 57 | signature split (binders, optional `: T`) | H7:5 `optDeclSig_none/some, declSig_eq (rfl)` | proved+runner-built | explicit binder/type headers | S | concrete node shapes only |
| 58 | `def` child layout | H7:2 `def_view` | proved+runner-built | node shape for `pDef` | S | documentation value |
| 59 | def-like kinds | H7:6 `isDefLike_kinds` | proved+runner-built | which decls share def path | S | none |
| 60 | modifier defaults | H7:7 `default_modifiers` | proved+runner-built | spec of "no modifier" | S | none |
| 61 | modifier slots exclusive | H7:8 `partial_nonrec_exclusive, meta_noncomputable_exclusive` | proved+runner-built | reject `partial nonrec`, `meta noncomputable` | S | none |
| 62 | attribute order | H7:9 `addAttr_attrs, addFirstAttr_attrs` | proved+runner-built | `@[a, b]` | S | none |
| 63 | `theorem` view (needs a type) | H7:3 `theorem_view` | proved+runner-built | accept/erase `theorem` | M | erasure is a design decision |
| 64 | `private` round trip | H7:10 `private_roundtrip` | proved+runner-built | justifies existing `private` skip | S | 4 concrete instances only; thin |
| 65 | `s!`/`m!` token shape | H2:7 `s_bang, m_bang` | proved+runner-built | `s!"…{e}…"` | M | expansion semantics |
| 66 | escape set in `s!"…"` (`esc` ∪ `{`) | H2:3 `quotable_interp_iff` | proved+runner-built | interpolated strings | S | H2:7 |
| 67 | `dec` of `\xHH`/escapes vs mirror | H2:4 `dec_sub_mirror` | proved+runner-built | exact escape semantics | M | mirror is hand-transliterated; real fn `#guard`-tested only (opaque `String.Internal.get`) |
| 68 | parser-behaviour witnesses (assoc, cross-level, `!`) | H5:9 `sub_left … pipe_arith` | proved+runner-built | regression anchors for new Pratt table | S | concrete inputs only; thin |
| 69 | first body byte after `/-` consumed unexamined | H10:5 `blockEndX_eq, F2` | local-only | closes bug F2 | S | spec change in `step`/`docWs`; selfhost_gate |
| 70 | whitespace after doc-comment opener (tab/CR reject) | H10:6 `docWsFix_eq_lws, F1_fix_rejects` | local-only | closes bug F1; `/-- -/`, `/-! -/` | S–M | re-prove lexer lemmas that mention `docWs`; mirror |
| 71 | `namespace`/`section`/`end` balance | H10:7 `nanoEnd_sound, nameOf_numParts, nameOfScopes_take, F3` | local-only | checked `end` instead of line skip; closes F3 | M | scope stack in lexer state; mirror |
| 72 | decimal with `_` (`1_000_000`) | H1:5 `decUs_toNat?` | local-only | `_` separators | S–M | lexer + `decVal` skips `_`; single `_` between digits only |
| 73 | wrap to UInt64 for any radix | H1:6 `runU_eq, runU_lean` | local-only | `0x/0b/0o/_` literal value | S | H1:1,3,5 |
| 74 | hex digit class | H1:1 `isHex_eq_lean` | local-only | `0x` digits | S | overlaps H2:1 |
| 75 | hex digit value | H1:4 `hexVal_digitChar` | local-only | `0x`, `\xHH`, `\uHHHH` | S | overlaps H2:1 |
| 76 | bin/oct digit classes | H1:3 `bin_oct_dec_hex` | local-only | `0b`, `0o` | S | inclusion only; exact set transcribed |
| 77 | char escape set | H1:8 `escVal_eq_lean` | local-only | `'\n'` | S | overlaps H2:2 |
| 78 | `\uHHHH` via `Char.ofNat` | H1:11 `ofNat_u16` | local-only | avoid silent NUL | S | overlaps H2:6 |
| 79 | byte vs Char width | H1:10 `utf8Size_byte` | local-only | reject bytes ≥128 in `'…'` | S | side condition |
| 80 | char literal body decode | H1:9 `litDec_quoteCore, litDec_hex` | local-only | `'a'`, `'\n'`, `'\x41'` | M | new token kind; `'` also starts nano names (M7) |
| 81 | `let mut x := a; x := f x` | H8:1 `reassign_lean` | local-only | mutable locals | S | desugar to `let` chain |
| 82 | `let y ← e` in Id | H8:5 `bind_id_lean` | local-only | `←` as `let` | S | Id only |
| 83 | statement `if c then x := .. else x := ..` | H8:3 `if_stmt_lean` | local-only | stmt-level `if` | S | H8:1 |
| 84 | `unless` | H8:2 `unless_lean` | local-only | `unless` | S | H8:1 |
| 85 | `if let some y := o` | H8:4 `ifLet_lean` | local-only | `if let` on Option | S | Option only |
| 86 | doSeq item list | H8:10 `items_eq_lean, indent_items` | local-only | `{a; b}` ≡ indented block | S | none |
| 87 | `let mut` flag | H8:11 `isMut_eq_lean` | local-only | recognise `mut` | S | none |
| 88 | expression statement | H8:12 `exprOf_eq_lean` | local-only | doExpr shape | S | none |
| 89 | `for a in xs do x := g a x` | H8:6 `for_fold_lean` | local-only | plain `for` | M | lists/loops in nano IR |
| 90 | `for` with break/continue/return | H8:7 `forIn_list_eq` | local-only | loop exits | M | H8:6 |
| 91 | `for i in [lo:hi]` | H8:8 `forIn_range_eq` | local-only | counted loops | M | H8:6; step 1 only |
| 92 | `while`/`repeat` (subset form via nano fuel) | H8:9 `runW_imp_lean, while_lean` | local-only | `while` | M | termination witness required; nano run must finish |
| 93 | beta/paren/ascription/`show … from` | H6:9 `fun_app, paren_ascr, show_from (rfl)` | local-only | `fun`, `(e : T)`, `show` | S | trivial rfl; Lean must still accept the form |
| 94 | `have`/`let`/`let (x,y)` | H6:10 `have_beta, let_beta, let_pair (rfl)` | local-only | `have` | S | trivial rfl |
| 95 | tuple nest, `⟨a,b⟩`, `()`, `·` sections, curried app | H6:11 `tuple_nest, anon_pair, anon_triple, unit_tuple, pipe_app, cdot_fun, app_curry (rfl)` | local-only | anon ctor / n-tuples / `(· + 1)` | S–M | parser + typing |
| 96 | token bytes `λ ↦ ⟨ ⟩ ·`, `fun => show from have` | H6:5 `newTokBytes_eq` | local-only | UTF-8 bytes of new tokens | S | none |
| 97 | non-ASCII punct never id chars | H6:6 `punct_not_ident` | local-only | word boundary at `⟨ λ` | S | overlaps H3 |
| 98 | `λ Π Σ` excluded from letter-likes | H6:7 `greek_exceptions` | local-only | `λx` binder | S | duplicate of H3:5 |
| 99 | `fun show from have` word-shaped | H6:8 `kw_are_words` | local-only | why M6 matters | S | H4:1 |
| 100 | infix rows (pipes, `∘ <$> >>= :: ++ && \|\| ∧ ∨`) | H6:1 `AppOps.infixRows_eq_lean` | local-only | same as H5:1-6 | S | duplicate of H5/H4:12 |
| 101 | associativity classes | H6:2 `assoc_shape` | local-only | loop direction per op | S | duplicate of H4:12 |
| 102 | `f $ x` (needs trailing whitespace) | H6:3 `dollar_lean` | local-only | `$` lexing | S | H5:8 could not do this |
| 103 | prefix `!b`, `¬p` | H6:4 `prefix_lean` | local-only | Bool negation | S | duplicate of H5:5 |
| 104 | doc opener tokens `/--` `/-!` | H10:3 `docopen_eq + `#guard`` | local-only | `/-- -/`, `/-! -/` module docs | S | `Parser.info` guard is interpreter-only |
| 105 | nested block comment end | H10:4 `blockEnd_eq_fcb` | local-only | nested comments exact | — | mirror; nothing new |
| 106 | `--` line comment | H10:2 `line_eq` | local-only | exact | — | mirror; nothing new |
| 107 | whitespace chars (tab/CR rejected) | H10:1 `ws_skip_eq, ws_nano_not_tab_cr` | local-only | nothing new | — | none |
| 108 | precedence constants | H10:9 `prec_consts` | local-only | nothing new | — | none |
| 109 | decimal digit class | H1:2 `isD_eq_lean` | local-only | already in nano | — | none |
| 110 | radix value inverse of `Nat.toDigits` | H1:7 `runVal_toDigits` | local-only | sanity only | — | not an equality with `decodeNatLitVal?` |
| 111 | nano copies equal nano's own (`isW isD kwWords`) | H4:16 `Link: isW_copy isD_copy kw_copy kw_reserved` | drafted | ties standalone files to real lexer | S | needs nano chain build (slot) |
| 112 | decl-head keywords / modifiers; extra heads nano must reject | H7:11 `nanoHeads_sub, nanoMods_sub, declaration_first, modifiers_first` | drafted | reject `coinductive public meta scoped local opaque axiom class` | S | `#guard` only; re-run per Lean bump |
| 113 | clause keywords/symbols (`extends where deriving := \| =>`) | H7:12 `structure_kw … inductive_sym` | drafted | token sets for structure/inductive | S | `#guard` only |
| 114 | command keywords `namespace section end open universe set_option variable` | H10:8 ``#guard` in Tokens.lean` | drafted | `lineKw` words are Lean tokens | S | interpreter only |
| 115 | do-keywords (`break continue return while repeat until unless for in mut ← else do`) | H8:13 `Keywords.lean `#guard`s` | drafted | reserved list for new syntax | S | interpreter only (`trimAscii` stuck) |
| 116 | `fun` bodies, `show … from/by`, tuple `,`, ascription `:`, app `..` | H6:13 `Shapes.lean `#guard`` | drafted | keyword slots of each form | S | `#guard` only |
| 117 | first tokens + node kinds of paren/tuple/ascr/⟨⟩/fun/show/have/let | H6:12 `Shapes.lean `#guard`` | drafted | `(`-form dispatch needs lookahead | M | `#guard` only |
| — | `decodeNatLitVal?` equality | H1:12 | not provable | `partial` aux; stays with fuzzer | — |  |
| — | tokenizer digit run `takeDigitsFn` | H1:13 | not provable | accepts `1__2`, `0x_1` (trap) | — | `partial` |
| — | prefix dispatch `0x/0b/0o` | H1:14 | not provable | data only | — | `ParserFn` |
| — | decimal followed by `.`/`e`/`E` | H1:15 | not provable | scientific literal hazard | — | `ParserFn` |
| — | char literal tokenizer `charLitFnAux` | H1:16 | not provable | accepts `'''`, raw newline | — | `ParserFn` |
| — | string/`\u`/scientific decoders | H1:17 | not provable | not attempted | — | `partial` |
| — | `f!` token shape | H2:8 | not attempted | same shape by source | — | name `«termF!_»` not checked |
| — | plain string literal scan/decode | H2:9 | not provable | only per-escape leaves | — | `partial` + opaque `String.Internal.*` |
| — | char literal | H2:10 | not provable | fuzz | — | opaque `String.Internal.get` |
| — | raw strings `r#"…"#` | H2:11 | not provable | fuzz | — | `partial` |
| — | string gap `\⏎ ws*` | H2:12 | not provable | parser: exactly one newline; decoder: any ws | — | `partial` |
| — | `String.quote` / `Char.quoteCore` output | H2:13 | not provable | printing | — | `String.Internal.append` opaque |
| — | identifier lexing `identFnAux`, `mkIdResult` | H3:15 | not provable | cut point is fuzz-only | — | `partial` |
| — | `x.1`, `x.«a»`, `a.b` after-dot rules | H3:16 | not provable | fuzz | — | `partial` |
| — | keyword vs name token table | H3:17 | not provable | M6 stays open (H4:1 narrows it) | — | IO.Ref |
| — | macro scopes / `✝` | H3:18 | not provable | irrelevant (`✝` not in table) | — |  |
| — | name resolution | H3:19 | not provable | M4, M5, M8 | — | environment |
| — | builtin keywords via `collectTokens` closures | H4:8 | not provable | partly unblocked by H4:6; whole-parser lists need `withAntiquot`/`andthen` unfolding + padded lemma | — | token table is runtime |
| — | `fun`, `⟨⟩`, `←`, `\|>.` as builtin Parser closures | H4:14 | not provable | token spellings only | — | closures |
| — | Pratt loop `trailingLoop` | H4:15 | not provable | edge | — | `partial` |
| — | `^^` Bool xor (L33) | H5:7 | not attempted | dropped: `«term_^^_»` not found by that name | — | find the name |
| — | `$` pipe | H5:8 | not provable | covered by H6:3 (local-only) | — | `.unary` wrapper, partial ws check |
| — | shift counts mod 64 (`<<<` `>>>`) | H5:13 | not attempted | `<<<` with count ≥64 | — | BitVec lemma hunt |
| — | `<`/`>` tokens, `\|>.`, `<;>`, `$`, `←`, `·` sections | H5:14 | not provable | edge | — | `partial`/ParserFn |
| — | node precedences (`fun` maxPrec, `have`/`show` leadPrec, app arg) | H6:14 | not provable | which forms need parens as args; fuzz | — | `leading_parser` closure |
| — | paren/tuple/ascription choice; `fun` binders; `have` letDecl; colGt | H6:15 | not provable | fuzz | — | `ParserFn` |
| — | elaboration: binder types, `⟨⟩` expected type, `show` check | H6:16 | not provable | nano must reject what it cannot type | — | elaborator |
| — | modifier ORDER | H7:13 | not provable | literal rank table + fuzz | — | closure; `firstTokens` merges slots |
| — | `deriving` handlers | H7:14 | not provable | per-class instance proof, not syntax | — | IO.Ref |
| — | structure/inductive elaboration | H7:15 | not provable | L, outside harvest | — | `TermElabM` |
| — | `elabModifiers`, `expandDeclId`, `mkDefView` dispatch, instance naming | H7:16 | not provable | fuzz | — | `CommandElabM` |
| — | doc comment `/-- -/` body | H7:17 | not provable | fuzz | — | `partial` |
| — | grammar of `for`/`while`/`return` | H8:14 | not provable | fuzz only | — | closures, layout |
| — | `try/catch/finally`, do-`match`, `let rec`, nested `(← e)` | H8:15 | not provable | conservative rejection | — | monadic elaborator |
| — | redundant/overlapping alt | H9:11 | not provable | stricter nano rule is safe | — | elaborator error |
| — | `termination_by`/`decreasing_by` syntax; GuessLex | H9:15 | not provable | require explicit measure or ignore | — | ParserFn / elaborator |
| — | matchAlt grammar shape | H9:18 | not provable | fuzz only | — | `checkColGe` state |
| — | `open … in/hiding/renaming`, `variable`, `universe`, `set_option` effects | H10:10 | not provable | conservative rejection; M4/M5 risk | — | environment |
| — | command terminator / position (`checkColGt`, `ppDedent`) | H10:11 | not provable | fuzz | — | `partial`, ParserState |
## 3. "Nano must reject" traps

Lean accepts (or silently mangles) these; nano's candidate rules must be at least as strict.

- `\uD800`–`\uDFFF`: `Char.ofNat` yields `'\0'` silently (H1:11 `ofNat_u16`, H2:6 `u_surrogate`). Reject.
- `\xHH` with HH ≥ 0x80 is U+00HH = 2 UTF-8 bytes (H2:5 `x_high`); source bytes ≥ 128 inside `'…'` are a UTF-8 sequence, not one `Char` (H1:10). Reject both.
- `1__2`, `0x_1`: Lean's `takeDigitsFn` accepts, `String.toNat?` rejects `1__2`. Use the stricter single `_` between digits (H1:5, H1:13).
- Scientific literals: decimal followed by `.`/`e`/`E` (`1e5`, `1.5`, `1..2`) is a different token; nano must not lex `1e` as numeral + ident (H1:15).
- `0b1`, `0o7`, `0xe` start prefixed numerals in Lean but nano today lexes `0` + name `b1`; existing programs may already differ; check before enabling (H1 mismatch 4).
- `'''` and a raw newline inside a char literal: Lean's tokenizer takes them; nano rejecting is safe (H1:16, H2:10).
- No `\u{…}`, `\0`, `\a` in Lean; `\u` takes exactly 4 hex digits (H2 header). Note: H2:4 is titled "decode of `\e`" while the header says `\e` does not exist; re-check before adding `\e`.
- String gap `\⏎ ws*`: parser needs exactly one newline, decoder accepts any whitespace; nano should reject gaps (H2:12).
- Tab and lone CR are errors in Lean whitespace (H10:1); keep rejecting. Tab/CR right after a `/--` opener is also an error (F1).
- Decl heads/modifiers present in 4.34.1 that nano must still reject: `public`, `meta`, `coinductive`, `scoped`, `local`, `opaque`, `axiom`, `class`; `requires`/`ensures` contract clauses on `def`; `partial_fixpoint`/`termination_by` tails (H7 notes, H7:11).
- Reserved words are not names: 168 words nano accepted as identifiers (H4:1); `with_annotate_term` is NOT reserved (`scoped`) and stays a legal name; `fun1`, `at'` stay names (H4:2).
- `λ Π Σ × ÷` are not letter-like: `λx` must lex as binder, `a×b` as operator (H3:5, H6:7).
- UTF-8 decoders must reject E0/ED/EE/EF lead bytes and overlongs beyond the table blocks (H3:7 narrow guard).
- Operator traps: `::` (67) binds tighter than `+` (65), so `1 + 1 :: []` is a Lean type error (H5); non-assoc 50 means `a < b < c` is a parse error (H5:3); `!a == b` is `!(a == b)` but `!a && b` is `(!a) && b` (H5:5, H6:4); `$` is a pipe only when followed by whitespace, else antiquotation (H6:3).
- `have`/`show` are not application arguments, `fun` is (H6:14, fuzz only).
- `while`/`repeat`: Lean may diverge; nano must demand a terminating witness (H8:9). `termination_by`: require an explicit measure; Lean may infer one (H9:15).
- `match`: rejecting non-covered or redundant alts is sound (H9:10, H9:11).
- `\|>.`, `<;>`, `←`-do, `·` sections: not provable; only token spellings are known (H5:14, H4:14).
- `open … in/hiding/renaming`, `variable`, `universe`, `set_option` change meaning through the environment; nano skips `open` lines, so a later name clash is the Lean-side risk (M4/M5, H10:10).
- `theorem` erasure and `deriving` are design/instance questions, not syntax (H7:3, H7:14).

## 4. Bugs: nano accepts, Lean rejects (H10 F1–F3)

All reproduced with the real `lean` 4.34.1 (H10). Each: **queued on syntax-1**.

| id | input | Lean | nano `LexSpec.step` | proved fix | status |
|---|---|---|---|---|---|
| F1 | `/--<TAB>foo -/` then `def x` (tab or lone CR after the `/--` opener) | `error: tabs are not allowed` | accepts (`docWs` stops at the tab) | `docWsFix_eq_lws`, `F1_fix_rejects` | queued on syntax-1 |
| F2 | `/-/- -/ -/` then `def x` | comment ends at the FIRST `-/` (`whitespace` consumes the byte after `/-` unexamined, Basic.lean:578); then `-/` is unexpected | accepts (`blockEnd 0` nests on that byte) | `blockEndX_eq`, `docWsFix_eq_lws` | queued on syntax-1 |
| F3 | stray `end` / `end Foo` with no open scope | `invalid 'end', insufficient scopes` | `lineKw` skips the line | `nanoEnd_sound`, `nameOf_numParts`, `nameOfScopes_take` | queued on syntax-1 |

Caveats: the proved fixes are against H10's fuel mirrors of `whitespace`/`finishCommentBlock`/`elabEnd` (transcribed from `partial`/monadic code), not the Lean functions themselves. F2 also has a harmless reverse (`/-/- -/` Lean accepts, nano rejects). F1/F2 fixes change `step`/`docWs` (selfhost_gate; lexer lemmas mentioning `docWs` must be re-proved). F3 needs a scope stack in lexer state.

## 5. Cross-cutting blockers

| blocker | what it blocks | how far solved |
|---|---|---|
| `String.trimAscii` not kernel-reducible (`symbol` stores `"x".trimAscii.copy`; `decide +kernel`/`rfl` stuck) | any `Parser.info`/`collectTokens` table as a theorem; H6:12–13, H7:11–12, H8:13, H10:3/8 are `#guard`s because of it | **Partly.** H4:6 (unpadded, `trimAscii_copy` by equation lemmas; `⟨ fun do`) and H4:7 (padded, per-literal certificates `colon_trim with_trim arrow_trim larrow_trim`, each fact by `decide +kernel`), both runner-built. **Open:** variable `s` in `(" " ++ s ++ " ").trimAscii.copy = s` (needs Pos/Splits lemmas; no `get` lemma for `sliceFrom`); whole-parser lists need `withAntiquot`/`andthen` unfolding. The `#guard` rows in H6/H7/H8/H10 have not been migrated to it. |
| `String.Internal.get/next/atEnd/append` are `opaque` `@[extern]` | every Lean decoder taking a `String` (`decodeQuotedChar`, `decodeCharLit`, `decodeStrLit`, `decodeStringGap`), `Char.quoteCore` on controls | **Not solved.** Only per-escape leaves (H1/H2 predicates, `Char.ofNat`, value semantics) are proved; `dec_sub_mirror` (H2:4) is a hand mirror, real function `#guard`-tested only. |
| `leading_parser` closures (no `ParserDescr` data) | node precedences, `(`-form choice, `fun` binders, `do`/`match` grammar, modifier order | **Not solved.** Worked around by proving the semantics Lean gives each shape (H6 `rfl` desugars, H8 `Id.run do … = rule`, H9 `match` shapes) and, for token spellings, H4:6-7. Node precedences and layout (`checkColGe`) are fuzz-only. |
| `partial` tokenizers/parsers (`whitespace`, `takeDigitsFn`, `identFnAux`, `strLitFnAux`, `trailingLoop`, `matchPrefix`) | lexer equality for numerals, idents, strings, comments | **Mirrors only.** H10 fuel mirror (`fcb`, `lws`), H2 list mirror, H4:9 nano-side longest-match; mirror fidelity is transcription + differential runs. `while` uses Lean's public `Loop.forIn_eq_of_monadTail` (H8:9). Digit runs, identifier cuts, string scans: fuzz. |
| Elaborator/environment (`open`, name resolution, typing, `deriving`) | M4/M5/M8, binder types, instance names | Not provable; nano must reject conservatively. |

## 6. Recommended first fold-in batch

Ten rows, all proved+runner-built, S effort, each adds syntax nano lacks or closes a known hole:

1. **H4:1** reserved-word list (closes M6) — add the 190 words as a lexer table; lookup proof.
2. **H4:2** `w ++ "1"` / `w ++ "'"` stay names — companion of 1.
3. **H5:1 (UInt64 subset)** `^^^ / % <<< >>>` rows into `opInfo`; leave `++` until lists exist; shifts only after H5:13 (count ≥ 64) is settled, so take `^^^ / %` first.
4. **H5:3** comparisons `!= > >= <=` (non-assoc 50; chained comparison is a parse error).
5. **H5:11** UInt64 compare = Nat compare — lowering for 4.
6. **H5:12** `x/0=0`, `x%0=x` — no zero check for `/` `%`.
7. **H7:1** `abbrev` as `def` (one kwTable row).
8. **H9:5** UInt64 literal pattern.
9. **H9:2** literal chain + `_`.
10. **H9:7** `none`/`some x` patterns.

Next after that: H9:6 tuple patterns, H9:16–17 (`_`, separators), H2:1/2/5/6 string/char escapes with the surrogate and ≥0x80 rejects, then H3 identifiers (needs the UTF-8 decode step).
Caveats: H9:1–3 are Nat patterns (nano is UInt64-first); H9 theorems are one-shape facts, so each pattern still needs its own nano-side proof; H5:2/4 rows with `::`, `<$>`, `^^` need lists/functors or a name fix. Local-only rows with the best value once built: H10:5–7 (close F1–F3), H1:5–6 (`_` separators, `0x` literals), H8:1–5.
