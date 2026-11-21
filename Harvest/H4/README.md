# Harvest/H4: keywords, tokens, future infix operators vs Lean 4.34.1

Standalone (imports `Lean` only; `Link.lean` imports `Nano.Lexer.Lex2Spec`). Checked locally with `lean 4.34.1` per file;
axioms (`Review.lean`): `propext` / `Classical.choice` / `Quot.sound` only. Lean sources: tag v4.34.1.
Method as `Nano/LeanEquiv`: ParserDescr constants are data, so `decide +kernel` can compare them to a candidate table.

| feature | Lean def (file:line) | candidate nano rule | theorem | status | value for nano | effort |
|---|---|---|---|---|---|---|
| reserved words are not names (M6) | token table (runtime) `isToken` Parser/Basic.lean:934-941 | `identOK`: word bytes, not digit/`'`-led, not kw, not in `reserved` (190 words from LEAN_RULES §3) | `reserved_not_ident` | proved+built | closes M6 (168 accepted reserved names); 1-line lexer check | S: add the list as a table in Lex2 + proof it is not an identifier (lookup) |
| rule is not over-rejecting | `isToken`: token must be >= ident length | `w ++ "1"` and `w ++ "'"` stay names | `reserved_ext_ok` | proved+built | `fun1`, `at'` keep working | S |
| `!`/`?` words | `isIdRest` Init/Meta/Defs.lean:129-133 | `isW` has no `!` `?` | `reserved_wordlike_or_punct` | proved+built | `assert!` `by?` need no list entry | none |
| list words are Lean-shaped | `isIdFirst`/`isIdRest` | none (sanity) | `reserved_lean_shaped` | proved+built | only the token table keeps them from being names | none |
| list provenance from Lean data | `ParserDescr.symbol` atoms of 73 Init syntax constants (Init/Notation.lean, Tactics.lean, ...) | `reserved ⊇` identifier-shaped atoms | `init_atoms_reserved` | proved+built | list is derived from Lean's own declarations, not only from a fuzz run; shows `with_annotate_term` is `scoped` (not reserved) | S |
| builtin keywords (`def let fun match do ...`) | `Parser.Term.fun` etc: closures over `String.trimAscii` | none | none | not provable: `collectTokens` is stuck in the kernel (`trimAscii` is well-founded); token table is runtime | edge: list stays fuzz-derived (`lean_reserved_words.txt`) | - |
| longest match, future tokens `\|>. <\|> <- ← => \|> <\| :: ++ ∘ ⟨ ⟩ #[ ] fun λ` | `Trie.matchPrefix` Lean/Data/Trie.lean:168-193 (`partial`) | longest-first table + `find?` | `find_longest` (generic), `tab_sorted`, `tab_munch`, `munch_examples` | proved+built (nano side) | `\|>.` vs `\|>`, `<\|>` vs `<\|`, `<-` vs `<`: order rule and its proof | S (table + `find_longest` instance) |
| prefix pairs needing care | same | `prefixPairs` | `prefixPairs_eq` | proved+built | only two shadowing pairs in the future set | none |
| ident vs token at equal length | `isToken` (private; restated `isTokenL`) | length compare | `fun_is_token` | proved+built (restated copy; private def) | semantics of M6 | none |
| `++ :: ∘ <\| \|> <\|> >>= <$>` precedence | `«term_++_»` etc, Init/Notation.lean:272,292,427,430,528,552 | rows (bytes, prec, lhs, rhs) | `rows_eq_lean`, `assoc_table`, `pipes_weakest` | proved+built | add list append, cons, composition, pipes to `ParSpec.opInfo` with Lean's numbers (`<\|` lhs 0 rhs 10; `\|>` rhs 11) | M: parser cases + semantics per operator; the numbers are free |
| array literal `#[a, b]` | `«term#[_,]»` | node 1024, `sepBy term ", " allowTrailing`, `]` | `arrayLit_shape` | proved+built | shape of a future `#[` literal (trailing comma allowed) | M |
| `fun x => e`, `⟨a, b⟩`, `←`, `\|>.` | `Parser.Term.fun`, `anonymousCtor`, `doElem` are builtin `Parser` values (closures), not `ParserDescr` | none | none | not provable: only token spellings (above) and fuzzing | edge | - |
| how Lean's Pratt loop uses prec numbers | `trailingLoop` Parser/Basic.lean:1968 (`partial`) | `ParSpec.pLoop` | none | not provable (`partial`) | edge | - |
| nano copies equal nano's own | Lex2Spec.lean:18-37 | `isW isD kwWords` | `Link.lean`: `isW_copy isD_copy kw_copy kw_reserved` | drafted (needs nano chain build; slot request) | ties the standalone files to the real lexer | S |

Files: `Reserved.lean`, `Tokens.lean`, `Infix.lean`, `Review.lean` (`#print axioms`), `Link.lean`.
Finding: `Lean.withAnnotateTerm` is `scoped syntax`; its token is not reserved by default, so a name `with_annotate_term` is legal.
