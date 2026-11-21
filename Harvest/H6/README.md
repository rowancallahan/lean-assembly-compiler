# Harvest/H6: term-syntax leaves (fun, application, parens, tuple, ⟨⟩, ascription, show, have)

Standalone (imports `Lean` only). Lean 4.34.1; lean paths below are under `src/lean/`. All built with `lean -o` locally
(axioms ⊆ propext, Quot.sound, Classical.choice; none for the `rfl` ones; `REVIEW.lean` prints them); runner build: see bottom.

**Finding (the edge):** the builtin term parsers of this area (`paren`, `tuple`, `typeAscription`, `anonymousCtor`, `fun`, `show`,
`have`, `app`; Parser/Term.lean:183-235, 384-388, 559, 897) are `leading_parser` = `Parser` {info, fn}. No `ParserDescr`, so
their node precedences (`leadPrec`, `maxPrec`) live inside the `fn` closure: not data. `info` (first tokens, kinds) is data but the
kernel cannot evaluate it: `symbol` calls `String.trimAscii` and `example : (" (".trimAscii.copy == "(") = true := by decide +kernel`
fails (stuck; so does `rfl`). Hence rows 12-13 are `#guard` (compiled evaluation), not kernel theorems.

| # | feature | Lean def (file:line) | candidate nano rule | theorem | status | value for nano | effort |
|---|---|---|---|---|---|---|---|
| 1 | `f <\| x`, `x \|> f`, `∘`, `<$>`, `>>=`, `::`, `++`, `&&`, `\|\|`, `∧`, `∨` | Init/Notation.lean `«term_<\|_»` … (ParserDescr consts) | `infixRows`: (spelling, prec, lhsPrec, rhsPrec) read by a `pLoop` | `AppOps.infixRows_eq_lean` | proved+built (local) | pipeline/compose/bool-and-or operators: same table shape as `ParSpec.opInfo` | S per operator (lexer tag + opInfo row + Sem case) |
| 2 | associativity classes | same | rhs = prec ⇒ right, rhs = prec+1 ⇒ left | `AppOps.assoc_shape` | proved+built | `<\|` `∘` `::` right; `\|>` `++` `&&` `\|\|` left: no per-operator proof of loop direction | S |
| 3 | `f $ x` | Init/Notation.lean `«term_$__»` | `$` accepted only when followed by whitespace (`atomic (" $" >> ws)`) | `AppOps.dollar_lean` | proved+built | `$` lexing rule (otherwise antiquotation) | S |
| 4 | prefix `!b`, `¬p` | `term!_`, `«term¬_»` | prefix node 1024, operand at 40 | `AppOps.prefix_lean` | proved+built | Bool negation parse (operand 40 < comparison 50: `!a == b` needs parens) | S |
| 5 | token bytes `λ ↦ ⟨ ⟩ ·` + `fun => show from have` | `unicodeSymbol "λ" "fun"` etc. (Term.lean:386, 384) | lexer `opTable`/`kwTable` rows | `Bytes.newTokBytes_eq` | proved+built | exact UTF-8 bytes for new tokens | S |
| 6 | non-ASCII punctuation never identifier chars | `isIdFirst`/`isIdRest` Init/Meta/Defs.lean:120,133 | word scan stops at these chars | `Bytes.punct_not_ident` | proved+built | safe word boundary for `⟨x,y⟩`, `λx` | S |
| 7 | `λ Π Σ` excluded from letter-likes | `isLetterLike` Init/Meta/Defs.lean:101 | if Greek names are ever admitted, exclude these 3 | `Bytes.greek_exceptions` | proved+built | `λx => x` lexes as binder, not name | S |
| 8 | `fun show from have` are word-shaped | Term.lean | keyword table must beat `isW` | `Bytes.kw_are_words` | proved+built | shows why M6 (reserved words as names) matters for these 4 | S |
| 9 | beta / paren / ascription / `show … from` | Term.lean:183,201,228 | desugar form to RHS | `Desugar.fun_app`, `paren_ascr`, `show_from` | proved+built (`rfl`) | desugaring `fun`/`show`/`(e : T)` keeps Lean's value; Lean must still accept the form | S |
| 10 | `have`/`let`, pair `let (x,y) :=` | Term.lean:551,559 | `have x := v; b` ↦ `b[v/x]` | `Desugar.have_beta`, `let_beta`, `let_pair` | proved+built (`rfl`) | `have` for free once `let` exists | S |
| 11 | tuple nest, `⟨a,b,c⟩`, `()`; pipes; `·` sections; curried app | Term.lean:187,217 | `(a,b,c)` = `(a,(b,c))`; ⟨⟩ at product = tuple | `tuple_nest`, `anon_pair`, `anon_triple`, `unit_tuple`, `pipe_app`, `cdot_fun`, `app_curry` | proved+built (`rfl`) | anonymous constructor / n-tuples / `(· + 1)` as sugar over existing pair | S–M (parser + typing) |
| 12 | first tokens + node kinds of paren, tuple, ascription, ⟨⟩, fun, show, have, let | Term.lean:183-235,386,559 | `shapes`: leading token ↦ kind (dispatch table for `pAtom`) | `Shapes.lean` `#guard` | drafted (`#guard`, not kernel) | the leading tokens for `(`-forms disambiguation: `(`→ paren/tuple/ascription share one token, so dispatch needs lookahead | M |
| 13 | `fun` body forms (`=>`/`↦`, `\| alts`), `show … from/by`, tuple `,`, ascription `:`, `app` `..` | Term.lean:384-388,228,187,183,897 | token membership | `Shapes.lean` `#guard` | drafted (`#guard`) | confirms the keyword slots of each form | S |
| 14 | node precedences (`fun` maxPrec, `have`/`show` leadPrec, `app` trailing leadPrec:maxPrec, arg at argPrec) | Term.lean:386,559,228,897 | `have`/`show` not an application argument; `fun` is | none | **not provable**: `leading_parser:prec` prec sits in the `fn` closure | which forms need parentheses as arguments | fuzz only |
| 15 | how `(`…`)` chooses paren/tuple/ascription; `fun` binder grammar; `have` letDecl; `argument` colGt | `partial`/`ParserFn` closures; `checkColGt` Basic.lean:1496 | — | none | **not provable**: `ParserFn` state machines | — | fuzz (LEAN-DIFF) |
| 16 | elaboration: `fun` binder types, expected-type for `⟨⟩`, `show` type check | Elab/* | — | none | **not provable**: elaborator-only; nano must reject what it cannot type | — | conservative rejection |

Method as `Nano/LeanEquiv`: tables read from `ParserDescr` constants with `decide +kernel`; term identities by `rfl`.
`sym` in `AppOps` strips spaces because the kernel cannot run `trimAscii`. Files: `AppOps`, `Bytes`, `Desugar`, `Shapes`, `REVIEW`.
