# Harvest/H9: patterns, `match`, `fun |`, termination hints (Lean 4.34.1)

Build: slot 10 (4de2d52e) PASS, axioms OK. Standalone (Init only, no nano imports). Local check: `lean Harvest/H9/<File>.lean` (all three compile, axioms in `REVIEW.lean`:
only `propext`/`Quot.sound`). Lean refs are `src/` at tag v4.34.1.
Method note: `match`, `matchAlts`, `termination_by` are builtin `leading_parser`s (ParserFn, not `ParserDescr` data) and the matcher
compilation is MetaM. So the theorems are about the **semantics Lean gives each shape** (Lean's own `match` appears in the statement), not about the parser.
Candidate model (`Match.lean`): `P` = `any | lit k | succ p | as p`, `evalAlts` = first-match-wins.

| feature | Lean def | candidate nano rule | theorem | status | value for nano | effort |
|---|---|---|---|---|---|---|
| Nat `0 / n+1` alts | Init/Prelude Nat.casesOn via `match` | `evalAlts [lit 0, succ any]` | `succ_shape` | proved+built | `match n with \| 0 \| n+1` as a primitive | S: decide/branch on `n=0`, bind `n-1` |
| literal chain + `_` | `match` literal alts (Elab/Match.lean:1266) | `lit`s then `any` | `lits_shape` | proved+built | multi-literal `match` = if-chain | S |
| offset `n+2` | `Nat.add` patterns, Meta/Match/Match.lean `expandNatValuePattern` | `succ (succ any)` | `succ2_shape` | proved+built | `n+k` patterns | S |
| as-pattern `m@(k+1)` | `Pattern.as` (Meta/Match/Basic) | `as p` binds scrutinee first | `as_shape` | proved+built | `x@pat` | S |
| UInt64 literal pattern | `match x with \| 0 => ..` | `x = k` test | `u64_lit_shape` | proved+built | match on `UInt64` literals | S |
| tuple pattern | structure eta | project `.1 .2` | `prod_shape` | proved+built (rfl) | `(a,b)` patterns = `let`-destructure | S |
| `none`/`some x` | `Option.casesOn` | `(o.map f).getD d` | `option_shape` | proved+built | Option patterns | S |
| `fun \| p => e` | Parser/Term.lean:387 `basicFun <\|> matchAlts` | desugar to `fun x => match x with ..` | `fun_alts_shape` | proved+built (rfl, one shape; general desugar is a macro) | `fun` with alts | S (parser-side macro) |
| multi-discriminant `\| p, q =>` | Parser/Term.lean:266 `matchAlt` (`sepBy1 term ","`) | nested first-match | `two_disc_shape` | proved+built (one shape) | `match a, b with` | M |
| exhaustiveness | Meta `reportMatcherResultErrors` ("Missing cases") | `covers`: some alt irrefutable | `covers_total` | proved+built for the candidate model only; Lean's checker is elaborator-only (not provable) | nano may reject non-covered `match` (sound subset: Lean accepts) | S |
| redundant/overlap alt | `lean.redundantMatchAlt` | reject alt after irrefutable | none | **not provable**: elaborator error. Stricter nano rule is safe (subset) | none | n/a |
| `termination_by f` | Init/WF.lean:267 `measure`, :189 `invImage` | `decr f b a := f b < f a` | `decr_measure`, `decr_wf`, `decr_pred` | proved+built | rule for accepting measure-decreasing recursion; nano subset ⊆ Lean | S |
| lexicographic `termination_by (a,b)` | Init/WF.lean:286 `Prod.Lex` | `lexDecr` | `lexDecr_lex` | proved+built | Ackermann-style recursion | S |
| WF fixpoint equation | `WellFounded.fix_eq` | none (instantiation) | `fix_unfolds` | proved+built | gives unfold equation Lean's compiled WF defs satisfy | S |
| `termination_by`/`decreasing_by` syntax | Parser/Term.lean:624, :702 (`"termination_by " >> optional "structural " ..`) | keyword shapes only | none | **not provable**: ParserFn; `decreasing_by` tactic block is elaborator-only; Lean may also *infer* a measure (GuessLex) | nano can require an explicit measure or ignore hints | n/a |
| `_` wildcard vs identifier | Init/Meta/Defs.lean:120 `isIdFirst`, :133 `isIdRest` | word = `[95]` is wildcard (`isWild`) | `underscore_isIdFirst`, `underscore_isIdRest` | proved+built | `_` is a legal ident char, so test `isWild` before name; `_x` stays a name | S |
| separators `\| , => @ +` stop a word | `isIdRest` | word lexer stops at them | `sep_not_idRest`, `as_split` | proved+built | `x@p`, `n+1`, `\| a, b =>` tokenise safely | S |
| matchAlt grammar shape | Parser/Term.lean:266-282 | token-shape recogniser | none | **not provable**: `leading_parser`, `checkColGe` column state | fuzz only | n/a |

Edge (not provable): which program Lean's elaborator *accepts* (match compilation, exhaustiveness, redundancy, type inference of patterns,
GuessLex, `decreasing_tactic`). nano ⊆ Lean here relies on nano being stricter, and the theorems fix the *value* semantics of accepted shapes.
Files: `Match.lean`, `Termination.lean`, `Tokens.lean`, `REVIEW.lean` (axiom prints). Lakefile has a `Harvest` lib on this branch only.
