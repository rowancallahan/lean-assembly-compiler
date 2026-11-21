# Harvest H5: operator notation table (Lean 4.34.1) — status: BUILT (slot 6, sha f2ae6fb, axioms pinned OK: propext, Quot.sound, Classical.choice)

Files: `Ops.lean` (descriptor tables), `Sem.lean` (parser-behaviour witnesses, macro shapes), `Wide.lean` (∀ UInt64 totality), `REVIEW.lean` (axioms).
Standalone (imports only Init). Method as `Nano/LeanEquiv/Prec.lean`: Lean's `«term_+_»`-style `ParserDescr` constants are data, so `decide +kernel` reads symbol/prec/lhsPrec/rhsPrec.
Candidate rule shape: `(spelling, prec, lhsPrec, rhsPrec)` with `L p=(p,p,p+1)`, `R p=(p,p+1,p)`, `N p=(p,p+1,p+1)`.
Lean sources: `Init/Notation.lean` (272-292 arith/bit/`∘`/`×`, 372-394 relations, 404-437 logic, `::`, `<$>`, `>>=`), `Init/Core.lean:775` (`!=`), `Init/Data/Bool.lean:30` (`^^`), `Init/Notation.lean:528-566` (pipes).

| feature | Lean def | candidate nano rule | theorem | status | value for nano | effort |
|---|---|---|---|---|---|---|
| `\|\|\|` L55 `^^^` L58 `&&&` L60 `+ - ++` L65 `* / %` L70 `<<< >>>` L75 | Notation.lean:277-292 | `infixTable` rows `L p` | `infixTable_lean` | proved+built | `^^^`, `/`, `%`, `++` (list/array append) beyond nano's current 7 ops | low: add rows to `opInfo`/`opTable` |
| `^` R80, `::` R67, `∘` R90, `<$>` R100 (right assoc) | 272, 291, 428 | `R p` | `infixTable_lean` | proved+built | exponent, list cons, composition | low (right-assoc loop `rhs=p`) |
| `== != < > <= >= ≤ ≥ ∣` non-assoc 50 | 372-394, Core:775 | `N 50` | `infixTable_lean` | proved+built | `!=` and `>`,`>=`,`<=` comparisons; non-assoc means `a < b < c` is a parse error | low |
| `&& L35, \|\| L30, ^^ L33, ∧ R35, ∨ R30, × R35` | 404-415, Bool:30 | `L`/`R` rows | `infixTable_lean` | proved+built | Bool connectives (short-circuit semantics in `Sem`) | low–med (codegen for short-circuit) |
| prefix `-` 75, `~~~` 100, `!`/`¬` max with operand 40 | 283-285, 407, 412 | `prefixTable` | `prefixTable_lean` | proved+built | unary `!`, `~~~`; `!a && b = (!a) && b` but `!a == b = !(a == b)` | med (new prefix production in ParSpec) |
| pipes `<\|` / `\|>` (min=10, lhsPrec 0) | 528, 552 | `(10,0,10)`, `(10,0,11)` | `pipes_lean` | proved+built | `f <\| x`, `x \|> f` desugar to application (`pipe_app`, rfl) | low once application exists |
| `^^` Bool xor (L33) | Init/Data/Bool.lean:30 | `L 33` | — | dropped: `«term_^^_»` constant not found under that name in this build (no Init import of it) | Bool xor | low, find the name |
| `$` pipe | 564 | — | — | not provable by this reader: `atomic(" $" ws)` is a `.unary` wrapper, partial whitespace check | skip | — |
| parser-behaviour witnesses (left/right assoc, cross-level order, `!`/`^^` placement) | `Sem.lean` | none (checks Lean's real parse via compiled terms) | `sub_left … pipe_arith` | proved+built | pins Lean's actual grouping for concrete inputs; regression anchors for a new Pratt table | trivial |
| operator = instance fn (UInt64 `+ - * / % &&& \|\|\| ^^^ <<< >>>`, `::`, `++`, `∘`, `!=`, `^^`, `&&`, `\|\|`) | `Sem.lean` | `binop` ids | `u64_* … or_false` (rfl) | proved+built | one-line link nano op id → Lean function | trivial |
| UInt64 `==`,`<`,`≤` ↔ Nat/Eq | Init UInt | comparison lowering | `u64_beq_iff`, `u64_lt_iff`, `u64_le_iff` | proved+built | unsigned compare = toNat compare | trivial |
| UInt64 `x/0=0`, `x%0=x` | Init UInt | evaluator totality | `u64_div_zero`, `u64_mod_zero` | proved+built | `/`,`%` without a zero check | low |
| shift counts mod 64 (`<<<`,`>>>` on UInt64) | UInt64.shiftLeft | `b % 64` | — | not attempted (needs BitVec lemma hunt) | `<<<` with count ≥ 64 | med |
| `<` `>` as ambiguity-free tokens, `\|>.`, `<;>`, `$`, `←`-do notation, `·` sections | partial parser code (`Lean.Parser.prattParser`, token fn) | — | — | not provable: `partial`/ParserFn state machine | — | — |

Edge (not provable): how `prattParser` consumes these numbers (partial), longest-match tokenisation of `<<<` vs `<` + `<`, `ws` handling, elaboration-time coercions (`binop%`, `binrel%` insert `↑`; nano is monomorphic so none are needed).
Axioms: see `REVIEW.lean` (expected: propext, Quot.sound, Classical.choice only).

Note found while building: `::` (67) binds tighter than `+` (65), so `1 + 1 :: []` is a Lean type error (witness dropped). The `^^` rows/witnesses were removed; `Sem` has no `^^` claim. The `u64_*` names in Sem are all `rfl`.
