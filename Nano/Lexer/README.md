# Proof/Lex — specification and soundness of the S lexer (`C.s10`)

| file | contents |
|---|---|
| `Lex2Spec.lean` | `LexSpec.Lexes x t`: `x` lexes to token words `t` (maximal munch; `isW`, `isD`, `opTable`, `kwTable`, `le8`), independent of the lexer's code |
| `Lex2Sound.lean` | `s9_sound` (loop invariant), `s10_sound`: `s10 x = t`, `t ≠ []`, `x.length < 2^32` ⇒ `Lexes x t` |
| `ParTokWF.lean` | `TokWF ts` (= `∃ toks, TokL ts toks`): token-buffer well-formedness, hypothesis of `ParserSound`; `tokens_of` |
| `MainTokWF.lean` | `Lexes x ts → TokWF ts`: glues the lexer spec to the parser's hypothesis |
| `Lex2.lean`, `Dsg.lean` | the code: lexer `s10` (trivia scanners s11–s15) and the `match` desugar stage `t10` |
| `DsSpec.lean` | `DsSpec.ds`, `LexesD` (= `Lexes` then `ds`): the SPECIFICATION of the desugaring (trusted; used by `pOf`) |
| `DsSound.lean`, `DsTok.lean` | `t10` sound for `ds`; desugared tokens stay well formed |

Where it sits: first two stages of `mC x = g41 x (o41 (y16 (t10 (s10 x))))`; `Main/Sem` uses `s10_sound` + `MainTokWF`.
Decisions: the spec is a relation, one token per `step` (not a second lexer), so soundness is the only direction needed;
keyword/operator tag facts (`op_tags`, `kw_tags`, `and255'`) are closed by `decide` over the tables.
Guarantee: soundness only (no completeness: an input the lexer rejects, `s10 x = []`, is simply outside the theorem).
Check: `lake build Nano.Lexer.MainTokWF`. Limit: inputs shorter than 2^32 bytes.

Trivia (syntax-1, Testing/notes/SYNTAX_EXP.md "Reject rules"): dash-dash lines; nested block comments; doc comments with
Lean's whitespace skip after the opener (`docWs`); `@[inline|reducible, …]` (`attrEnd`); `private`; each modifier only
where Lean's `declModifiers` allows it (`declNext`), a module doc only before a command (`cmdNext`). Scope lines
`namespace N`/`section`/`end [N]` (`scopeLine`, `nsName`) become marker tokens (48-51) that `DsSpec.frame` (stage `t10`,
Nano/Lexer/Dsg.lean `t16`/`t19`) allows only around the whole program; `open` is rejected. The compiler's own source
stays in the bootstrap subset (`Testing/scripts/subset_check.sh`); comments are allowed there.
