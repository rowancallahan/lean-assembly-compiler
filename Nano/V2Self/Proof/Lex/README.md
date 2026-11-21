# Proof/Lex — specification and soundness of the S lexer (`C.s10`)

| file | contents |
|---|---|
| `Lex2Spec.lean` | `LexSpec.Lexes x t`: `x` lexes to token words `t` (maximal munch; `isW`, `isD`, `opTable`, `kwTable`, `le8`), independent of the lexer's code |
| `Lex2Sound.lean` | `s9_sound` (loop invariant), `s10_sound`: `s10 x = t`, `t ≠ []`, `x.length < 2^32` ⇒ `Lexes x t` |
| `ParTokWF.lean` | `TokWF ts` (= `∃ toks, TokL ts toks`): token-buffer well-formedness, hypothesis of `ParserSound`; `tokens_of` |
| `MainTokWF.lean` | `Lexes x ts → TokWF ts`: glues the lexer spec to the parser's hypothesis |

Where it sits: first stage of `mC x = g41 x (o41 (y16 (s10 x)))`; `Main/Sem` uses `s10_sound` + `MainTokWF`.
Decisions: the spec is a relation, one token per `step` (not a second lexer), so soundness is the only direction needed;
keyword/operator tag facts (`op_tags`, `kw_tags`, `and255'`) are closed by `decide` over the tables.
Guarantee: soundness only (no completeness: an input the lexer rejects, `s10 x = []`, is simply outside the theorem).
Check: `lake build Nano.V2Self.Proof.Lex.MainTokWF`. Limit: inputs shorter than 2^32 bytes.
