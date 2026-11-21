# Nano/Lexer: source bytes → token buffer (stage 1 of the compiler C)

## Contents
| file | what |
|---|---|
| `Lex2.lean` | **code**: the lexer `C.s10`, written in the nano subset (was `C/Lex2`) |
| `Lex2Spec.lean` | spec `LexSpec.Lexes x t`: maximal-munch tokenisation of byte list `x` to token words `t`, independent of the code |
| `Lex2Sound.lean` | soundness: `s10`'s output satisfies `Lexes` |
| `ParTokWF.lean` | `TokWF ts`: the token-buffer well-formedness the parser proof assumes |
| `MainTokWF.lean` | `Lexes x ts → TokWF ts` (discharges that assumption) |

## Role
Reads the program text (`List UInt8`), writes a `Buf` of tag bytes (def, let, numbers + 8 LE value bytes, punctuation, names). Feeds `Nano/Parser`. Driver: `mC x = g41 x (o41 (y16 (s10 x)))` (`Main/Sem.lean`).

## Decisions
Spec is a one-token-at-a-time relation (not a second lexer), so the proof is "code refines relation", and the parser proof only needs `TokWF`. Alternative rejected: proving against a reference lexer function (spec would repeat the code's shape).

## Check
`lake build Nano.Lexer.Lex2Sound Nano.Lexer.MainTokWF`. Used by `Nano/Main` (`Sem`) and the certificate in `Nano/SelfHost`.

## Limits
Inputs under 2^32 bytes. Buffer capacity exhaustion is a separate exit handled in `Nano/Run` (Cap*).
