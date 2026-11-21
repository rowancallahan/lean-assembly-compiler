# Nano/Ownership: linearity check on buffers (stage 3)

## Contents
| file(s) | what |
|---|---|
| `Own.lean` | **code**: the ownership stage `o41` in the nano subset (was `C/Own`) |
| `OwnSpec.lean` | spec `OwnSpec.Linear`: buffers are affine, borrowed only by `bsize`/`bget`/read-only params |
| `OwnWF.lean`, `MainKeep.lean` | well-formedness and the "program kept" lemma |
| `OwnP0` … `OwnP30` | the proof of the walk, split by case to stay under the module budget |
| `OwnStage.lean` | `own_stage`: o41 accepts ⇒ `Linear` |

## Role
Between `Nano/Parser` (AST) and `Nano/Codegen`; passes the AST through or rejects. Guarantees Codegen/Run may treat buffer updates as in-place (the machine proofs assume `Linear`). Notes: `Testing/notes/NANO_V2_OWN.md`.

## Decisions
Checks a spec relation rather than a type system, so soundness is one theorem (`o41_sound`, via `own_stage`).
Non-vacuity examples are in `Nano/Tests/OwnNV.lean`.

## Check
`lake build Nano.Ownership.OwnStage`.

## Limits
Sound, not complete: it may reject linear programs it cannot see are linear.
