# Nano/Parser: token buffer → flat pre-order AST (stage 2)

## Contents
| file(s) | what |
|---|---|
| `Par1.lean` | **code**: parser driver `y16` (typed params, pairs, prims, calls, layout) in the nano subset (was `C/Par1`) |
| `ParSpec.lean`, `ParSpecLen`, `ParSpecTail`, `ParSerLen`, `ParTreeOK`, `ParRep` | trusted-style reference grammar `ParSpec` (`refParse`, `ParsesProgram`) and its serialisation facts |
| `ParRun*.lean` (≈50) | the abstract parser `ParRun`: one file per grammar piece (Expr, Call, Def, Ty, Tup, Loop, WF*, …) |
| `ParInv*.lean` (≈45) | refinement invariant Par1 ↔ ParRun, one file per construct; `ParInv.parserSound` |
| `DBPar`, `MainTyP` | field bounds / kind typing of parsed programs used by Codegen |

## Role
Consumes the token `Buf` from `Nano/Lexer`, emits the serialised AST (`Testing/notes/NANO_V2_IR.md`) to `Nano/Ownership`. Spec grammar is intended to move to `Spec/Source/` later; its proof stays here.

## Decisions
Two-step proof (heap code → abstract `ParRun` → grammar `ParSpec`) keeps each file small (module budget ≤ 5 min, 8 GB); the many `ParInv*` files are per-construct for that reason, not design.

## Check
`lake build Nano.Parser.ParInv` (closure of the parser proof); `Nano/Main/REVIEW.lean` lists what to trust.

## Limits
Parser soundness (parsed ⇒ grammar), not completeness of accepted language beyond `ParsesProgram`. Width cap `nslots, nres < 2^20` is proved in `Main/ParCapBnd.lean`.
