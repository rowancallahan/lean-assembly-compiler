# Proof/Parser — the parser stage (Par1), layers 1–2 and side facts

(`ParInv*` — layer 3, machine ↔ layer 2 — is documented in its own section below, written by its owner.)

Par1 (`Nano/V2Self/C`, the parser) turns Lex2's token words into the serialized AST that Gen reads. The proof is three
layers: **L1** `ParSpec` (reference grammar, independent of the C code), **L2** `ParRun` (Par1's task machine with
abstract data: a frame stack and a state `St`), **L3** `ParInv*` (the real machine's memory ↔ L2). This folder holds L1,
L2 and the facts that other stages take from the parser.

Where it sits: fed by Lex2's tokens (`tokens ts = some toks`, well-formedness of the token words). The result
`Accepts ⇒ refParse ts = some p ∧ output = serialize p` is consumed by `Proof/Main` (`Sem`, `Compile`, `DBStageE`),
`Proof/Bridge` (`MainOk`, `MainShift4`) and `Proof/Own/OwnWF`. `ParSerLen`, `MainTyP`, `DBPar` give those stages the
bounds / typing / operand-count facts about `p`.

## Files
* `ParSpec.lean` — reference grammar `refParse`, `serialize`, resolved program `List DefA`.
* `ParSpecLen.lean`, `ParSpecTail.lean` — small spec-side facts (`len'` has type Nat; the tail flag only admits self-calls).
* `ParSerLen.lean` — `ser_len`: serialization is linear in the tokens.
* `MainTyP.lean` — parsed programs are well-kinded, hence never `.stuck` (`parsed_not_stuck`).
* `DBPar.lean` — parsed bodies have Gen's prim operand counts.
* `ParRep.lean` — how Par1's tables represent ParSpec's context `Cx` (shape codes).
* `ParRun.lean` — L2 machine: `Frame`, `St`, `stepF`/`stepS`, `findB`, `RN` (arena nodes).
* `ParRunStar.lean` — generic run facts (`Star`, determinism, frame discipline `Star.append`).
* `ParRunShape/Small/CInv/Bnd/Names/Obl/Arena/TreeOK.lean` — run invariants: stack shape, width cap, mode/stash, bounds, non-empty names, arena.
* `ParRunWF.lean`, `ParRunWFStep/WFInv/WFFr/WFPres.lean` — invariant `WF` and its per-frame preservation (`wf_star`).
* `ParRunTy/Atom/Args/Call/CallSpec/Prim/PrimS/HCall/Self/Tup.lean` — L2 → ParSpec for types, atoms, arguments, calls, primaries, tuples.
* `ParRunExpr/ExprInv/ExprMain.lean` — expressions: frame inversions, binary-operator loop, assembled refinement.
* `ParRunHdr/Body/Row/Def/Defs/Loop/Flat.lean` — def level: headers, plain and fuel-loop bodies, rows, flatten tasks.
* `ParRunProg.lean` — program level: `loopStep`, `accepts_sound`.
* `ParInv*.lean` — L3 (see below).

## Design decisions
* L2 is pure and fuel-free: frame lemmas are proved once per task code and L3 only has to show the machine implements
  `stepF`. Alternative not taken: simulating ParSpec directly from machine memory (mixes memory and grammar in one invariant).
* ParSpec is a plain recursive descent over decoded tokens (one clause per grammar rule; fuel is a bound never reached), so it
  reads as the language definition. Design: `Testing/notes/NANO_V2_PARINV_DESIGN.md`.
* WF is preserved per frame (`ks_/cx_/bs_` in WFFr, `si_` in WFInv, `gh_` in WFStep) rather than by one big case split:
  each file stays within elaboration limits. The many same-shaped lemmas are intentional.
* Shared helpers live in the lowest file that can host them (`ParRun.lean:findB_mem`, `RN.sh_mk`).

## Main results
| file:name | what |
|---|---|
| `ParSpec.lean:refParse`, `ParsesProgram`, `serialize` | the reference parse and its output format |
| `ParRunProg.lean:loopStep`, `accepts_sound` | L2 accepting run ⇒ `refParse = some p ∧ o = serialize p` |
| `ParRunWFPres.lean:wf_star` | every state reachable from `init toks` is `WF` (so `none` of `stepF` is a true failure) |
| `ParRunSmall.lean:stepS_small` | the width cap `Small` is preserved by every step |
| `ParSerLen.lean:ser_len` | `(serialize p).length ≤ 4 * ts.length + 1` |
| `MainTyP.lean:parsed_not_stuck` | parsed programs are well-kinded: `Sem κ p inp ≠ .error .stuck` |
| `MainTyP.lean:refParse_ty` | a parse has a `TyProg` typing |

Assumes: token words well-formed (`tokens ts = some toks`, non-empty identifier spellings, `ParRunNames`). Guarantees to
L3/other stages: the theorems above.

## Build / check
`lake build Nano.Parser.ParRunProg Nano.Parser.MainTyP Nano.Parser.ParSerLen`;
full check: `lake build` and `Testing/scripts/review_axioms.sh` ("OK: 8 theorems, axioms as pinned").

## Limits
Only the `Nano` surface Par1 accepts is covered (no error recovery claims: a rejected input says nothing about which
error). No dead declarations remain in this part (swept: every name is
referenced from elsewhere); the per-frame lemma families in `ParRunWF*` are the main repetition left and are not
mergeable without changing statements used by the dispatch.

## `ParInv*` (L3)
Per-handler proofs that each step of the parser's machine code preserves the representation `Rep` between the real
machine memory and the L2 state (one file per handler: `ParInvAtom`, `ParInvCall`, `ParInvIte`, …; shared helpers in
`ParInvOps`, `ParInvStep`, `ParInvTop`). Swept: no dead declarations; same-statement copies merged
(`status_bset0`, `ite0`, `shRow0`, `drop_bset0`, `nt_code`).

Lean compatibility (owner rule: nano accepts only what Lean accepts, with the same result): the front end's reject rules
(misplaced modifiers, attribute whitelist, module docs, duplicate arms, doc whitespace, the scope frame) are listed with
examples in Testing/notes/SYNTAX_EXP.md "Reject rules". Still open there: Nat defaulting of literal-only operands (B) and
Lean's offside rule (D).
