# Question for Astra (round 14): the parser soundness invariant

## Context
Compiler C (written in a tiny Lean subset: UInt64, if, let, pairs, word buffers, tail fuel loops) self-compiles (B₂ = B₃).
We are proving soundness on success, per your round-11 advice. Lexer, codegen templates, codegen work-loop invariant and the
link to Sail are proved. The PARSER is the big remaining piece (est. 8–15k lines).

The parser `Par1` is an explicit task machine over one heap buffer `h` (a `List UInt64`): ~45 task codes, a dispatcher `v96`,
a runner `v97 : Nat → Buf → Buf` that pops one task per fuel unit, a node arena (8 words/node: tag, payload1, payload2, shape,
pending bit, first child, child count, next sibling), an operand stack of node ids, binding/def/shape tables, and a final
preorder flatten. Your round-10/12 design (provisional bit, task table) is what it implements.

We have an executable reference spec `ParSpec.refParse : tokens → Option AST` (plain recursive Lean, fuel-bounded functions
pExpr/pBin/pLoop/pApp/pArgs/pAtom/pTup/pTy/pDef/pDefs) and `serialize : AST → List UInt64`, and on 8,000 random programs
plus the compiler's own source Par1's output = serialize(refParse) exactly. Goal theorem:
`ParserSound ts : y16 ts ≠ [] → ∃ p, ParsesProgram ts p ∧ y16 ts = serialize p`.

Proved so far: loading phase, name equality, innermost-binding lookup = spec `findEnv`, def lookup = `findDef`,
representation relations for the binding/def/shape tables.

## Our proposed design (please review)
# ParInv design (proposal for the Opus box's review, 2026-11-18)

Goal: `ParserSound ts` (Proof/ParInv.lean): `y16 ts ≠ [] → ∃ p, ParsesProgram ts p ∧ y16 ts = serialize p`.
Done: loading phase (`v99_eq`), `entry` (reduces to the initial task), name equality `v85_name`, `v7_lookup`/`v8_lookup` (innermost binding / def lookup = ParSpec `findEnv`/`findDef`), table representations `ShapeCode`/`BindRep`/`DefRep`/`CxRep` (Proof/ParRep.lean).
The semantic `Completes` is only the bridge; it is true by construction. The real proof is a FORWARD SIMULATION against a defunctionalised (CPS) version of ParSpec:

## Layer 2 (pure spec work, no machine): `ParSpec.Run`
* `inductive Frame` — one constructor per task code of `v96`, carrying exactly the data the task needs (`a`, `b`, the tail flag, the saved depth/slot, …), e.g. `exprStart tl`, `binLoop minp`, `letValue x`, `letBody slot w`, `ifCond`, `ifThen`, `ifElse`, `argsLeft ps`, `callDone id`, `tupRest`, `defHeader`, `defBody …`, `arms`, `defsLoop`.
* `State` = (token list `toks`, next slot `nx`, context `Cx` (env/defs/self), value stack `vals : List (Nd × Ty)`, output defs `out : List DefA`).
* `Run : List Frame → State → Option (List DefA)` — a step function `stepF : Frame → State → Option (List Frame × State)` and `Run` = iterate to `[]`.
* **Refinement lemma (spec-only)**: `refParse ts = Run [defsLoop] (init ts)`. Each ParSpec function `pExpr/pBin/pLoop/pApp/pArgs/pAtom/pTup/pTy/pDef/pDefs` equals `Run (k ++ ks) st = Run ks st'` for its frame list `k` (induction on the fuel). This needs no heap, so it can be proved and reviewed on its own.

## Layer 3 (machine ↔ Run): the invariant
`Rep h st fs` :=
* `HeapRep`: `view h` decodes; status 1; token cursor `cur = |ts| − |st.toks|` (`TokensAt h ts`); slot counter `h[11] = st.nx`;
* `CxRep h st.cx` (binding table, def table, shape table: Proof/ParRep.lean) and, for loops, the current def's self data in the def table;
* `TasksRep (view h).tasks fs`: the task stack read top-down is `fs` (each `Frame` ↔ code/a/b cells; `a`,`b` carry node ids / depths / slots);
* `OpsRep h st.vals`: operand ids `h[d3 + i]` point to arena nodes whose subtrees are `st.vals` (`NodeRep h id nd`: tag/payload/shape/child chain/pending bit decode to `Nd`; the pending bit = "contains a provisional self-call", i.e. `Ty.bot`/`cont`, which is exactly ParLet's v118 fact);
* arena well-formedness (`OpsOK`: ids < capacity; children chains acyclic) and the validation property `v209`-compatible (inputs only where the spec allows);
* the emitted words `h[d11+|ts|+1 …]` = `serialize st.out` followed by the flatten work in progress.
`Inv ts h := ∃ st fs, Rep h st fs ∧ Run fs st = some p ∧ ParsesProgram ts p` is NOT needed; instead
`Cont ts h := ∃ st fs, Rep h st fs ∧ (Run fs st).isSome → ∃ p, ParsesProgram ts p ∧ out = serialize p`
follows from `Rep` + the refinement lemma (the continuation `fs` from `st` can only finish with a parse because `Run fs st` is a suffix of `Run [defsLoop] (init ts)`).

## Preservation: one lemma per task code
`Rep h st (f :: fs) → ∃ st' fs', stepF f st = some (fs', st') ∧ Rep (step h) st' fs'` — and `stepF f st = none → machine fails (status 0)`. Fail directions are needed for completeness only; soundness needs just the first conjunct (machine step ⇒ spec step), and for machine failure nothing (empty output).
Accepting stop: `fs = []`, status 2, `fin` checks ⇒ `serialize` words = output.

## Cost / order
1. Layer 2 refinement (largest pure part; reviewable first). 2. `Frame`↔task-code table and `TasksRep`, `NodeRep`/`OpsRep`. 3. Handler lemmas, expression core first (codes for const/name/bin/if/let/pair/call/prim), then types, defs, loops, `defsLoop`. Each module ≤ 5 min: split by task-code family (ParInvExpr, ParInvDef, …).
Questions for review: (a) is `Run` with an explicit `Frame` datatype acceptable, or should Layer 2 be a relational small-step? (b) `NodeRep` via the sibling chain (field 7) vs via the flattened-words view — I propose the arena chain (v5/v2 are already proved on it in ParLet). (c) the machine does not backtrack, so `stepF`'s `Option` can be read as "machine would fail"; ok?

## Questions
1. Is this forward simulation against a defunctionalised (CPS) spec `Run` the cheapest sound route? Answer our (a)–(c).
   In particular: does `Cont` need an explicit "(st, fs) reachable from init ts" component, and is that the right way to
   connect `Run fs st` to `refParse ts`?
2. The Layer-2 refinement `refParse ts = Run [defsLoop] (init ts)` — fuel-bounded recursive spec vs. iterated `stepF`.
   What is the cleanest statement and induction (fuel mismatch, Option failure) so each ParSpec function needs ONE lemma?
3. Give a Lean skeleton (≤ 120 lines, abstract where needed): `Frame`, `State`, `stepF`, `Run`, the refinement lemma
   statement for one function (pExpr's BIN case with precedence climbing), and the per-task preservation lemma statement
   `Rep h st (f :: fs) → …`, plus how the 45 handler lemmas compose into ParserSound.
4. What is the most error-prone part of `OpsRep`/`NodeRep` (arena sibling chains, reuse of nodes after each def is flattened)
   and how should the invariant state it so the handler proofs stay local (frame rule for the arena)?
5. Rough line estimate for this design vs alternatives.
