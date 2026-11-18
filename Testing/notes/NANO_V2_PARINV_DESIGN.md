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
