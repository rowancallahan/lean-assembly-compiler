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

## HANDOFF — Opus box B, parser Layer 2 (2026-11-19, keep current)
DONE (pushed, no sorry):
* `Proof/ParRun.lean`: `Frame` (one constructor per v96 task code, `Frame.code`), `RN` (arena node: tag a b sh pend kids), `Bd`, `DefR`, `Callee`, `St`
  (cell map in the file header), `stepF` (pushed frames TOP FIRST), `stepS`, `Star`, fuel `run`, `mainOK` (v99 post-checks), `Accepts`, `runParse`.
* Validation: `Testing/nano/v2self/fuzz/runrun.lean DIR N` (Layer-2 run on the spec tokens) == native Par1 (`B1 parse`, B1 from boot/build_B1.py
  + `lean -c` + `leanc`) on 4,890 pargen programs (seeds 7, 11, 12, 13), 22 hand cases and the full C source (29,224 words): 0 differences.
* `Proof/ParRunStar.lean`: `StarN`, `Star.det`, `Star.append` (lift a sub-run under a stack suffix), `Star.split` / `StarN.split`
  (a run of `k ++ ks` to `[]` passes through `ks`), `StarN.head`. These give each ParSpec function its "Run (k ++ ks) st = Run ks st'" lemma shape.
* `Proof/ParRunTy.lean`: TYPES done. Inversions `tyAtom_inv`/`tyCross_inv`/`tyPair_inv`/`rparen_inv` (pattern: `simp only [stepF] at h; split at h`),
  `ty_sound`: `StarN n (tyAtom :: ks, st) ([], fin) → ∃ t r n' < n, |r| < |toks|, (∀ f ≥ 2|toks|+2, pTy f toks = some (t, r)) ∧
  StarN n' (ks, st.withTy r (trRes t)) ([], fin)` (+ the `tyCross` continuation `crossK`). Template for every other family.
  Cold build ParRun+ParRunStar+ParRunTy ≈ 3 s.
* `Proof/ParRunFlat.lean`: FLATTEN done. `RN.words` (= what v142/v143 emit), `flat_run`/`flatL_run` (frame `flat n` always reaches its
  continuation with `out ++ n.words`), `Star.cut`/`Star.one`; `RN.toNd`/`RN.ok`, `RN.words_eq : n.ok → n.words = n.toNd.ser`.
  NOTE: `RN.ok` includes "no input-local children" for bin/ite/let/loop/cont; it is NOT an invariant of the operand stack (the machine
  builds e.g. an ITE with input branches and rejects it only at the next `defs` via v209). Get it from the v209 check of the arena.
* `Proof/ParRunWF*.lean`: INVARIANT `WF fs st` done, for box C. `effF` = per-frame big-step ghost effect + precondition on
  (operand depth, binding count, ty set) read through `Ctx` (rows, arm); `Shape` (final frames last, `group` alone, `assign` only in
  `tys ++ [assign a, binders]`), `PhOK` (placeholders only during their group), `SInv` (stack values have a shape code, finished defs and the
  current def in a step arm have a result code). `wf_init`, `wf_step`, `wf_reach`, `wf_star : Star ([defs], init toks) (fs, st) → WF fs st`,
  `wf_pre : WF (f :: r) st → ∃ g1, effF st.ctx f st.g = some g1` (C unfolds `effF` for the facts it needs).
  Files: ParRunWF (defs), ParRunWFStep (`gh_*`), ParRunWFInv (`si_*`), ParRunWFFr (`ks_*`, `cx_*`, `bs_*`, `bt_*`), ParRunWFPres (assembly).
  Per-frame lemmas are GENERATED (python in the session; the pattern is the macro at the top of each file + one theorem per frame);
  if `stepF` changes (Par1 fix), regenerate/fix only the affected frames. Cold build of all ParRun* ≈ 31 s.
BLOCKER (reported to owner 2026-11-19): Par1 accepts MORE than ParSpec, so `Accepts ⇒ refParse` is FALSE today:
  (1) code 3 parses `if`/`let` as primaries (operands, if-conditions): `1 + if a < 2 then 3 else 4`, `1 + let b := a; b`, `if let b := a; b < 2 then …`;
  (2) input parameter = first `List UInt8` param regardless of binder group (ParSpec: only when alone in its group): `(x y : List UInt8) … rd x 0`;
  (3) Nat never rejected: Nat params / results / let values / tuple components / loop states, and a Nat `let` accepted as self-call fuel.
  Completeness-only (Par1 rejects, spec accepts): zero-state loop; `(if c then x else x)` as the input argument.
  Awaiting the decision: fix Par1 (box C) or widen ParSpec. Layer 2 mirrors CURRENT Par1; after a Par1 fix, update `stepF` + rerun runrun.
Interface for box C (Layer 3): frames ↔ task cells as in `Frame`'s comments; `none` results that the machine does not have (shallow stack,
`ty = none`, param index out of range) are to be excluded by a Layer-2 invariant `WF` (TODO, below).
NEXT: (b) soundness per ParSpec function, form: `StarN n (k ++ ks, st) ([], fin) → ∃ r, pX f … = some r ∧ StarN n' (ks, st') ([], fin)` for all
fuel `f ≥ c·|toks| + d` (pTy: 2|ts|+2; expressions: 4|ts|+4 per the call-chain potential), relating nodes by `toNd` (drop input args/locals as v142);
order: types (independent of the blocker), flatten (`flat`/`flatL` ↔ `Nd.ser ∘ toNd`), defs/binders/arms, expressions last (blocker).

## HANDOFF — parser lead (2026-11-19, keep current)
Role: review of Layers 2/3 + own families: loop defs 73–79, self-call 46/54, FINISH 80, def headers 60–70, flatten 81–83, `v98`/`fin`, validation.
DONE (pushed, no sorry, std axioms; each module < 5 s):
* `Proof/ParTreeOK.lean` (pure, on B's `ParRunFlat`): `nodes` (postorder), `ArenaInv st` (arena = nodes of the operand trees), `cntOK`/`CntInv`
  (child count per tag); `stepF_arena`, `stepF_cnt`, `Star.inv` (both are invariants of every handler, proved by one `cases f` script);
  `ok_of_nodes` (every node cntOK ∧ nodeOK ⇒ `RN.ok`), `words_body : z.words = z.toNd.ser`. (My duplicate `ParTree.lean` of B's ParRunFlat was removed.)
* `Proof/ParInvVal.lean` (machine): `v205_eq` (input-local count over a `Links` chain), `v210_eq` (= pure `imC` over code cells),
  `v209_eq` (v209 = 1 ↔ every node in [u, h[9]) passes `nodeC`).
* `Proof/ParInvFlatM.lean` (machine): `v1_append` (task pushes commute with appended output), `v141_eq` (task 80), `v142_eq` (81),
  `v143_eq` (82), `v144_eq` (83): exact heap = low-cell effect ++ appended words.
* `Proof/ParRunShape.lean` (pure): def-level frames only at the bottom (`StackOK`), `stepF_shape`, `SInv` (+ acc ⇒ empty stack), `Star.sinv`.
* `Proof/ParInvTop.lean`: `RepAPI` (the Layer-3 contract) and `parserSound_of : RepAPI → |ts| ≤ 2^24 → Layer-2 soundness → ParserSound ts`.
* `Proof/ParInvFin.lean` (machine): `v98_eq` (output copy = heap suffix, or `[]` on fuel-out), `MainCells`, `fin_ne`
  (`fin ts 1 h ≠ []` ⇒ status 2 ∧ a def exists ∧ main cells ∧ output = `h.drop (d11 + |ts| + 1)`).
REVIEW FINDINGS (sent to B, C, owner):
* Par1 ⊋ ParSpec, confirmed on native B1: (1) if/let operands [fixed: Par1 fix G]; (2) input = first List param regardless of binder group
  (`(a b : List UInt8)`: npw 1 vs spec 2); (3) Nat outside fuel positions (let, tuple, param, result, state, under ×); (4) `: (Nat) →` loop header.
  Proposed guards (C): v106, v130, v134, v137, v136, v116, v107 reject code 4; input rule: `pickPs` drops `single` or v132/v133 group flag.
* `ParserSound` is false for arbitrary `ts`: v87 ORs numeral payload words (spec adds), v85/v86 accept any non-zero ident marker.
  The top theorem needs `TokWF ts` (tokens decode ∧ payload words < 256), from Lex2Spec (D). Owner to confirm.
* Design: Layer-2 state machine-typed (done by B: `RN`); validation is deferred (v209/v210 in the next v127); soundness direction is
  run ⇒ spec (fuel-free machine grammar, then fuel bound 8|toks|+8); stack-typing `WF`; slots/widths only mod 2^64 (`isInp` must test
  `b.toUInt64 == 0`; CALL emit `b.toUInt64 - ni.toUInt64`); step-arm env order (fuel binder outermost in Par1); def rows ≥ h[12] have
  field 6 = 0 and param-code cells ≥ h[27] are 0; arena = consecutive postorder intervals (coverage for v209); pend tested only in v101/v107.
NEXT (in order): (c) machine lemmas for 81/82/83 and 80 on C's Rep (blocked until C's
NodeRep/OpsRep are restated on `RN`); (d) headers 60–70, loop arms 73–79, 46/54; (e) `api_of_rep`: RepAPI from C's `Rep` ∧ `SInv` (status/ntasks/len/out/main from Rep; step = the per-frame lemmas of C, D and me).
OPEN ISSUES: Par1 fix H unsound (multi-name List group before the input; C informed with programs); `(Nat) →` header accepted;
C's Rep relates nx/slots/npw/RNRep a,b by toNat (must be mod 2^64) and ShapeCode lacks the width cell; DefsRep lacks zero code cells ≥ h[27];
B: `isInp` on b mod 2^64; prim 1..3 nodes need ≥ 1 child (WF: mkCall n = arity) else flatten of a 0-child prim diverges from Par1.

## HANDOFF — G: arguments / calls / prims / types (2026-11-19, keep current)
Families: frames 43 argAtom, 44 args, 45 mkCallN, 47 argCheck, 48 mkCall, 55 argName, the prim / def-call heads of code 3, types 61–63 (machine side),
binders 66–68, shape interning v10 (split proposed to F, who keeps 46, 54, 60, 70, 73–83; no objection received).
DONE (all pushed, no sorry, axioms ⊆ propext / Classical.choice / Quot.sound, every module < 3 s):
* Layer 2, `Proof/ParRunCall.lean` (imports ParRunStar only): `mkNode_inv`, `args_zero/succ`, `mkCallN_eq`, `argOK` + `argCheck_inv` / `argCheck_run`
  (k+1 steps, state unchanged), `mkCall_inv`, `argAtom_inv`, `argName_inv`, `AtomLeaf` (= the non-parenthesised clauses of `pAtom`) + `AtomLeaf.eff`,
  `atom_run` (paren case handed back as a run of `expr 0 false :: parenClose :: ks`), `Atoms` / `args_run`, `callNode` / `call_tail` (45→47→48).
* Layer 2, `Proof/ParRunPrim.lean`: `psCode`, `prim_sig` (Par1's prim tables = `ParSpec.primSig`: id, arity, result, parameter codes, input position),
  `prim_tok`, `prim_head`.
* Layer 3 on C's `Rep`: `Proof/ParInvCall.lean` — generic `rep_pop` / `rep_push`; `h_args` (44, v119), `h_mkCallN` (45, v121; needs `d ≤ |vals|`).
  `Proof/ParInvPrim.lean` — `ShapeCode.det`, `ShOpt.det`, `u_beq`/`u_lt`, `v91_eq`, `v92_code`, `v90_code`.
  `Proof/ParInvArg.lean` — `rep_scratch` (Rep ignores cells 21 / 31), `v122_eq`, `row_rep` (callee row from DefsRep), `calleeOK`, `arW_code`
  (machine parameter code = `parCode`), `operand_fld`, `h_argCheck` (47, v122), `h_mkCall` (48, v123, on C's `rep_v5`).
  Side conditions for the glue (`api_of_rep`), all from B's `WF` / F's `SInv`: `inDefF fs` (47, 48: the callee row is read), `k ≤ |vals|`,
  `k ≤ arity st c`, `calleeOK st c` (row index in range / prim id < 2^32), `n < 4096` and no flatten frame on the stack (48, from `rep_v5`).
FINDING J (Par1 ⊋ ParSpec, confirmed on native B1 vs `specrun`; sent to C, B, owner; = F's "fix H unsound"): fix H made v133 choose the input per binder
group, but the call-site validation v210 still takes "first code-3 parameter" as the callee's input. `def f (a b : List UInt8) : UInt64 := 1` +
`… put [] (f x [])` is ACCEPTED (CALL with 1 arg, callee npw 2: mis-compile), spec rejects; `(a b : List UInt8) (x : List UInt8)` + `f x [] []` likewise;
the correct calls are rejected. Needs: the def row records its input parameter, v210 tests that; Layer 2 `inpMatch` / `assign` mirror it.
Native B1 for such checks: `build_self_S.py; boot/build_B1.py; lean boot/B1.lean -c B1.c; leanc -O2 B1.c -o B1; B1 parse < p.txt | od -tu8`.
OPEN (no answer from B yet): statement form of reflection after the fuel decision (ParSpec is still `Option`; "ok ∨ OutOfFuel" needs a 3-valued spec),
and who owns the St↔Cx relation (binds↔env, rows↔DefI, cur/arm↔self) and RN↔(Nd × Ty).  Facts pArgs reflection needs: `v.toNd` = the spec node;
Ty.s s ⇒ sh = s ∧ ¬isInp (and tag 1 ⇒ Ty.lit); Ty.lit ⇒ sh = uw; Ty.inp ⇒ isInp; "argument i isInp ⇔ parameter i = `.inp`" comes ONLY from the
deferred validation (`nodeOK` of the CALL node at the next `defs`), so call reflection takes `inpMatch`/nodeOK of the built node as a hypothesis.
Fuel arguments: argCheck accepts a Nat parameter for sh = nt, a bare numeral (tag 1) or len' (tag 9, a = 1) — a subset of `tyMatch .fuel`.
NEXT: (1) machine 43 (v120) and 55 (v126): need the name lookup on Rep (v7_lookup / v8_lookup ↔ findB / findD) and the LOC node (shared with C's
task 3 id case — ask C before writing); (2) machine types 61–63 (v128–v130; v10 pair interning: loop over the shape table, new row ⇒ ShapeCode for
`.p l r`, ShTabAgree frame); (3) `pArgs` / `pCallDef` / prim-head reflection on `args_run` + `call_tail` once B fixes the statement form;
(4) binders 66–68 ↔ `pBinders`/`bindSlots` after fix H/J are mirrored in `stepF`.
