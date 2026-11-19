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
  `tys ++ [assign a, binders]`), `PhOK` (placeholders only during their group), `StkInv` (stack values have a shape code, finished defs and the
  current def in a step arm have a result code). `wf_init`, `wf_step`, `wf_reach`, `wf_star : Star ([defs], init toks) (fs, st) → WF fs st`,
  `wf_pre : WF (f :: r) st → ∃ g1, effF st.ctx f st.g = some g1` (C unfolds `effF` for the facts it needs).
  Files: ParRunWF (defs), ParRunWFStep (`gh_*`), ParRunWFInv (`si_*`), ParRunWFFr (`ks_*`, `cx_*`, `bs_*`, `bt_*`), ParRunWFPres (assembly).
  Per-frame lemmas are GENERATED (python in the session; the pattern is the macro at the top of each file + one theorem per frame);
  if `stepF` changes (Par1 fix), regenerate/fix only the affected frames. Cold build of all ParRun* ≈ 31 s.
RESOLVED (owner 2026-11-19): ParSpec unchanged, Par1 fixed (G 09c864d, H/I 21f717a, J/K d8aadd8). stepF mirrors d8aadd8 (b555635):
  `expr (minp md)` / `prim md` (md = b cell: 0 not tail, 1 tail, 2 operand: if/let rejected), `assign (i sz)` (sz = group size; input only
  alone in its group; a multi-name List group before the input rejected), Nat rejected (let value, pair components (v10), params, states,
  results), `(Nat) →` rejected via `St.all` (constant token list) + `prevTok`. runrun == B1 (rebuilt from current self_S) on 4.9k fuzz.
  B1 recipe: `python3 Testing/nano/v2self/build_self_S.py; python3 Testing/nano/v2self/boot/build_B1.py; lean -c B1.c boot/B1.lean;
  leanc -O2 B1.c -o B1` (then `git checkout Testing/nano/v2self/boot/` — the generator rewrites B1.lean/B1L.lean); compare with
  `cmp.py` = for each pN.txt, `B1 parse` words vs runrun line (script in the session scratchpad; trivial to rewrite).
* `Proof/ParSpecTail.lean` (pure ParSpec): `tl_up`, `tl_down` (+ `Nd.tailCont`, `pLoop_noop`).
EXPRESSION REFINEMENT (B, in progress). PUSHED: `Proof/ParRunExpr.lean` — `VT`, `Post`, `BinSpec n` (expr m 2 ↔ pBin false m),
  `LoopSpec n` (binLoop ↔ pLoop), `loop_sound : (∀ n' < n, BinSpec n') → LoopSpec n` (no sorry); `Proof/ParRunExprInv.lean` — inversions for
  ifCmp/ifThen/ifElse/mkIte/letStart/letSemi/letEnd/letPairX/letPairY/letPairSemi/parenClose/tupRest/mkPair, `PrimCase` + `prim_inv`
  (ifs / lets / AtomLeaf / paren / self / call / primTok); `ParSpecTail.nobot` (tl=false ⇒ type ≠ bot).
  `Proof/ParRunExprMain.lean` (no sorry): `PrimSpec`, `ExprSpec`, `bin_of` (BinSpec n from PrimSpec/LoopSpec < n), `expr_other`
  (expr 0 md at a non-if/let token, incl. the tl re-parse via `tl_down`), `expr_if`, `expr_let` (+ `CxRel.push`/`CxNN.push` for let
  bindings, `join_rel`, `nodeOK_noInp`, `let_shape`, `body_rel`). All specs also give `Stop` (loop stopped), `PT` (tail CONTINUE ⇒
  pending), `ShNN v.sh` (shape present, no nested Nat — ParSpec's `tyShape` needs `hasN = false`) and take `CxNN st` (tables NNT).
  TODO (in order): `expr_letpair` (letStart `(` → letPairX/Y/stash/letPairSemi; pExpr's pair-let clause), `prim_sound` (PrimSpec n from
  specs < n: leaf via G's `atomLeaf_spec`, paren + tuples (`parenClose`/`tupRest`/`mkPair` ↔ pAtom `(` / `pTup`, first component
  re-parse via `tl_down` + `PT`), calls/prim tokens via args (G's `Atoms`/`args_run`/`call_tail`; still waiting for G's answer on who
  writes `args_spec`), self-call 46/54 (needs a `SelfRel st cx`: arm ↔ cx.self, cur.params ↔ self params)), then the assembly
  `∀ n, BinSpec n ∧ LoopSpec n ∧ PrimSpec n ∧ ExprSpec n` by `Nat.strongRecOn`, then def level (F) on top.
PLAN (was: nothing pushed yet): one strong induction on the run length n, using G's `CxRel`/`TyRel`/`AtomLeaf`
(ParRunAtom) and G's call/arg lemmas (ParRunCall) for call/prim heads. Statements (cx related by CxRel, ParSpec nx = st.nx):
  prim md ↔ `pApp f cx (md == 1)` (md ≠ 2 also admits if/let ↔ `pExpr`'s if/let clauses); `binLoop m` with a on top ↔ `pLoop f cx m a.toNd ta`;
  `expr 0 md` (md < 2) ↔ `pExpr f cx (md == 1)`; `expr m 2` ↔ `pBin f cx false m`; `parenClose` ↔ pAtom's `(` continuation; `tupRest` ↔ `pTup`.
  Post-state: vals = v :: st.vals, binds/defs/cur/arm/out/sslot/acc/all unchanged, toks suffix, arena extended, nx ≥, ty/stash free.
  Result: `VT v → (∀ f ≥ 4|toks| + c, pX f … = some (v.toNd, ty, st'.toks, st'.nx)) ∧ TyRel v ty`, VT v := every node of v passes
  `nodeOK (st.defs ++ [st.cur])` (discharged at the def level by the next `defs` step's v209 check; F's `ParTreeOK.nodes`/`ArenaInv`).
  Fuel constants: pExpr 4|ts|+4, pBin +3, pApp +2, pAtom/pLoop/pTup +1 (each recursive descent consumes a token or drops a level).
  pBin's re-parse with tl = false: machine node not pending ⇒ no tail CONTINUE ⇒ `tl_down`; tuple re-parse: `tl_up`.

## HANDOFF — parser lead (2026-11-19, keep current)
Role: review of Layers 2/3; own families: def start/accept 60, headers 66–70/73, loop arms 74–79, self-call 46/54, FINISH 80, flatten 81–83,
`v98`/`fin`, validation, top glue.  All files below pushed, no sorry, std axioms, each module < 10 s.
DONE
* pure (on B's `ParRun`): `ParTreeOK` (ArenaInv/CntInv invariants of every handler, `ok_of_nodes`, `words_body`, `StarN.out_le`),
  `ParRunShape` (`StackOK`/`StkInv`: def-level frames only at the bottom, acc ⇒ empty stack), `ParRunNames` (`NInv`: def names non-empty
  given non-empty identifier tokens), `ParRunArena` (kids < |arena|; `CallInv` along runs via B's `wf_star`/`wf_pre`).
* machine: `ParInvFin` (`v98_eq`, `fin_ne`, `MainCells`), `ParInvVal` (`v205_eq`, `v210_eq`, `v209_eq`), `ParInvFlatM` (`v1_append`,
  `v141_eq`..`v144_eq`: tasks 80–83 = low-cell effect ++ appended words), `ParInvDefs` (`v86_skip`, `idxOf_findD` = v8 lookup vs `findD`,
  `defTab_of`).
* on C's Rep: `ParInvApi` (`out_of`, `ntasks_of`, `main_of`), `ParInvValRep` (`v209_nodeOK`: machine validation ⇒ B's `nodeOK` on
  every arena node; needs `IsInpW`, i.e. B's `RN.isInp` comparing the width mod 2^64 — requested).
* glue: `ParInvTop` (`RepAPI`, `run_sim`, `parserSound_of : RepAPI → |ts| ≤ 2^24 → Layer-2 soundness → ParserSound ts`).
OPEN / WAITING
* Par1: main arity check missing in v99 (Par1 accepts `def m : List UInt8 := []` when 4096 parameter codes are used) — fix requested
  from C; then mirror in `ParInvFin.fin`/`MainCells` and drop `main_of`'s arity hypothesis.
* C's Rep: `inDefF [] = true` makes Rep false at the accepting state (current row is zero) — requested `!fs.isEmpty && …`.
* B: `RN.isInp` mod 2^64 (`IsInpW`); `CxOK` + expression-lemma shape for the def-level Layer-2 soundness (pDef/pDefs) that I take.
* `TokWF ts` hypothesis for `ParserSound` (numeral payload bytes < 256, identifiers non-empty): owner to confirm, D to derive from Lex2Spec.
NEXT: `h_defs` (task 60 on C's Rep, using `v209_nodeOK`, `v86_skip`, `idxOf_findD`), then 80–83 step lemmas (cell lemmas done), then
`api_of_rep` (RepAPI from Rep ∧ StkInv ∧ NInv), then def-level Layer-2 soundness.

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
  Side conditions for the glue (`api_of_rep`), all from B's `WF` / F's `StkInv`: `inDefF fs` (47, 48: the callee row is read), `k ≤ |vals|`,
  `k ≤ arity st c`, `calleeOK st c` (row index in range / prim id < 2^32), `n < 4096` and no flatten frame on the stack (48, from `rep_v5`).
* `Proof/ParInvTy.lean` [pushed] — `tok_cell_k`, `rep_cursor` (generic cursor move), `h_tyCross` (62, v129; needs `st.ty.isSome`),
  `rep_ty` (h[25] := code), `ty_leaf`, `h_tyAtom` (61, v128).
* Layer 2 → spec, `Proof/ParRunAtom.lean` [pushed] — `bdPs`, `CxRel st cx` (typed bindings, `findEnv` = `findB`, `findDef` = `findD` on finished
  rows, row ↔ DefI: `params.map psCode`, `res`), `TyRel v ty`, `atomLeaf_spec`: an `AtomLeaf` step = the `pAtom` clause at every fuel ≥ 1,
  result node `v.toNd`, one node pushed.  (ParRunCall now imports ParRunFlat: two sibling modules that both `simp [stepF]` cannot be imported
  together — "environment already contains ParRun.stepF.eq_8" — B should realize stepF's equation lemmas once in ParRun.lean.)
* `Proof/ParInvIntern.lean` (imports Par1 + BufL only) — `PairRow`, `v10_scan`: v10 from row j = `h[25] := i + 5` for the first matching row i,
  else the allocation step `v10 1 g x y h[26]`.
FINDING J (found by G; fixed by C in d8aadd8, re-verified on native B1): v210's "first code-3 parameter is the callee's input" contradicted fix H;
`def f (a b : List UInt8) : UInt64 := 1` + `f x []` was accepted with a 1-arg CALL. Now a List group before the input is rejected at the def
(Par1 ⊂ ParSpec there: completeness only); input first then a group (`(x : List UInt8) (a b : List UInt8)`) agrees with the spec.
DESIGN GAP for 63 / pairs (sent to C): `ShapeCode.pr` has no width cell (+2, read by v9) and no bound against h[26] (rows allocated), and `Rep`
does not mention h[26]; v10's allocation writes row h[26], so `ShTabAgree` (whole region) cannot be used as its frame — needs
`c < 5 + h[26]` in `ShapeCode.pr`, `(bget h 26).toNat ≤ 8192` in Rep and a frame lemma over rows < h[26].
OPEN (no answer from B yet): statement form of reflection after the fuel decision (ParSpec is still `Option`; "ok ∨ OutOfFuel" needs a 3-valued spec),
and who owns the St↔Cx relation (binds↔env, rows↔DefI, cur/arm↔self) and RN↔(Nd × Ty).  Facts pArgs reflection needs: `v.toNd` = the spec node;
Ty.s s ⇒ sh = s ∧ ¬isInp (and tag 1 ⇒ Ty.lit); Ty.lit ⇒ sh = uw; Ty.inp ⇒ isInp; "argument i isInp ⇔ parameter i = `.inp`" comes ONLY from the
deferred validation (`nodeOK` of the CALL node at the next `defs`), so call reflection takes `inpMatch`/nodeOK of the built node as a hypothesis.
Fuel arguments: argCheck accepts a Nat parameter for sh = nt, a bare numeral (tag 1) or len' (tag 9, a = 1) — a subset of `tyMatch .fuel`.
* Layer 2 → spec [pushed]: `Proof/ParRunArgs.lean` — `Pushed`, `CxRel.transport`, `ValOK`, `AtomSpec`, `ParenH N cx` (the open-recursion
  hypothesis on parenthesised atoms: B's expression induction supplies it), `atomSeg_spec`, `ArgsMatch`, `args_spec` (k atom segments =
  `pArgs` at all large fuels for every parameter list the argument types match).  `Proof/ParRunCallSpec.lean` — `tyMatch_of` (argOK + input
  rule ⇒ `tyMatch`), `InpPair` / `toNdL_dropInp` (flattener's skip = `dropInp`), `defcall_spec` (CALL of a finished def = `pCallDef`, node
  `toNd`, type `.s res`), `primcall_spec` (prim application = prim clause of `pApp`; `prim_toNd`), `prim_inpPair` (the prim input rule from
  `nodeOK` of the built node).  Statement style = B's ty_sound (∀ fuel ≥ F ⇒ `some`); both call theorems take `InpPair` of the built node
  as a premise (deferred validation) and return the continuation run with the node pushed.
* Layer 3 [pushed, on C's stable Rep]: `ParInvBind.h_binders` (66, v131); `ParInvName` — `v85_drop` / `v8_drop` / `v7_drop`, `v8_val`
  (h[22] = findD index + 1 / 0), `v7_findB` (h[21] ↔ `findB`), `bindTab_of`, `idxOf_findB`, `rep_same` (Rep across `Same 21/22`);
  `ParInvArgName.h_argName` (55, v126; needs no flatten frame on the stack); `ParInvAtom` — `tok_num`, `v9_cw`, `ShapeCode.nt_code`.
  `ParRunCallSpec.def_inpPair` / `inpMatch_get`: v210's `inpMatch` ⇒ `InpPair`, given the row invariant `FirstLs` (asked of F).
AGREED (owner relay, 09:30): statement form = ty_sound's (∀ fuel ≥ F ⇒ `some`), no 3-valued spec; B adopts `CxRel` / `TyRel` and plugs
`args_spec` / `defcall_spec` / `primcall_spec` into its expression induction via `ParenH`; F = defs / headers / arms / flatten / top.
Build runner for G: Haiku session_01MfKuVZqa87sKK2KCMC5w2M.
DONE since (all pushed): `ParInvAtom.h_argAtom` (43, v120; LOC node via C's `rep_v5g`), `ParInvGroup.h_group` (67) + `rep_v6`,
`ParInvAssign.h_assign` (68, v133) with `v201_eq`, `asgHeap` / `v133_eq` / `asg_eff` / `rep_asg`, `v133_full`, `row_frame'`.
MACHINE HANDLERS OF G, STATUS: 43 ✓, 44 ✓, 45 ✓, 47 ✓, 48 ✓, 55 ✓, 61 ✓, 62 ✓, 66 ✓, 67 ✓, 68 ✓; 63 (tyPair, v130) OPEN.
Side conditions the glue must supply (from B's `WF` / F's `SInv`): no flatten frame on the stack (43, 48, 55); `inDefF fs` (47, 48, 68);
`k ≤ |vals|`, `k ≤ arity`, `calleeOK` (47); `d ≤ |vals|` (45); `n < 4096`, `calleeOK` (48); `st.ty.isSome` (62, 68); `i ≤ |binds|`,
`cur.nni < 2^63` (68).
WAITING ON C: `ShapeCode.pr` bound `c < 5 + h[26]` + a Rep fact on h[26] ⇒ `h_tyPair` (63) from `ParInvIntern.v10_scan`: found row i ⇒
h[25] := i + 5 with ShapeCode (needs "rows < h[26] decode" — an interning invariant in Rep), else allocate row h[26] (Nat components
rejected, capacity d15, width cell = sum of the two v9 widths) — the frame must show old codes < 5 + h[26] keep decoding.

