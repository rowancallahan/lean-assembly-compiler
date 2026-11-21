# Proof/Gen — codegen soundness on success

Gen (`Nano/V2Self/C/Gen.lean`, functions `g10`..`g56`) turns the serialized AST of a program into RISC-V words. This
stage proves, about Gen's own code: **if Gen's output is non-empty, the words it emitted are described by a
relation over the AST** (`CG`/`CT`/`CGs` per node, `DefsC` per program) and the width pre-pass accepted every def
(`W`, `WDefs`). It says nothing about what the words do when run; that is Proof/Machine.

Where it sits: fed by the parser (the buffer `x` it serialized, `x.length < 2^31`) and by `Machine/ExprExact`,
`Machine/CallExact`, `Machine/RvEnc` (emitter helper facts). Used by `Machine/NdCG*`, `NdProgW`, `NdWidthB`,
`NdTop2` (which turn `CG`/`W` into "these words are the J templates of this node") and by `Parser/DBPar`, `ParInv`.

## Files
* `BufL.lean` — `Buf` (= `List UInt64`) read/write lemmas: `bget_bset`, `length_bset`.
* `Fixup.lean` — `off_eq`: Gen's jump displacement `(b − a) <<< 2` is `4·(b − a)` (used for `g13`/`g19`/`g20`).
* `GenRef.lean` — the main loop `g39` as a work-item machine, and the node relation. One work item = one `g37` call.
* `GenTop.lean` — one def, the def loop, the start code, and the top functions `g42`/`g41`.
* `GenWidth.lean` — the width pre-pass `g53`.
* `GenAll.lean` — joins the code relation and the width relation over the same defs.
* `DBNode.lean` — Gen's node field bounds `NB` from the kind typing `TyN` (`nb_ty`, `nbl_ty`); consumed by the parser side.

## Main definitions and theorems
| file:name | what |
|---|---|
| `GenRef.lean:GS`, `st`, `it`, `Reach` | Gen's state, one item step, `Reach s P`: after finitely many items `P` holds or the error flag is set |
| `GenRef.lean:Stk`, `Fx` | the item stack (triples) and the fixup list as abstract lists over the buffers |
| `GenRef.lean:em` | the words an append-only emitter adds at position `h` |
| `GenRef.lean:Cx`, `JOk` | per-def constants (AST, npw, nslots, def-start table); `JOk a b`: Gen's jump range check `g14` passes |
| `GenRef.lean:CG`, `CT`, `CGs` | words of a value node / a tail node / an operand sequence: `CG K d i h c i' E` = node at AST index `i`, code position `h`, emits `c`, ends at `i'`, exits `E` |
| `GenRef.lean:Inv`, `Bnd`, `DefC` | invariant between items; state at a def boundary; the code of one def |
| `GenRef.lean` `v_*`, `t_*`, `g36_*`, `g37_t*` | per node kind: the visit / the item runs to a state satisfying `CG`/`CT` |
| `GenTop.lean:def_run`, `DefsC`, `prog_run` | one def (header `g38`, root visit, ENDDEF) and the chain of defs |
| `GenTop.lean:startW`, `gen_ok`, `gen41_ok` | start code; non-empty `g42`/`g41` output = stubs ++ defs' code (`DefsC`) ++ start code |
| `GenWidth.lean:W`, `Ws`, `WDefs`, `g53_ok` | stack-width relation per node and per def chain; `g53` accepting gives `WDefs` |
| `GenAll.lean:Sk`, `sk_det`, `chains` | AST spans are deterministic, so `DefsC` and `WDefs` describe the same defs |
| `GenAll.lean:gen41_full` | **the stage's result**: `g41 c x ≠ []` ⇒ `DefsC … hs T … o ∧ WDefs … hs D …`, the output bytes are `g40 … (startW …)`, `o.length + 32 < 2^18` |

Assumes from the previous stage: only `x.length < 2^31`. Guarantees to the next: `gen41_full` (consumed by
`Machine/NdTop2.lean`).

## Design decisions
* **Soundness on success only.** `Reach` allows the error flag at any point; nothing is proved about when Gen
  fails. Rejected: completeness (Gen accepts every well-formed program) — not needed for `CompileCorrect`, which
  has `compile = some _` as a hypothesis.
* **Relational spec over raw words.** `CG` describes the emitted list as `em (emitter call) h` and concatenations;
  the item proofs never look inside the words (they use an emitter only as append-only, with a length bound).
  "These words are `encG` of J templates" is a separate layer (`Machine/NdCG*`, the `*_exact` lemmas). Rejected:
  stating `CG` directly over J templates — it would mix Gen's control structure with instruction encoding.
* **Work-item machine, not structural recursion.** Gen is an explicit-stack loop (`g39`), so the proof follows its
  items (`Stk`, `Inv`) and recovers the tree shape in `CG`; the AST is read from the flat buffer by index (`tg X i`).
* **Fixups as abstract lists.** Forward jumps are a `0` placeholder word patched later (`g19`/`g20`, `Fx`); `CG`
  carries the pending exits `E`.
* **Width relation proved separately** (`GenWidth`), then tied to the code relation by span determinism
  (`GenAll.chains`) instead of threading widths through `CG`.

## Known limits
* RISC-V-specific (from the prototype note `Testing/notes/GEN_EMIT_PROTO.md`, branch `proto-genemit`): the 40
  dispatch lemmas `g36_*`/`g37_t*`/`g38_*`; emitter names inside `CG`/`CT` (44 `em (…)` sites); a jump is ONE word
  (`g13`/`jw`) with range check `g14`/`JOk` (±1 MiB) and hard-coded lengths; a placeholder is ONE `0` word patched
  by one `bset`; size limits 2^24 code cells, 65536 fixups.
* A native generator (other encoders, multi-word or variable-length jumps) needs `CG` factored over an abstract
  emitter (`Em`: per-call cell lists, jump length independent of displacement, `hole`/`patch`) and the template
  layer over a layout `pos` (CLEANUP_PLAN step 9). Prototyped for CONST/sequence/CALL only; IF/LOOP/tail exits
  (the one-cell-patch assumption) are not done.
* No statement about Gen's failure cases or its running time.

## Build / check
```
lake build Nano.V2Self.Proof.Gen.GenAll Nano.V2Self.Proof.Gen.DBNode
lake build Nano.V2Self.REVIEW && Testing/scripts/review_axioms.sh    # "OK: 8 theorems, axioms as pinned"
```
