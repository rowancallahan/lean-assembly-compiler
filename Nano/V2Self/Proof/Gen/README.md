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
* `GenBase.lean` — source-independent part: state `GS`, item stack `Stk`, fixups `Fx`, `em`/`PI`, `Cx`, `Inv`, buffer lemmas.
* `GenE.lean` — the work-item invariant proved ONCE for any Gen source (`Src`: g36/g37) and encoders (`Em`: g4 … g32).
* `GenRef.lean` — today's RISC-V Gen: the node relation over Gen's own words, the unfolding lemmas of g36/g37 and of
  the emitters, the RISC-V instances, `visit_all` as an instance of `GenEmit.visit_all`; then `g39` and the def level.
* `GenLay.lean` — groundwork for the template layer over a target encoder and layout (`Tgt`, `encL`, `GLay`, `lay_at`,
  `Exact`); not yet used by the chain.
* `GenTop.lean` — one def, the def loop, the start code, and the top functions `g42`/`g41`.
* `GenWidth.lean` — the width pre-pass `g53`.
* `GenAll.lean` — joins the code relation and the width relation over the same defs.
* `DBNode.lean` — Gen's node field bounds `NB` from the kind typing `TyN` (`nb_ty`, `nbl_ty`); consumed by the parser side.

## Main definitions and theorems
| file:name | what |
|---|---|
| `GenRef.lean:GS`, `st`, `it`, `Reach` | Gen's state, one item step, `Reach s P`: after finitely many items `P` holds or the error flag is set |
| `GenBase.lean:Stk`, `Fx` | the item stack (triples) and the fixup list as abstract lists over the buffers |
| `GenBase.lean:em` | the words an append-only emitter adds at position `h` |
| `GenRef.lean:Cx`, `JOk` | per-def constants (AST, npw, nslots, def-start table); `JOk a b`: Gen's jump range check `g14` passes |
| `GenRef.lean:CG`, `CT`, `CGs` | words of a value node / a tail node / an operand sequence: `CG K d i h c i' E` = node at AST index `i`, code position `h`, emits `c`, ends at `i'`, exits `E` |
| `GenRef.lean:Inv`, `Bnd`, `DefC` | invariant between items; state at a def boundary; the code of one def |
| `GenE.lean:Src`, `Em`, `SrcOK`, `EmOK` | a Gen source and its encoders as classes; the dispatch equations and the emitter facts the proofs use |
| `GenE.lean` `v_*`, `t_*`, `visit_all` | per node kind, for any instance: the visit / the item runs to a state satisfying the generic `CG`/`CT` |
| `GenRef.lean` `g36_*`, `g37_t*`, `pi_*`, `*_len` | the RISC-V facts behind `rvSrcOK` / `rvEmOK` |
| `GenRef.lean:cg_e`, `ct_e`, `reach_e`, `visit_all` | the generic relation / run at the RISC-V instance is the concrete one; the concrete invariant |
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
* **Invariant generic over the source and the encoders, by type classes.** `GenE.lean` is GenRef's former proof text
  with `g4 … g37` read as fields of the classes `Em`/`Src` (instance arguments), and the unfolding lemmas as fields
  of `EmOK`/`SrcOK`; the RISC-V instances give back the concrete statements (`cg_e`, `reach_e`), so `GenTop`,
  `GenAll` and `Machine/NdCG*` are unchanged. A second Gen source with the same control skeleton needs only its
  own unfolding lemmas. Rejected: explicit records `Em`/`Src` threaded through every statement (the prototype) —
  same content, but every proof line changes; classes keep the text. The instance equations are proved by folding
  with `rw` (`rvfold`), never by unfolding: unfolding g36/g37 in the elaborator or the kernel exhausts memory.
* **Width relation proved separately** (`GenWidth`), then tied to the code relation by span determinism
  (`GenAll.chains`) instead of threading widths through `CG`.

## Known limits
* The generic invariant keeps Gen's cell shapes: a jump is ONE cell (`g13`) with range check `g14`, a placeholder
  is ONE `0` cell patched by one `bset` (`g20`), the IF / LOOP heads have Gen's lengths (positions `+4`, `+2`, `+5`
  in `GenE`). So it covers a source with other encoders at one cell per control-flow instruction. Multi-cell or
  variable-length jumps (native ARM blocks, x86-64) still need `Em` to carry the jump/head lengths and a splice
  patch; that change is now confined to `GenE.lean` (IF, tail exits, LOOP) and `g28_ok`/`patchR`.
* Not generic yet: the def level and the top (`g38`, ENDDEF `g28`/`g29`, `GenTop`), the width pass, and the
  template layer (`Machine/NdCG*`: `Mt` over `encG`; `GenLay.lean` is only its groundwork).
* Size limits 2^24 code cells, 65536 fixups are part of `live`/`big`/`Inv`.
* No statement about Gen's failure cases or its running time.

## Build / check
```
lake build Nano.V2Self.Proof.Gen.GenAll Nano.V2Self.Proof.Gen.DBNode Nano.V2Self.Proof.Gen.GenLay
lake build Nano.V2Self.REVIEW && Testing/scripts/review_axioms.sh    # "OK: 8 theorems, axioms as pinned"
```
