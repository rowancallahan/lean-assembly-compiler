# Astra round 11 — proving C itself correct (ADVICE; owner may override)

Relayed advice, not owner decisions. Skeleton: `NANO_V2_ASTRA11_Sound.lean` (type-checks on Lean 4.29 after one
fix: Astra's `compiler_ok` passed the wrong argument to `hg` — needs `hg a p b hr (...)`; axioms: propext only).

Route: (a) refinement for the FRONT END, (c) direct template proofs for CODEGEN. Prove SOUNDNESS ON SUCCESS only:
C may reject valid programs. No completeness, no step correspondence with R, no binary comparison with R.
Meeting point: R's typed source semantics. C's flat AST denotes the source read; C's fixed-frame code implements
that AST. R's inlined output never enters the statement. Translation validation = optional shortcut for the
single self-source (adds a `check s b = true` premise unless folded into C's success).

Parser invariant: tasks = continuation of the reference grammar; operand stack = partial trees.
`View` (cursor, tasks, vals, scope, arena) is ghost; `HeapRep L h q`; `ParserInv` = LayoutOK ∧ HeapRep ∧
cursor ≤ len ∧ WellScopedTasks ∧ ∀ p, Completes ts q p → ParsesProgram ts p.
`Completes` defined by grammar rules for unfinished tasks, independent of the heap machine.
Obligations: Entry; Step (heap reps q', Completes q' p → Completes q p; rejecting branches have no success case);
Exit (empty tasks, one root, EOF; preorder walk invariant: emitted prefix ++ ser(pending ids) = ser(root)).
If the parser resolves slots / flattens pairs / rewrites self-calls, decode to a RESOLVED first-order AST and
prove a separate elaboration lemma to R's typed semantics.

Layout: half-open word-index regions; LayoutOK = disjoint, inside heap, used ≤ cap. One checked-write lemma
(bset changes one cell, preserves disjoint regions; bpush grows live length). Prove non-wrap of UInt64 index
arithmetic BEFORE using it. Exhaustion must not report ok with unfinished work. Separate compiler capacity from
the emitted program's runtime capacity (Implements needs a resource precondition / OOM outcome per the ABI).

Codegen templates: expression stack ops over an arbitrary live prefix; call/return over arbitrary caller frame +
return pc (preserve live slots, owned regions, deliver result at width); branches; loop backedges; functions in
call-graph order; one fixup lemma (patched field encodes target, all else preserved). Reuse Sail instruction/
encoding/memory lemmas below the code-shape split.

Reuse from R: grammar/binding/typing + Lean-meaning link; typed evaluator + prim semantics; inlining theorem as a
bridge for source calls; Sail layer. R's whole-codegen theorem only via a bridge.

Estimate: same order as R's compiler proofs (½–2×). First two probes: (1) scoped `let` around a provisional
self-call (parser), (2) non-leaf call with a live expression-stack value (codegen).
