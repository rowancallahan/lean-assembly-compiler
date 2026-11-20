# Astra round 7 — growth order for C compiling S (ADVICE; owner may override)

Relayed advice, not owner decisions.

1. Freeze versioned intermediate formats for ALL of S first (tags, lengths, function/var IDs, labels).
   Reserve tags for the full subset, but reject unsupported constructs. Include the loop node + local-var
   conventions in the format from the start.
2. Grow one construct end-to-end, in this order: (0) exact UInt64 literals/arith, (1) comparisons + if,
   (2) pairs, (3) buffers + byte I/O, (4) tail-fuel loops, (5) remaining spellings + whole-source.
   Per feature: tiny source example, expected parser/inliner output, execution matches reference,
   rejection tests for nearby unsupported forms. Do NOT implement the whole grammar first.
3. Differential test at the earliest shared semantic boundary (tokens, decoded AST, eval before/after
   inline, eval before/after expand, decoded instrs + execution, end-to-end bytes+status).
   One harness that records and decodes all five stage outputs (test-only decoders in plain Lean).
   Reference compiler = oracle, not foundation; keep some hand-specified results (wrap, exhaustion, indexing).
4. Shrink syntax, not structure: desugar &&/|| to nested if (short-circuit kept); a<=b as
   `if b < a then false else true` (NEVER a < b+1); drop Int64 if unused; no general match;
   keep pairs; keep a small buffer API (len/read/write/append/new); no general recursion/HOFs.
5. Loops: node loop(fuel, state, zeroBody, stepBody ending continue/exit). Recognise at parse,
   inliner never chases self-calls. Parallel assignment of loop state (compute all from old first).
   Fresh labels/locals per inlined copy. Simple branch layout: short inverted branch over jal; check jal range.
6. Risk checks: inventory; inlining growth per function (main architectural risk — add direct calls for
   big acyclic helpers if bad); peak buffer sizes; loop-state swaps; label collisions/displacement units;
   branch ranges at boundaries; max-word/empty/full; fuel counts on C's source; work-memory init; determinism.
7. Milestones: (1) C compiles its own source; (2) output binary is correct (certificates); (3) fixed point.
