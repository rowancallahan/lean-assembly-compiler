# NANO_V2_SRC: the nano compiler's stages in the restricted (nano v2) style

Branch `nano-v2-src`. Goal (ROADMAP "DIRECTION"): nano compiles itself. This branch writes the five stages of
`Nano.selfHosted` (lexA, 2b, inliner, expander, assembler) as byte machines in the constructs the grown nano language
(branch `nano-v2`, Testing/notes/NANO_V2.md) is to accept, and proves each equal to the current stage.

## Status

| stage | current definition | v2 source | bridge (no sorry, axioms propext/Classical.choice/Quot.sound) | status |
|---|---|---|---|---|
| assembler | `Nano.asm` (Nano/Asm.lean) | `Nano.V2S.asmV` (Nano/V2S/Asm.lean) | `Nano.V2S.asmV_eq : xs.length < 2^32 → asmV xs = asm xs` | DONE |
| expander | `Nano.mexp` (Nano/Expand.lean) | `Nano.V2S.mexpV` (Nano/V2S/Expand.lean) | `Nano.V2S.mexpV_eq : xs.length < 2^32 → mexpV xs = mexp xs` | DONE |
| inliner | `Nano.U.inlB` (Nano/SerU.lean) | `Nano.V2S.inlV` (Nano/V2S/Inl.lean) | `Nano.V2S.InlP.inlV_eq : xs.length < 2^32 → inlV xs = inlB xs` (Nano/V2S/InlProof.lean) | DONE |
| lexA (lexer + 2a) | `Nano.LS.lexA` (Nano/LexS3.lean) | `Nano.V2S.lexV` (Nano/V2S/Lex.lean) | `Nano.V2S.LexP.lexV_eq : xs.length < 2^32 → lexV xs = lexA xs` (Nano/V2S/LexProof.lean) | DONE |
| parser 2b | `Nano.PS.stage2b` (Nano/ParseS3B.lean) | `Nano.V2S.p2bV` (Nano/V2S/Parse.lean) | `Nano.V2S.ParseP.p2bV_eq : xs.length < 2^27 → p2bV xs = stage2b xs` (Nano/V2S/ParseProof.lean) | DONE (needs the tuple state + word buffers, see below) |
| composition | `asm ∘ mexp ∘ inlB ∘ stage2b ∘ lexA` | `Nano.V2S.chainV` (Nano/V2S/Chain.lean) | `Nano.V2S.chainV_eq` (intermediate lengths bounded) | DONE |

Every bridge holds for every input of length < 2^32 (2^27 for the parser: its gas-indexed bound on the stack depth is
14·len+7 and must stay < 2^31). Positions are UInt64 words; the self-hosting domain bounds every intermediate by 2^20,
so the hypotheses hold there. Build: `lake build Nano.V2S.Chain` (cold module times: Prelude, Asm, Expand, Inl, Lex,
Parse ≤ 3.2 s; InlProof 4.2 s; LexProof 9.4 s / 0.6 GB; ParseProof 20.6 s / 1.0 GB). Axioms of every bridge:
propext, Classical.choice, Quot.sound. Differential tests (Lean `#eval`, `lake env lean Testing/nano/v2s_*_test.lean`):
inliner 400 random inputs, lexer 3000 (45 accepted), parser 23000 mutated tag streams (4027 accepted), 0 mismatches.

## The constructs actually used (the nano-v2 language must support exactly these)

Prelude (Nano/V2S/Prelude.lean), real Lean definitions:
- `rd (xs : List UInt8) (i : UInt64) : UInt64` — input byte `i`, 0 past the end;
- `len (xs : List UInt8) : UInt64` — input length;
- `put (o : List UInt8) (b : UInt64) : List UInt8 := o ++ [b.toUInt8]` — append one output byte.
The input `xs` is passed unchanged; the output `o` is threaded linearly (never used after being passed on), so it
compiles to a buffer pointer + length register.

Function shapes:
- fuel-recursive: `def f : Nat → List UInt8 → UInt64 → … → R | 0, … => base | n + 1, … => body`; every self call
  passes `n`. `R` is `UInt64` or `List UInt8` (the output). Self calls are tail calls except in `inlBody`, where the
  result of one self call is the output argument of another (`f n xs j (p+2) hi (f n xs t s h o)`).
- non-recursive helpers `def g (a b : UInt64) : UInt64` and `def g (o : List UInt8) (a b : UInt64) : List UInt8`.
- the entry `def stageV (xs : List UInt8) : List UInt8 := …`, which computes initial fuels from `xs.length` (Nat `+`,
  `*`: `xs.length + 1`, `n * n`, literal 256) and calls the loops with `[]` as the initial output.

Expressions (UInt64 only): literals; `+ - *`; `&&& ||| <<< >>>` with literal shift amounts < 64; `let x := e; b`;
`if c then a else b` where `c` is built from `==`, `<`, `≤` on UInt64 and `||` (asm uses `||` in conditions);
calls. No `/`, `%`, no Bool values outside `if` conditions, no structures, lists, Option, pattern matching other than
the fuel `0 / n + 1`.

Used per stage: asm: `&&& ||| <<< >>> == ≤ ||`, `+`; mexp: `== ≤ +`; inliner: `+ - * == < ≤`, the nested self call.

## Design of each stage

- asm: loop over 4-byte records at position `i`; per record four helper functions `ax0..ax3 op a b c` compute the
  output bytes in UInt64 (the low 8 bits are `X0..X3`; lemmas `beq8`, `shr8`, `lt8` move the conditions and shifts
  from UInt8 to UInt64).
- mexp: loop over 2-byte micro-ops; `mexpOp m x o` appends the records (an if-chain of `put`s, generated from the
  arms of `mexp`).
- inliner: no table. The inlined body of def `t` is recomputed from the input whenever `t` is called:
  `startOf` (position after the `t`-th `13` record), `hiAt` (the high-byte register at a position: the last `14`
  record before it), `inlBody f xs j p hi o` walks def `j`'s records from `p`, appending ordinary records, following
  `14`, and for `15 x` with callee `t = hi*256+x < j` calling itself on def `t` (nested), until the `13` record.
  Fuel `(len+1)^2`: fuel is passed by value, so it bounds the longest call chain, at most `len+1` loop steps per
  nesting level and at most `len/2` levels (the work itself can be exponential, as `inlB`'s output). The entry
  counts the `13` records (`cnt13`), emits `wrap k last` (`putPro` for `serPro k`, `putWr` for `sWr`).
  Proof (Nano/V2S/InlProof.lean): list-level meanings `c13`, `so` (offset after the `t`-th `13`), `hiS`, `segG` (one
  def's code); `inlBody_eq : inlBody … = segG …` given the table entries so far (`BP`); `inl_main`: the state of
  `inlGo` at the start of def `t`, by induction on `t` (`inlGo_seg` jumps one def).

## lexA: design

`lexA xs = encT (lexTS xs)`: `[]` unless `adjOk xs`, `lexS xs.length xs = some ts` and the type code of `ts` is 1 or 2;
then `code :: encToks ts`. The first output byte depends on all tokens, so two passes, both scalar loops over the input
position with the SAME fuel discipline as `lexS` (one fuel unit per token, the word span bounded by the fuel too, so
the bridge is a step-by-step simulation, no fuel-independence lemma): `lexChk` returns 4 on failure or the `uniC`
code; `lexEmit` appends `encToks ts`. One step = `stepK` (kind: 0 fail, 1 end, 2 skip, 2+tag token) and `stepN` (next
position); words are ranges `[p, e)` (`wordEnd`, `wordK`, `allDigR`, `allDUR`, `numR`, `emitId`). Proof: `step_eq`
(one `lexS` step = one `stepK/stepN` step, by cases on the byte), then `lexChk_eq`, `lexEmit_eq`, `adjL_eq`.

## Parser 2b: design and the extra constructs it uses

`stage2b` is the parser machine `runS` on a state with lists: the scope `sc` (name, depth), the def table `ds`
(name, arity, index), the continuation stack `K` (frames with ≤ 2 fields). The v2 source `p2bV` keeps the machine
step for step: `pstep` maps one state TUPLE `PS = (c, f, x, y, p, d, na, cg, cf, o, S, D, F)` to the next (control tag
and its ≤ 3 fields, cursor into the tag-format input, depth, arity, current def name, def fuel, output, and three WORD
BUFFERS: scope pairs, def-table triples, frame triples); `prun` is the tail-only gas loop (gas `13·len+6`, enough by
`parseA_gas`). Names are positions of identifier tokens, compared by re-reading (`nmEq`); lookups scan a buffer from
its top (`lookV`, `findV`). A validation pass (`vld`) and a token count (`ntok`) come first.
Extra constructs beyond the other four stages (all real Lean, modelled in Nano/V2S/Prelude.lean):
- one state tuple (13 components, built whole and taken apart whole by `let (…) := s`, the consuming decomposition);
- word buffers as `List UInt64`: `bget b i` (0 past the end), `bsize b`, `bpush b v` (append), `bpop b` (drop last);
  used affinely.
These are exactly the planned increments 3 (products) and 5 (buffers) of NANO_V2.md; nano-v2's `Array UInt64` API
(mk / size / get default 0 / set / push) covers them with `pop` = shrink.
Proof (Nano/V2S/ParseProof.lean, 1950 lines): token layer (`ts_step`: what `decT2` gives at a token boundary;
`vld_eq`, `ntok_eq`, `nmEq_eq`, `idV_eq`); buffer relations `ScR`/`DsR`/`KR` and lookups `lookV_eq`, `findV_eq`; the
relation `Rel xs V s ctl st` with a bound `V` on every number (grows by one per step; `V + gas ≤ 14·len + 7`); one
lemma per control (`sim_defs` … `sim_ret`, combined in `sim`); `prun_eq` by induction on gas; `p2bV_eq`.

## Coordination

nano-v2 box: session_01MfKuVaecMPtighd5kbQ58u, branch `nano-v2`. Messages sent: (1) hello + proposed construct set;
(2) the exact style above + the memory request for 2b; (3) the loop-shape/tail-call questions (my loops take several
parameters; `inlBody` has one non-tail self call, rewritable with buffers if nano-v2 keeps tail calls only) and the
rename to `Nano.V2S`. Worker 4 (nano-v2-boot, session_01MfKuVbK875JiDk244XTTBb) compiles S3 twins of these stages
(`asmVS = asmV`, `mexpVS = mexpV`, `inlVS = inlV`), so the S3 bootstrap of the V2S stages is covered there.

## Open points (for the next round)
- The bridges are against the v1 stages. Main session (round 4) asks for correctness against the v2 LANGUAGE as worker 1
  grows it (if, bits, products, loops, buffers): the stage sources must track the grammar; the v1 bridges are the
  stepping stone and their proof structure (step simulation) carries over.
- `inlBody`'s non-tail self call: keep it (if nano-v2 allows a non-tail self call whose result is the affine output) or
  rewrite the inliner with a buffer table + copy loop.
- Buffers are `List UInt64` with append; switch to the frozen `Array UInt64` API names once NANO_V2_SPEC.md freezes
  them (a renaming plus `Array`↔`List` lemmas).


## HANDOFF (2026-11-17, stage rewrite paused by owner decision)
- DONE: all five stages in the restricted style with bridges to the v1 stages (no sorry; axioms propext,
  Classical.choice, Quot.sound): `asmV_eq`, `mexpV_eq`, `inlV_eq`, `lexV_eq` (len < 2^32), `p2bV_eq` (len < 2^27),
  composition `chainV_eq` (Nano/V2S/Chain.lean). `bash Testing/scripts/check.sh` ALL CHECKS PASSED at d698bab (merge of
  main; only the known statement-fingerprint warning); a second run on 0c5ee27 was still in progress at the pause.
- IN PROGRESS: the tail-only inliner required by NANO_V2_SPEC.md §1.1 (`inlBody` has a non-tail self call, rejected):
  `Nano.V2S.inlTV` (Nano/V2S/InlT.lean): word-buffer table `T` (all def bodies, then the current one) + offsets `O`,
  a call copies `T[O[t], O[t+1])` with the loop `cpy`; capacity `kap = 2^24` (overflow = error, empty output).
  Builds; equals `inlB` on the 400-input differential test (Testing/nano/v2s_inlT_test.lean). NO bridge yet. Plan:
  simulate `inlGo` with `T = tab.flatten ++ cur`, `O` = prefix sums of the entry lengths; hypothesis `Adequate`:
  the final table length ≤ kap (the table only grows, so that bounds every step and the `cpy`/`emT` fuel).
- CONFORMANCE GAPS vs NANO_V2_SPEC.md (to do when the rewrite resumes): (1) the parser's 13-tuple state (`PS`,
  `pstep`) — the spec has no products in milestone 1: flatten `pstep` into `prun` (one loop, 13 parameters, each branch
  ends in a tail call, `[]` or the output) and prove the flattened loop equal to `prun` (branch-by-branch unfolding);
  (2) source text rules (§2): no `namespace`/`open`/`abbrev`, names of the form `x1`/`f_2`, no hex literals, `len'` for
  fuel, `≠` → swap branches of `==`, the shift guard (numerals next to shifts as zero-arity defs, e.g. asm's
  `((a &&& 1) <<< 7) ||| 3`); (3) buffers: §3 (`List UInt64`) vs §8.8 (`Array UInt64` templates) — rename when frozen.
- NEXT: retarget the stages to the v2 grammar (cmp/if, bits, then products, buffers) as worker 1's increments land,
  proving `Adequate x κ → C x = compileV2 x` (Astra r4 §0); the v1 bridges are the route and their step-simulation
  structure carries over. Benchmarks (inlined size, buffer copy cost, kernel time) go to the Haiku test runner.
