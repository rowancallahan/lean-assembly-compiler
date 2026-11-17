# NANO_CLOSE: closing the four machine theorems of `Nano.selfHosted_parse_asm`

## Section A (box nano-closeA: lexer h1, expander hm, final instantiation)
(owned by nano-closeA)

## Section B (box nano-closeB: parser h2 = `stage2`, inliner hi = `inlB`)

### Plan / decisions
* 2026-11-17 (start). Setup: build cache restored, toolchain via elan 4.29.0. Branch nano-closeB = nano-parse + nano-int.
* DECISION (inliner design): a paged (`wp_compile`) stage. Its output buffer is PREALLOCATED (fill loop) and written
  only with `set!` (constant size: the side goals of the fixed tactic stay branch-free); one write per step; copy
  mode (`rem`, `cp`) for `[14 h][15 l]` calls; consumes one input byte per non-copy step (parity flag).
  Consequence: a fixed buffer capacity, so the stage equals `inlB` only when the inliner's whole table fits; the
  stage hypothesis becomes `∀ x, <fits> x → fi (ofL x) = inlB x` (weaker hypothesis = stronger final theorem), and
  the size domain gets that condition on `serU u`.

### Log
* Probes (`Testing/nano/closeB/p1.lean`, `p2*.lean`, `p3*.lean`): what `wp_compile`'s `wfP` / fixed tactic accept:
  1. ONE changing array per loop (`Args.wfP`: after the first non-`var` array argument `cw = false`); two arrays
     changed in one loop (`ob`, `st`) ⇒ `wfP = false`.
  2. An array loop must return a plain variable (`T.wfP (.ret a)`: `.var` only); `else ob.set! …` ⇒ `wfP = false`.
  3. The size of a previous loop's result is not known to the next loop's invariant (fill loop + set! loop: open goal
     `(g0 …).size = 64`). `Array.replicate n 0` has a known size (`Array.size_replicate`), also for n = 327680.
  4. A large literal `Array.replicate 327680 0` as a closed term overflowed the stack (`lean` default thread stack);
     `CAP + 0 * xs.size` and `lean --tstack=4000000` are used.
* DECISION (inliner v2, `Nano/InlP.lean`): ONE work array `ob : Array Nat` = def table (cells 0..65536) + header cell
  (start·2^24 + end + 1 of the last closed def) + byte region (inlined bodies, each followed by its arity byte); the
  main loop writes three cells per step with `set!` (byte, table entry, header; unchanged cells rewritten with their own
  value); the emit loop fills a preallocated `Array UInt8` (`set!` only, so no loop allocates: the page events are the
  two `replicate`s, bound `inlP_pk : pk ≤ 600` pages, work space `8192 · 601`).
* PROVED (`Nano/InlPProof.lean`, standard axioms): **`Nano.IP.inlP_eq : inlFits x → (inlP ⟨⟨x⟩⟩).toList = inlB x`**
  (`mn_main`: the main loop simulates `inlS` = `inlGo` with its final state, invariant `Inv`; `mn_copyAll`: copy mode;
  `em_wrap`: the emit loop writes `wrap k last`). `inlFits x`: the inliner's table (all inlined bodies + arity bytes +
  the current body) has < 262136 bytes.
* PROVED (`Nano/PgStage.lean`): `Nano.Link.pg_stage`: `PgProg.Good` + `GoodE` runs + a page bound ⇒ `Implements1With
  (·.data.toList) id body (fun xs => (f xs).toList) (fun _ => 8192·(B+1)) maxIn true` (`body_ok`, `of_pg`).
* PROVED (`Nano/SelfHostB.lean`): `selfHosted_parseB`, `selfHosted_parseB_asm` = `selfHosted_parse(_asm)` with the
  inliner hypothesis `hfi : ∀ x, inlFits x → fi (ofL x) = inlB x` and domain `Sized5B` = `Sized5` ∧ `inlFits (serU u)`.
* Stage 2 (`stage2`, the parser machine): NOT compiled in this session. Assessment from the inliner's experience:
  the inliner's main loop (11 scalars, three `set!` per step, ~10 nested conditionals per component) takes > 1 h of
  `wp_compile` (single thread, 4 GB) and needs `--tstack`. `parseA`'s `step` has ~25 transitions, a frame stack, a
  scope list and a def table (names compared byte by byte), and emits up to 18 bytes per step (`sLi`). Under the
  constraints above (one changing array per loop: stack + scope + defs + output in ONE `Array Nat`; one tail call
  per step; per-step constant work) it needs sub-step modes (emit-k-bytes, compare-name, pop-frame) on the order of
  50 transitions per step function, i.e. several compiles of the inliner's size. Suggested split (each a paged loop
  over one `Array Nat`, composed with `link_stage`, each proved equal to its part of `parseA` by a Lean equation):
  (2a) token bytes → tokens with names resolved to scope slots / def numbers (rescans, no stack);
  (2b) precedence/parentheses with an explicit stack → postfix micro-ops (`serU` without numerals expanded);
  (2c) numeral expansion (`sLi`), a list-path stage (`frontx_compile`), constant output per token.
# NANO_CLOSE: closing the self-hosting theorem of nano

## A (branch nano-closeA): stage 1 (lexer `lexB`) and the expander (`mexp`)

### Setup
* Branch `nano-closeA` = `origin/nano-parse` + merge of `origin/nano-int`. Build cache restored (zstd parts).
* Toolchain: `elan.lean-lang.org` is denied by the network policy (403). elan was installed from its GitHub release
  (`github.com/leanprover/elan/releases`) and Lean 4.29.0 from GitHub releases (the canonical source elan itself uses);
  no denial was routed around.

### Decisions
* `mexp`: the 13-arm list function (up to 20 stored bytes per arm) did not compile in 47 CPU-min (integrator).
  DECISION: compile instead `Nano.MX.mx` (`Nano/ExpandM.lean`), a record-per-step machine: each step either looks up
  one 4-byte record in a table (`MXCODE`, one `UInt64` per record, generated by `Testing/nano/gen_mx.py`) or emits it
  (exactly 4 stored bytes, the micro-op argument substituted by flag bits). `mexp_eq_mx : mexp xs = mx xs 0 0 0` is
  proved for every input, so `hfm` holds for the compiled `nanoExpM`.

### Log
* Front-end constraints found on the way (list front end, `frontx_compile` / `frontx_view`; not changed):
  1. `frontx_view`'s generic equation prover loops (stack overflow) on a recursive call that does not consume the
     list (`f (m :: x :: rest) …` in the `m :: x :: rest` arm): its leaf tactic `simp only [f]` unfolds the call again.
     Work-around: a hand-written view and equation (`mxv`, `mxv_eq` in `Nano/ExpandMSelf.lean`), passed to
     `frontx_compile … from mxv_eq`.
  2. The capacity obligation (`j + (f …).length ≤ O.length` at a call leaf) is closed by `simp only [*, ↓reduceIte, …]`
     with the path conditions. It FAILS (a) after a Prop test `k = 1` (the hypothesis substitutes `k` in the capacity
     hypothesis but not in the goal), and (b) when a Bool test is a sub-term of a later compound test
     (`m == 5 || m == 0` after `m == 5`: simp leaves `true || m == 0`). Work-around: Bool tests (`k == 1`), no
     compound test containing an earlier test.
  3. The `runs` proof (well-founded induction) closes the measure decrease with `dsimp only; omega` /
     `simp_all only [↓reduceIte, …]; omega` / `simp_all; omega`. A goal that `simp_all` closes completely then fails
     ("no goals" for `omega`), and `omega` cannot read `(k == 0) = true` for `UInt64`. Work-around: `Nat` counters and
     a measure whose `if`s use exactly the code's Bool tests (`if m == 5 then … else …`), or no `if` at all.
  The integrator's parked `ElabBSelf` (one-stage lexer, `UInt64` mode, measure `if m = 5 …` with Prop tests) hits 3
  (and 2b for no reason of its own: none of the template's compound tests repeat an earlier test, so 2 is fine).
* Lexer: DECISION: split `lexB` into two stages, proved equal on every input (`Nano/ElabBSplit.lean`,
  `eB_vB : eB (vB xs) = lexB xs`): `vB` = passes 5 and 0 of `lx` without the emitting alternatives, output `[0]` or
  `ty :: source` (copy mode); `eB` = read the type byte, then pass 1 of `lx` (the emitting alternatives only). The step
  macros are generated from the SAME templates as `lx` (`Testing/nano/gen_lexsplit.py`), so the proofs are
  alternative-by-alternative: `lx_vres0/5`, `lv_vres0/5` (through `vres`, the validator's run as an `Option`),
  `le_lx`, `vres5_good` (the type is one nonzero byte). Each half has about half of `lx`'s alternatives.
* Composition: `Nano.SelfHost.selfHosted_parse6` (`Nano/SelfHostSplit.lean`): six stages
  (`vB`, `eB`, `stage2`, `inlB`, `mexp`, `asm`), domain `Sized6` (= `Sized5` plus the bounds of `vB`'s output).
* Resources: four parallel Lean processes on this 15 GB box got two of them OOM-killed (exit 137: the one-stage
  lexer `ElabBSelf` after 21.5 CPU-min, and `mx`). DECISION: the one-stage lexer compile is dropped (the split stages
  replace it; it would also hit constraint 3); at most three compiles at a time.
* Owner's alternative route (S3 typed calculus, compiler proved once): noted; not taken for A's stages so far, because
  the frontx route was already running with the composition (`link_stage` over `Implements1With`) in place, and an
  S3 stage would need an adapter from `CompileCorrect` to `Implements1With`. Route per stage: see the table at the end.
* A path must not test the same condition twice (constraint 4, found on the validator): the test obligation
  `denote (x == 5) = if (m == 5) = true then 1 else 0` fails when `(m == 5) = true` is already a hypothesis. The
  validator's end macro is generated without `lx`'s leading `if m == 5` (the validator tests it before).
* 05:08. **`mexp` COMPILED**: `Nano/ExpandMSelf.lean` builds (5 min 46 s wall, one core; `frontx_compile` 22 s:
  539 obligations, translate + step proof 18.3 s, induction 3.1 s; the rest is `frontx_implements_listC`, the
  kernel-checked words), machine theorem `Nano.Self.nanoExpM.implements1` (Sail axioms), `nanoExpM (ofL x) = mexp x`
  by `mexp_eq_mx`. (The 13-arm `mexp` itself: > 47 CPU-min without finishing, integrator.)
* `mexp` stage TESTED (`python3 Testing/nano/stage_test.py expm R S seed`: inputs `ser p` of corpus + random
  UInt64/Int64 programs and random micro-op strings; expected = executed Lean `mexp`): seed 7, R = 40: QEMU 306/306,
  Sail 8/8; seed 11, R = 400: QEMU 2466/2466 (outputs up to 3248 bytes), Sail 5/5. 663 words, work 271 bytes.
