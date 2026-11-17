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
