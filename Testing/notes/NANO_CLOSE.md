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
