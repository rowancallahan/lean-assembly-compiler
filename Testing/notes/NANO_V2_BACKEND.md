# nano v2 small backend (worker 2, branch nano-v2-backend)

Owner of Nano/V2/* (except worker 1's spec files). Spec status: worker 1's NANO_V2_SPEC.md / origin/nano-v2 did NOT
exist when this round started (asked by message); the typed AST below is PROVISIONAL and will be adapted.

Namespace `Nano.V2B` (worker 1's increment-1 files use `Nano.V2`, Nano/V2*.lean, Testing/asm/emit_nano_v2.lean;
no name is shared).

## Files
- Nano/V2/Lang.lean: typed AST `Ex`/`Tl` (words, owned `Array UInt64` buffers, fixed nested products, `ite` on
  unsigned comparisons, the ONE loop `loop fuel init z body` with `Tl.ret`/`Tl.next` tail positions, consuming
  `split`), Lean meaning `den`/`run`/`denT`, `Prog.eval : List UInt8 → Except UInt64 (List UInt8)`, typing `tyOf`.
- Nano/V2/Gen.lean: `cE`/`cT` → structured stack code `SC` (ins/seq/ite/loop/jmp) → `SC.flat` (instruction list,
  branch offsets resolved) → `I.enc` (RV64IM words). `gen p : Option (List UInt32)`.
- Nano/V2/Copy.lean: the byte copy (round 2 §7) as typed AST (`copyProg F C`) and as ordinary Lean (`copyLean`).
- Testing/asm/emit_nano_v2b.lean, Testing/nano/v2b_test.py: QEMU + Sail tests.

## Machine contract (proposal for `ImplementsBytes`, pending worker 1)
StartCorrect registers (a0 input, a1 length, a2 work base 8-aligned, sp work top, a3 output, ra). On return:
ok ⇒ a0 = 0, a1 = length, output bytes at a3; error s ⇒ a0 = s, a1 = 0 (length 0); out of work memory ⇒ a0 = -1;
push on a full buffer ⇒ a0 = -2. Only caller-saved registers t0-t6, a0, a1, a4, a5 written; sp/gp/ra/s* kept.
Fixed code origin is not needed by this code (only relative jumps) but is accepted.

## Representation
- value stack: t6, 8-byte slots, downward from sp rounded down to 8; every push checks t6 ≥ t5.
- heap: t5, bump-allocated upward from a2; buffer = [len][cap][cap words]; a buffer value = its address.
- products: the components' slots side by side (no boxing); variables = (type, absolute first slot).
- input: t3 base / t4 length, read with `lbu` (immutable, separate from output and work).
- loop frame: [fuel][state]; HEAD: load fuel, if 0 → z; else decrement in place, body; `next` slides the new state
  over the old one and jumps to HEAD; `ret` slides the result over the frame and jumps to EXIT. Never unrolled.
- the 12-bit offsets limit a frame to 255 visible slots (`Lim`); `cE` returns `none` beyond.

## Log
- 2026-11-17: byte copy end to end: 264 words. `python3 Testing/nano/v2b_test.py nv2_copy|nv2_copyfuel|nv2_copycap`
  (after `lake env lean --run Testing/asm/emit_nano_v2b.lean`): 20 inputs each ([0,127,128,255], empty, 1..101 bytes)
  × (4096-byte work, 8-byte work): QEMU == Sail == Lean `Prog.eval` (= `copyLean`, checked in the emitter);
  statuses: ok, 1 (fuel exhausted: fuel 3, or 100 with a 100-byte input), 2 (capacity 3 full); OOM flag a0 = -1 with
  8-byte work; writes only inside output + work (Sail trace); sp/gp kept.
- 2026-11-17: `nv2_mix` (Nano/V2/Copy.lean `mixProg`): every construct (big literals through the 17-instruction
  `li`, add/sub/mul/and/or/xor/shl/shr, get/set incl. out of bounds, let, fst/snd, split, input-dependent fuel
  `isize + 1`): 492 words, 20 cases × 2, QEMU == Sail == `Prog.eval`.
- Proof layer 1 (Nano/V2/Sem.lean): abstract machine for `SC` (word memory for the work block, accesses checked:
  8-aligned inside [lo, hi); `lbu` only in the input, `sb` only in the output), big-step `SC.Ex` with loop rules.
- Proof layer 2 (Nano/V2/Expr.lean): `Stk` (value stack representation), `Keep`, `Post` (the uniform expression
  contract's outcome: pushed values or out of memory), `seq_ok` (composition), **`pushC_ok`** (the bound-checked push).
- Proofs added (Nano/V2/Expr.lean, Nano/V2/Loop.lean; axioms ⊆ {propext, Classical.choice, Quot.sound}):
  **`li_ok`** (any 64-bit literal, the 17-instruction path by a per-byte step lemma), **`lit_ok`** (literal contract),
  **`ld_slot`** (stack-slot load, address valid), **`varC_ok`** (a k-slot variable copied, by induction on k),
  `pre_ok`, `Stk.set`, `Keep.set`, and **`loop_ok`**: the LOOP-HEADER INVARIANT for `SC.loop`, generic (invariant at
  HEAD indexed by the fuel, zero branch, one body run re-establishing it at the backward jump), by induction on fuel.
  Generator refactor for the proofs (same behaviour, tests re-run): every push is `pushC`; `var` uses `varC`.
- Build: every Nano/V2 module < 4 s (`lake env lean`, deps built; no /usr/bin/time on this box).

- Nano/V2/Blocks.lean (1.6 s): `sd_slot`, `copies_ok`, **`slide_ok`** (result slots move down over a dropped frame,
  deepest first, by induction on the copies), `Stk.pop1`/`Stk.popk`, `drop_node` (fst), `sd_top`, `binT_ok`, and the per-construct
  lemmas **`bin_node`** (binary op from its operands' contracts), **`ite_node`** (branching `if` from the operands'
  and both branches' contracts; `BOp.ofCmp_eval`), **`let_node`**/`slide_node` (let; also snd/split/loop exits).
  Nano/V2/Inp.lean: `InpRep` (t3/t4 = the input block), **`isize_node`**, **`iget_node`** (lbu in range, 0 out of range).
  Nano/V2/Tail.lean: `JPost`, **`tail_node`** (loop-body `ret`/`next`: slide over the frame part, jump exit/head).
  Axioms of every lemma: ⊆ {propext, Classical.choice, Quot.sound}.
  Per-construct lemmas now proved: lit, var, bin, ite, let, fst, isize, iget (+ the loop header theorem). Missing for the buffer-free
  `cE_ok` induction: pair (= `seq_ok`), snd/split (= `slide_node`), `Tl` cases + loop instantiation, and the
  value/type bookkeeping (EnvRep: env entry (τ, p) ↔ slots p..p+|τ| of the stack hold `flat v`).

## Against Astra round 4 (merged from main)
- §1 generic header-to-header theorem: `loop_ok` (Inv indexed by fuel n, zero case = the `| 0 =>` equation, body
  outcome `jmp head` = continue s' / `jmp exit` = exit r, aborts). The label layer is `SC` (labels = `Tg`,
  `SC.Ex` never sees raw immediates); the layout is `SC.flat` (to prove: a checked layout certificate + flat_ok).
- §2 buffers: my representation already uses fixed descriptors [len][cap][cap words] with the whole cap as footprint,
  bump allocated (no reuse of regions, discard never reused), so framing = interval disjointness as advised.

## Remaining (next round), in order
1. `cE_ok`/`cT_ok` (ONE induction over `Ex`/`Tl`) for the buffer-free fragment: bin, ite, let/pair/fst/snd/split
   (`slide` lemma), isize/iget, loop (via `loop_ok` with Inv n s := Stk (L ++ [fuel n] ++ flat state) ∧ env rep).
2. Buffers: heap invariant (live owned buffers: pairwise disjoint regions [a, a+16+8cap) below t5, each holding its
   Lean list; consumed variables carry no guarantee) with worker 1's affine check as hypothesis.
3. `SC.flat` correct w.r.t. a pc-level semantics of `I` (cf. Compiler/Ir/StructOk.lean `flatT_ok`), then `I.enc`
   on Sail (`G.step_*` from Riscv/Steps), then `ImplementsBytes` once worker 1 freezes it.
4. Align `Nano.V2B.Ex` with worker 1's frozen AST (or a proved translation).
- Gate: merged origin/main (c61d8eb); `bash Testing/scripts/check.sh` at c61d8eb: ALL CHECKS PASSED (only the
  pre-existing statement-fingerprint WARNING; no Nano declaration listed; not re-frozen). The later commits only add
  Nano/V2/{Blocks,Inp,Tail}.lean and notes: `lake build Nano` passes, forbidden-words scan of Nano/ clean.
- QEMU/Sail re-run after the last generator change: nv2_copy, nv2_copyfuel, nv2_copycap, nv2_mix all ok.
- NOT done this round (honest status): no end-to-end theorem yet. Proved: the abstract-machine semantics, the loop
  header theorem, and per-construct lemmas (lit, var, bin, ite, let, fst, isize, iget, loop tails, slide). Not
  started: buffers' heap invariant, `SC.flat` layout correctness, Sail refinement of the new instructions,
  `ImplementsBytes` (worker 1 has not frozen it; contract proposed above).
