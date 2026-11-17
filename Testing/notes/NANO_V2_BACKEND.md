# nano v2 small backend (worker 2, branch nano-v2-backend)

Owner of Nano/V2/* (except worker 1's spec files). Spec status: worker 1's NANO_V2_SPEC.md / origin/nano-v2 did NOT
exist when this round started (asked by message); the typed AST below is PROVISIONAL and will be adapted.

## Files
- Nano/V2/Lang.lean: typed AST `Ex`/`Tl` (words, owned `Array UInt64` buffers, fixed nested products, `ite` on
  unsigned comparisons, the ONE loop `loop fuel init z body` with `Tl.ret`/`Tl.next` tail positions, consuming
  `split`), Lean meaning `den`/`run`/`denT`, `Prog.eval : List UInt8 → Except UInt64 (List UInt8)`, typing `tyOf`.
- Nano/V2/Gen.lean: `cE`/`cT` → structured stack code `SC` (ins/seq/ite/loop/jmp) → `SC.flat` (instruction list,
  branch offsets resolved) → `I.enc` (RV64IM words). `gen p : Option (List UInt32)`.
- Nano/V2/Copy.lean: the byte copy (round 2 §7) as typed AST (`copyProg F C`) and as ordinary Lean (`copyLean`).
- Testing/asm/emit_nano_v2.lean, Testing/nano/v2_test.py: QEMU + Sail tests.

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
- 2026-11-17: byte copy end to end: 264 words. `python3 Testing/nano/v2_test.py nv2_copy|nv2_copyfuel|nv2_copycap`
  (after `lake env lean --run Testing/asm/emit_nano_v2.lean`): 20 inputs each ([0,127,128,255], empty, 1..101 bytes)
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
