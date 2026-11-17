# NANO_V2_CG: C's fused code generator (Opus box) — `Nano/V2Self/C/Gen.lean`, entry `C.g41 : Buf → Buf`

Input = the parser's flat pre-order AST (NANO_V2_IR.md v2 with the Opus changes agreed 2026-11-17), output = RV64
machine-code bytes (little-endian words), or the EMPTY Buf on any unsupported form, a frame over 250 words, a result
over 250 words, a def id out of order, or a jump beyond ±1 MiB.

## Numeric tags (words)
Header `2` (IRV). Nodes: CONST 1 v | LOCAL 2 slot w | BIN 3 op a b (add 1 sub 2 mul 3 and 4 or 5 shl 6 shr 7 xor 8)
| IF 4 cmp a b t e (eq 1, lt 2 unsigned) | LET 5 slot w v body | PAIR 6 n c1..cn | CALL 8 id n a1..an
| PRIM 9 p args (ISIZE 1 [0 args], RD 2 [i], LEN 3 [0 args: the input length], PUT 4 [o b], BNEW 5 [0], BSIZE 6 [b],
BGET 7 [b i], BSET 8 [b i v], BPUSH 9 [b v]) | LOOP 10 zero step | CONTINUE 11 e.
Defs: `DEF 20 id npw nslots kind nres` body `END 21` (FINAL: IR v2.1, emitted by Par0; agreed 2026-11-17 23:45, no further changes); ids 0, 1, … in order (callees first); the LAST def is main
(npw 0, nres 1: the output buffer). A fuel def: slot 0 = fuel, state = slots 1..npw-1, body `LOOP zero step`,
`CONTINUE e` with e of width npw-1 (zero and step are both in TAIL mode: every leaf returns from the def).
`let (a, b) := v` = `LET slot w v body` (a at slot, b at slot + width a).

## Machine convention
t6 = expression stack (8-byte slots, downward; every push checks t6 ≥ t5), t5 = heap top (bump, buffers
`[len][cap][κ words]`; κ is a parameter: `g42 ast κ`, `g41 ast` = κ 2^18), s0 = frame pointer, t3/t4 = input base/length, a2 = work base (never
written: [a2] = caller ra, [a2+8] = caller s0, heap from a2+16), a3 = output. Call: args pushed (first deepest),
`jal ra`; callee pushes ra, s0, `s0 := t6`, reserves nslots-npw words; slot k < npw at s0+16+8(npw-1-k), k ≥ npw at
s0-8(k-npw+1); epilogue copies the nres result words over the args, t6 just below them, restores s0, `jalr ra`.
Loops: head reloads the fuel slot, `beq fuel, x0, +8; jal STEP`, zero arm, STEP: fuel-1 stored, step arm;
CONTINUE pushes the whole new state, then pops it into slots npw-1..1, `jal head`. Branches: short inverted branch over
a long `jal` (label fixups by `bset`). Exits: a0 = 0 / a1 = length / bytes at a3; empty output ⇒ a0 = 1, a1 = 0;
out of work memory ⇒ a0 = −1 (also when work < 16 bytes, before any write); capacity ⇒ a0 = −2.
Written registers: t0–t6, a0, a1, a4, a5, s0 (restored), ra (restored).

## Status
- Vertical example (Testing/nano/v2self/cg_vertical.lean: a fuel loop copying the input into a buffer, a helper
  with its own loop returning a pair, output): QEMU == Sail == native Lean on 5 inputs + the out-of-memory case
  (`BIG=2097152 python3 Testing/nano/v2self/cg_test.py cg_vertical`), 476 words.
- Gen.lean ACCEPTED by nano's front end (check.lean: 58 defs).
- Next: the parser's real output (Sonnet box) through g41; a diff test against Nano.V2B `gen` on the v2f programs.
