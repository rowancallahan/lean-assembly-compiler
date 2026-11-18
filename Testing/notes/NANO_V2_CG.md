# NANO_V2_CG: C's fused code generator (Opus box) — `Nano/V2Self/C/Gen.lean`, entry `C.g41 : Buf → Buf`

Input = the parser's flat pre-order AST (NANO_V2_IR.md v2 with the Opus changes agreed 2026-11-17), output = RV64
machine-code bytes (little-endian words), or the EMPTY Buf on any unsupported form, a frame over 250 words, a result
over 250 words, a def id out of order, or a jump beyond ±1 MiB.

## Numeric tags (words)
Header `2` (IRV). Nodes: CONST 1 v | LOCAL 2 slot w | BIN 3 op a b (add 1 sub 2 mul 3 and 4 or 5 shl 6 shr 7 xor 8)
| IF 4 cmp a b t e (eq 1, lt 2 unsigned) | LET 5 slot w v body | PAIR 6 n c1..cn | CALL 8 id n a1..an
| PRIM 9 p args (ISIZE 1 [0 args], RD 2 [i], LEN 3 [0 args: the input length], PUT 4 [o b], BNEW 5 [0], BSIZE 6 [b],
BGET 7 [b i], BSET 8 [b i v], BPUSH 9 [b v]) | LOOP 10 zero step | CONTINUE 11 e.
Defs: `DEF 20 id npw nslots kind nres` body `END 21` (IR v2.1, FINAL; any other table is rejected; tag changes only after an entry in NANO_V2_IR.md); ids 0, 1, … in order (callees first); the LAST def is main
(npw 0, nres 1: the output buffer). A fuel def: slot 0 = fuel, state = slots 1..npw-1, body `LOOP zero step`,
`CONTINUE e` with e of width npw-1 (zero and step are both in TAIL mode: every leaf returns from the def).
`let (a, b) := v` = `LET slot w v body` (a at slot, b at slot + width a).

## Machine convention
t6 = expression stack (8-byte slots, downward; every push checks t6 ≥ t5), t5 = heap top (bump, buffers
`[len][cap][κ words]`; κ is a parameter: `g42 ast κ`, `g41 ast` = κ 2^19), s0 = frame pointer, t3/t4 = input base/length, a2 = work base (never
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
- Chain test (Testing/nano/v2self/cg_chain.lean N): random scalar defs (params, let, if, all BIN ops; Par0 increments A-C)
  → C.s10 → C.y13 → + hand-written main (4 args from input bytes + 64-bit constants, 8 result bytes) → C.g41.
  40 programs x 5 inputs: QEMU == native tree eval (40/40, `BIG=8388608 NOSAIL=1 cg_test.py cgc_K`); Sail also on
  cgc_0/6/13 (483-1737 words). Note: work must hold the κ = 2^18 buffers (≥ 2 MiB each); 4 KiB work ⇒ a0 = −1 by design.
- Astra-10 "rule out now" audit of Gen.lean (fail loudly instead of silent truncation): fixed-fuel loops now reject
  instead of cutting off — LOCAL/LET slot ranges must be non-empty and inside nslots (g43), PAIR/CALL arity ≤ 250,
  ≤ 65536 exit fixups per def, code < 2^24 words; the LAST def must be main-shaped (npw 0, nres 1). Already true:
  every r[] field initialised in g42; fixup buffer and count reset per def; def ids by source order (`d == bsize t`);
  output = exactly 4 bytes per code word (no padding); only pc-relative jal/branches (no work addresses); κ one
  parameter (`g42 ast κ`). NOT checked by Gen (no types in the IR): CALL argument widths vs callee npw, CONTINUE
  width vs npw−1 — the parser must guarantee them. Capacity note for B₂: the output Buf holds 4 entries per code word,
  so compiled C at κ = 2^18 emits at most 65536 code words (status −2 beyond).
- Stage dump for B₁ vs B₂ vs B₃: `lean --run Testing/nano/v2self/stage_dump.lean SRC OUT` → OUT.tok / OUT.ast /
  OUT.code (one hex word per line); fixups are internal to g39 and not dumped.
- Non-vacuity (owner rule): cg_chain reports acceptance separately — valid programs accepted 40/40 (a rejection
  throws = FAILURE), must-reject 4/4 (no main, slot outside frame, main with npw 1); QEMU 40/40.
- Formal acceptance witness Testing/nano/v2self/cg_witness.lean: `theorem w1 : C.g41 (w1ast ++ w1main) = w1code`
  by `decide +kernel` (file 196 s incl. the `#guard` parser run, 3.7 GB; needs `--tstack=4000000`, `ulimit -s unlimited`), with w1ast = Par0's output
  on a let/if/mul/shift source (`#guard`, compiled). The kernel run of the PARSER stage is killed at 13.6 GB: Par0's
  fixed layout (offsets 10000/30000/40000 words) makes kernel lists that long; a layout sized by the input would fix it.
- Capacity (self-compile): C's own source ≈ 12k tokens now (Base 40, Lex2 1985, Par0 4554, Gen 5583), ≈ 20k once
  Par0 is complete; measured ≈ 4.2 code words per AST word (+ ~120 words of stubs/start) ⇒ ≈ 100k code words.
  Changes: g41/g42 now return `List UInt8` directly (bytes `put` to the output, no 4×-sized byte Buf — that Buf
  capped the output at κ/4 = 65536 words); the code-word Buf caps at κ; default κ = 2^19 (524288 words, ≈ 5×
  headroom); the per-def `bnew` for the fixup buffer is gone (g28 threads it as state), so C's own heap is a fixed
  number of buffers: Gen allocates 5 (r, o, k, t, f) + the stubs' buffer, each 8·(κ+2) bytes = 4 MiB at κ = 2^19.
  Memory map of a compiled program: work = [a2: saved ra][a2+8: saved s0][a2+16 …: heap, bump, each Buf = len, cap,
  κ words][… ↓ expression stack from the work end]; output at a3; tests now use BIG = 16 MiB.
- Whole chain on Par0's main-shaped output (Testing/nano/v2self/cg_par.lean, no hand-written AST): 4 sources
  (prims put/rd/len/bnew/bpush/bget/bset/bsize, let, if, arithmetic): accepted 4/4, QEMU == Sail == native Lean on
  5 inputs each (146–380 words).
- Next: the parser's real output (Sonnet box) through g41 as Par0 gains calls/prims/loops; a diff test against Nano.V2B `gen` on the v2f programs.
