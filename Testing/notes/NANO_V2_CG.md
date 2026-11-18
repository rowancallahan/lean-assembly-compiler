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
  number of buffers: Gen allocates 5 (r, o, k, t, f), each 8·(κ+2) bytes = 4 MiB at κ = 2^19.
  Memory map of a compiled program: work = [a2: saved ra][a2+8: saved s0][a2+16 …: heap, bump, each Buf = len, cap,
  κ words][… ↓ expression stack from the work end]; output at a3; tests now use BIG = 16 MiB.
- Whole chain on Par0's main-shaped output (Testing/nano/v2self/cg_par.lean, no hand-written AST): 4 sources
  (prims put/rd/len/bnew/bpush/bget/bset/bsize, let, if, arithmetic): accepted 4/4, QEMU == Sail == native Lean on
  5 inputs each (146–380 words).
- WHOLE SOURCE (Par1's dump Testing/nano/v2self/c_source_ast.bin = the OLD chain Lex/Parse/Inl/Expand/Asm/Main,
  90 defs, 14,619 words): first run stopped at def 28 on `LOCAL 1 0` (implicit input, width 0) — g43 now allows
  width 0; then ACCEPTED: 28,664 code words (`cg_whole.lean`, native 3 s).
  Since Par1 now DROPS width-0 locals (43c309b), g43 rejects width 0 again (strict; keeps Gen.lean == self_S, whose
  B₂ was built with the strict check); that old dump therefore no longer passes g41 — use self_S_ast.bin.
- g40/g42/g41 take the real input `c : List UInt8` FIRST (input convention), in Gen.lean itself; build_self_S.py
  no longer patches Gen (self_S regenerated from the files is byte-identical to the committed one).
- Heap budget of S = Base+Lex2+Par1+Gen+driver on its own source (static count of executed `bnew`s on the success
  path): lexer 1 (s10), parser 2 (y15 heap, v98 output), Gen 5 (r o k t f), output bytes 1 ⇒ 9 buffers.
  Largest: parser heap = 184,384 (layout) + 33,759 tokens + AST ≈ 233k words (needs κ ≥ 2^18; 2^19 gives 2.2×);
  Gen code Buf 28.7k words, output Buf 114.7k bytes = words. At κ = 2^19: 9 × 4 MiB = 36 MiB + stack ⇒ work 80 MiB
  gives > 2× headroom (QEMU run with 256 MiB). Decision per Astra-13 rule: fixed κ for the first self-compile.
- FIRST B₃ ATTEMPT (B2.bin @ 978c79f): B₂ crashes (pc → 0) on any input, at the start of the lexer. Traced with
  Testing/nano/v2self/rvtrace.py + cg_map.lean (def → code offset): Par1's AST of s9 (Lex2's fuel loop, npw 3) has
  CONTINUEs of width 1 (the `o` state word is lost, e.g. `s9 n x (p + 1) o` ⇒ CONTINUE (p+1)), so CONTINUE pops 2
  words, t6 drifts, a push overwrites the saved s0. Reported to the Sonnet box (Par1's width-0 PAIR drop).
- Width pre-pass in Gen (g44–g53, run before codegen): CONTINUE = npw−1, CALL Σ args = callee npw (callee nres
  as width), IF a, b = 1 and t = e, LET v = w, BIN/PRIM operands 1, LOOP arms = nres, def body = nres. The faulty
  AST is now REJECTED (empty output) instead of miscompiled; cg_chain has the regression pair (2-word CONTINUE
  accepted, 1-word rejected). 2 more buffers at run time (d, s). Witness re-proved (137 s, 3.9 GB).
- **SELF-COMPILE FIXED POINT (2026-11-18)**: with Par1's CONTINUE fix (5fcccd8) and Gen's width pre-pass, self_S
  regenerated from the files, B1 = Lean-compiled self_S (TRUSTED), B2 := B1(S) = 248,632 bytes (62,158 words),
  B3 := B2(S) on QEMU (64 MiB work, 1.6 s, a0 = 0): **B3 == B2 byte for byte**, sha256 2ceffa2c…2ebce
  (Testing/nano/v2self/B2.bin, B3.bin, B2.sha256). Reproduce: `Testing/nano/v2self/boot/fixpoint.sh OUTDIR`.
  Also B2(tiny source) == B1(tiny source) under rvtrace.py (5.5 M instructions).
- FAIL-LOUD ADDITIONS found while setting up the g39 proof (2026-11-18): Gen accepted, and MISCOMPILED, (a) a LOOP
  outside the def body (in a BIN / LET value / nested in an arm: its exits jump to the def epilogue, a nested head
  overwrites r[3]); (b) BIN op ∉ 1–8 (emitted xor), IF compare ∉ {1,2} (emitted bltu), PRIM ∉ 1–9 (emitted BPUSH).
  Now rejected: width pass (LOOP frame only directly under the root) and g36 (LOOP visited only as item 1 of the def;
  one operator-range check at the top).  cg_chain: valid 40/40 accepted, must-reject 13/13.  Fixed point re-run:
  B3 == B2 = 241,844 bytes, sha256 056aef1c…598af0e (B2.bin / B3.bin / B2.sha256 updated); Nano front end ACCEPTs
  Gen (69 defs); kernel witness cg_witness.lean re-proved (rc 0, peak 4.0 GB).
- MORE FAIL-LOUD FIXES from the g39 proof: (c) a tail-position LET (in a loop arm) skipped the g43 slot-range check
  (value-mode LET has it) ⇒ a pop outside the frame; (d) g36 normalized tags ≥ 12 as `c0 + 100`, so the tag 2^64 − 96
  wrapped to 4 and decoded as IF ⇒ now 999 (invalid).  cg_chain: valid 40/40, must-reject 15/15.  Fixed point:
  B3 == B2 = 242,208 bytes, sha256 a1970ad7…808ee1c; front end ACCEPT (69 defs); witness re-proved (rc 0).
- g39 PROOF STATUS (Nano/V2Self/Proof/GenRef.lean, no sorry, file 8 s / 1.8 GB): Reach (progress | error | code too
  big), item/fixup stacks as lists, the CG/CT/CGs reference relation over Gen's own emitter words; value-mode visits
  CONST, LOCAL, BIN, IF, LET, PAIR, CALL, PRIM proved (VS, given the IH for later cursors); operand sequences (seq).
  Technique notes: unfold Gen's big defs with `extract_lets` + `clear_value` (zeta-reduction blows up exponentially);
  never leave a `match` on an unreduced g19/g20 for defeq — rewrite with g19_eq/g20_eq first (kernel blowup otherwise).
- Hardening: B₃ identical with the work memory pre-filled 0xA5 / 0x5A (`FILL=` in selfrun.py); B₂ on a tiny source
  under Sail: QEMU == Sail == B1, writes only in output + work, OOM flag with 8-byte work.
- ASTRA-11 PROBE 2 (codegen, non-leaf call with a live stack value): `Nano/V2Self/Proof/Call.lean`, no sorry, axioms
  propext + Quot.sound, 3 s.  Abstract RV64 subset (`J`: addi ld sd jal jalr bgeu; word memory; non-wrap proved
  before every address use); templates exactly as Gen emits them: `push` (g21/g22, checked), `pro` (g38 prologue),
  `copy`/`epi` (g29 + g37 epilogue).  `call_live`: caller at `jal ra f` with p argument words on top of a live stack;
  callee body ABSTRACT (reaches the epilogue with q result words, keeps s0 and the saved ra/s0, writes nothing at or
  above the caller's pre-argument sp) ⇒ returns to c+1 with t6 = sp − 8q, s0 restored, every cell ≥ sp unchanged,
  result words copied in order (the copy moves UP over the args: a later source is never an earlier destination).
  Not yet: link `J` to Gen's word encoders (g1–g5) and to the Sail layer (nano-v2 `sim_*`); OOM exits; 12-bit
  immediate side conditions (Gen checks nslots, nres ≤ 250).
- ASTRA-11 PROBE 1 (parser, scoped let around a provisional self-call): `Nano/V2Self/Proof/ParLet.lean` (+ `BufL.lean`,
  the one checked-write lemma `bget_bset`), no sorry, axioms propext/choice/Quot.sound, 2 s.  On Par1's REAL code:
  `v2_low` (sibling linker writes only arena cells ≡ 7 mod 8), `v5_low`/`v5_fields` (node builder: low cells and
  operand stack untouched; new node's tag and PENDING field as given), `v118_scope` (task 12 restores the binding depth
  h[4] to the value saved by task 11: the let name leaves scope), `v118_pending` (the LET node carries the BODY's
  pending bit: a provisional self-call inside a let body stays marked for FINISH).  Finding: these need a heap
  invariant `OpsOK` (operand-stack ids < 16384) — Par1 indexes the arena with ids read from the heap in UInt64, so
  without it `d5 + 8·id + k` can wrap onto low cells; likewise v5's guard `8·h[9] + 7 < d6` passes for huge h[9]
  by wrap-around.  Both hold for heaps Par1 itself produces (ids < node count ≤ arena), to be carried by the
  parser invariant (Entry/Step obligations).
- nano-v2 merged into nano-v2-src (c5dd2a1): the Sail layer (Nano/V2/Enc, Sim, Flat) and Front's ownership fix are now
  here; self_S.lean still ACCEPT (186 defs; large files need `ulimit -s unlimited; lean --tstack=4000000 --run`).
- BRIDGE part 1 (encoders): `Nano/V2Self/Proof/Bridge.lean`, no sorry, standard axioms, 2 s.  C's g1 (R), g2 (I),
  g3 (S), g4 (B), g5 (J) produce exactly nano-v2's encR/encIt/encSt/encBt/encJt words with the signed immediate
  `sI v` (two's-complement reading of C's UInt64), hence g10 = addi, g11 = ld, g12 = sd, g4 = beq/bne/bltu/bgeu,
  g5 0 = jal x0 as `I.enc` — the words Enc/Sim tie to Sail; calls/returns go straight to Sail: `g5_wJ` (C's
  `jal rd` = `Proven.wJ rd o`, for `G.step_jal`) and `g2_jalr` (C's `jalr x0, rs` = the word of `G.step_jalr`).
  Still to do: lbu/sb/R-op corollaries, and the state link CallProbe.J ↔ nano-v2 St/pstep ↔ Sail (a
  code-agnostic `Rel`).
- BRIDGE part 2 (state link): `Nano/V2Self/Proof/SimW.lean`, no sorry, axioms = the Sail extern set + standard (same
  as nano-v2's sim_star), 4 s, 1.7 GB.  `RelW` (J state ↔ Sail: code as C's words at `base`, x0 = 0, J's code base
  `b` = base, work cells as 8 LE bytes).  Per instruction: sim_addi, sim_ld, sim_sd, sim_bgeu8, sim_jal (C's `g5`
  word, byte return address), sim_jalr (C's return word).  `encJ` = the word C emits per J instruction; `Safe` =
  the per-step side conditions (ranges, no wrap, work cells, aligned return); `sim_stepW` / `sim_starW`: a Safe J run
  on code `W = C.map encJ` is a run of retired Sail instructions keeping `RelW`.  J now carries the code base
  (`St.b`): `jal` stores `b + 4(pc+1)`, `jalr` jumps to `(x − b)/4` (call_live re-proved).  Not bridged yet: J's
  alu/slli/lbu (added for the expression templates; `Safe` is False for them until their sims exist).
- TEMPLATES (Opus box): `Nano/V2Self/Proof/Templates.lean`, no sorry.  Value contract `PV C pc len n V` (with n words
  of room the fragment pushes `V s`, keeps s0, t5 and every cell ≥ old t6; `V` stable under such changes).
  `if_eq` / `if_lt`: Gen's IF layout (A; B; pop2; beq/bltu t0,t1,+8; jal ELSE; T; jal END; E) pushes
  `if VA = VB (resp. VA < VB) then VT else VE`.  J gained `beq`/`bltu` (SimW: sim_beq8/sim_bltu8).
  Environment contract `EV C pc len n p nl R W V` (frame slots at `slotAddr p s0 k`: params above s0, locals below;
  `Frame` = slots hold env; the fragment pushes `V env`, V reads only slots in R, writes only frame slots in W, keeps
  s0/t5 and all other cells ≥ t6).  `let1` (LET width 1: value; pop into slot k0 (g26); body) proved, with the
  scoping side condition "the body reads none of the value's own lets" (from the parser's well-scopedness).
  EV has an invariant parameter `Inv` (input / heap / input-register facts; `InvOK`: Inv reads only x8, x28, x29,
  x30 and memory outside [t5, s0 + 8p + 16)) and x0 = 0.  `ifE_eq` / `ifE_lt`: IF under EV (room n+1 from n),
  scoping: B reads none of A's lets, T/E none of A's or B's.
  LOOP: `Nano/V2Self/Proof/Loop.lean` `loop_ok` (no sorry): Gen's head (ld fuel; beq fuel,x0,+2; jal STEP; zero arm)
  and STEP (fuel − 1 stored; step arm exits to E or CONTINUEs to HEAD), by induction on the fuel; arms, head
  invariant P and results abstract; result = inductive `LoopR` (zero / exit / cont).
  Multi-word values: contract `EVw` (w words, component i at t6 − 8(i+1)); `pairE` (PAIR = A ++ B), `letW` (LET of
  width w via `popN_run`, env updated by `setSlots`), `contE` (CONTINUE: state value, pop into slots 1..npw−1, jal
  HEAD; reaches HEAD with t6 restored and the frame = setSlots env' 1 (new state): loop_ok's continue branch).
  FIXUPS: `Nano/V2Self/Proof/Fixup.lean` (no sorry): `off_eq` (C's `(b − a) <<< 2` = ofInt 4(b − a)), `g13_encJ`
  (C's jump word = encJ (jal x0 (b − a))), `g20_ok` (patching placeholder p: length kept, word p = the jump to the
  current end, all other words unchanged), `g19_ok` (emit = append the jump).
  Next: the g39 work-item invariant (emitted code ↔ AST walk) that instantiates these templates.
- g39 INVARIANT (plan, Opus box): a ghost "pending tree" view of Gen's state (cursor i into the AST words, item stack
  k of (tag, a, b), emitted words o, fixup list f, registers r).  Invariant WI: (1) the AST suffix from i parses as a
  sequence of nodes whose pre-order matches the visit items on k; (2) every finished node N occupies a contiguous
  code block [start N, end N) of o that equals its template (`encG` of the J list) with jal placeholders recorded on
  k / f; (3) each pending item's patch target is the word index the template expects (IF items 3/4/5, LOOP STEP,
  exit fixups → epilogue).  Steps: one lemma per g36 visit case and per g37 item tag, preserving WI; at ENDDEF the
  def's words = `pro ++ body ++ epi` with all fixups patched (Fixup.g20_ok), so the templates (EV/EVw/IF/LET/LOOP/
  CONTINUE/CALL) apply bottom-up.  Width facts come from Gen's pre-pass (g53 = 1).  Heap prims via EVH (Sonnet).
- Next: the parser's real output (Sonnet box) through g41 as Par0 gains calls/prims/loops; a diff test against Nano.V2B `gen` on the v2f programs.
- EXPRESSION TEMPLATES PROVED (Sonnet box): `Nano/V2Self/Proof/Expr.lean` (+ `ExprExact.lean`), no sorry, standard axioms, ~5 s each.
  J (Proof/Call.lean) gained additive `alu` (Gen's BIN numbering), `slli`, `lbu` (byte of the aligned LE word cell).
  `const_run`/`const_oom` (CONST: li g23 incl. the 8-byte chain, then the checked push), `local_run`/`local_oom` (LOCAL w words,
  slot k<p at s0+16+8(p-1-k), k≥p at s0-8(k-p+1); the pushes in order), `bin_run` (all 8 ops through `aluf`; pops 2, result over the
  new top, exact register/memory state), `len_run`/`len_oom` (ISIZE/LEN), `rd_run` (index ≥ len ⇒ 0), `bsize_run`, `bget_run` (out of
  range ⇒ 0; buffer layout [len][cap][words…]).  Each: arbitrary live stack prefix (cells ≥ sp untouched, result cell exact), registers
  outside the scratch set unchanged (s0, t5, t3, t4 included), non-wrap side conditions explicit, capacity exit (`*_oom`) reaches the stub word.
  Exactness (`ExprExact.lean`): `encG` maps a template instruction to C's own encoder words; `g31_exact` (all 8 ops), `g22_exact` (push,
  with the position-dependent jal offset), `g32_len/len3/rd/bsize/bget`, `g23_exact` (li), `const_exact`, `g24_off`, `local_exact`:
  Gen's emitted words ARE `template.map encG`; with Bridge (encoders = nano-v2 `I.enc`) this ties the machine statements to the real code.
- Sonnet box (Proof/CallA.lean, CallExact.lean, ExprBridge.lean): `proA`/`pro_runA`/`call_liveA` — the prologue with Gen's REAL position-indexed
  capacity jumps (three different `jal` offsets to the stub word; `pro` in Call.lean uses one `oom` for all three, so its `At` premise cannot hold for
  emitted code; the old statements stay).  Exactness (Gen's words = template.map encG): `epi_exact` (g29 + tail + the two loads), `pro_exact`
  (g38's prologue = `proA 1 len r`), `popSlot_exact`, `ifHead_eq_exact`/`ifHead_lt_exact` (first four IF-head words + placeholder 0),
  `encG_encJ` (every template instruction's C word = the Nat word Sail/SimW consumes).
  NOTE: `g32` has no `p == 4` branch: PUT falls into the final `else`, i.e. BPUSH's code (pushes the whole word; the final output copy truncates
  to the low byte, so the semantics match `put`).  PUT = BPUSH in the proofs.
