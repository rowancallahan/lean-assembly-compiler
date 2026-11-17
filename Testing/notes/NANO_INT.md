# nano integration (branch `nano-int`): closing the loop on proven self-hosting

Integrator notes. Branch = `nano-mvp` + `nano-e2e` + `nano-proof` + `main`, merged every 30–45 min.

## Summary (state at the end of the integration session, 2026-11-17)

**Target** (`Nano/SelfHost.lean`, `SelfHosted B space D compile`): `B` = ONE RISC-V binary made by our compiler from
the nano compiler `asm ∘ genR ∘ nanoElab`; for every source `src` (in the size domain `D`) with `nanoElab src = some p`:
`B` on the Sail model, run on `src`, emits `c.code = asm (genR p)`; that code on the Sail model computes `p.eval` /
`p.evalI` on every input (`CompileCorrect` form) and sets the out-of-memory flag exactly when the work block is too
small (`CompileRuns` form).

**Status: NOT closed. Proved today, all with exactly the Sail axioms, no sorry:**
1. (L2, lane nano-proof) `nano_stack_correct : CompileCorrect riscv nanoCompileA`, `nano_stack_runs : CompileRuns riscv
   nanoCompileA` (`Nano/StackTop.lean`); `nanoCompileA p = some ⟨asm (genR p), 8, …⟩` for scoped programs of stack
   depth ≤ 256. UInt64 and Int64 source-level forms: `nano_stack_chain`, `nano_stack_chain_int` (`Nano/Chain.lean`).
2. (composition, this lane) `selfHosted_stack`: the target follows from (L1) alone, i.e. from a binary `B` with
   `Implements1With` for a byte function `cb` such that `cb src = asm (genR p)` on accepted sources.
   `selfHosted_stack_stages`: the same from three separately compiled stages (front end → generator → assembler),
   linked by `Nano.Link.link` (`link_implements`: an 18-word stub, two stages → one binary, machine proof; tested on
   QEMU + Sail). `of_pg`: stages compiled by the paged front end (stack available) link too.
3. (L1, partial) `selfHosted_asm_stage` (`Nano/SelfHostAsm.lean`): the composed statement with the part that is
   machine code today = the assembler (`Nano.Self.nanoAsm.implements1`, lane nano-e2e): the compiled `asm` on Sail,
   run on `genR p`, emits `c.code`; `c.code` on Sail computes `p.eval`; flag iff out of memory.

**What remains for the target: (L1) for the front end**, i.e. `genR ∘ nanoElab` (text → records) as machine code:
* `genR p = mexp (ser p)` is proved (`Nano/Ser.lean`); `mexp` (micro-op expander) is a list-front-end function whose
  compile is slow (see log); so what is missing is a compiled chain `src ↦ ser p` (or `↦ genR p`).
* lane nano-elab: stage 1 (lexer + type check) proved equal to the spec for every input, compile in progress; the
  parser / scopes / inlining stage is NOT started. It needs unbounded memory (a return path per inlined call), so it
  cannot be a list-front-end stage; decision here: compile it with the paged front end (`wp_compile`), probe
  `Testing/nano/wp_stack_probe.lean` shows the accepted shape and its limits (log, 00:20).
* then one Lean lemma `nanoElab src = some p → chain src = ser p` and one application of `selfHosted_stack_stages`.

**Trusted base**: `nanoElab` / `Prog.eval` / `Prog.evalI` (the spec of nano, cross-checked against Lean's elaborator
by agreement proofs and fuzzing, never proved), the Sail RISC-V model, the statements in `Spec/` and
`Compiler/AllocSpec.lean`, Lean's kernel.

**Reduction proved here (pure Lean + linker)**: `selfHosted_four` (`Nano/SelfHostChain.lean`): the target follows from
four stage machine theorems with exact byte specs — front end `src ↦ serU u` (NON-inlining; `nanoElab_eq`, `chain_eq`),
inliner `inlB`, expander `mexp`, assembler `asm` (exists). Alternative with three stages: `selfHosted_stack_stages`
(a parser that emits `ser p` directly, lane nano-parse).

**Final state (2026-11-17 04:20, tree e122335 + this note)**: `bash Testing/scripts/check.sh`: ALL CHECKS PASSED
(statement-fingerprint WARNING only, not re-frozen). `chain_test.py 4`: 92 sources, Lean accepts 85, nanoElab 82, 0
mismatches; P 328 pairs and S (through the compiled `asm` binary) 328 pairs on QEMU + Sail incl. the OOM flag.
`link_test.py 6`: 45 cases QEMU == Sail == Lean. Two stage compiles are parked in `Testing/nano/pending/` (lexer
`ElabBSelf`: standalone compile restarted 04:01, still running after 20 CPU-min, NOT confirmed; `ExpandSelf`: to redo).

## Live status (2026-11-17 00:00)
Lanes: nano-e2e (Sonnet: elaborator rules, `asm`, tests), nano-elab (Opus: `nanoElab` as compiled byte-level stages),
nano-proof (Opus: L2), nano-mvp (finished: Int64, Chain, chain_test), nano-int (this: glue, linker, composition).
| piece | state |
|---|---|
| L1 `asm` compiled, machine theorem | done: `Nano.Self.nanoAsm.implements1` (15-op table, nano-e2e c06682c) |
| L1 `genR` | `genR p = mexp (ser p)` proved (`Nano/Ser.lean`); `mexp` (micro-op expander) compile running since 23:47 (slow: 124 stored bytes); alternative: the front-end chain emits `genR p` directly |
| L1 `nanoElab` | nano-elab: stage 1 (lexer + type check, `lexB`) proved equal to the spec for every input, being reworked for e2e's lexer and compiled; stage 2 (parser, scopes, inlining → `ser p`) NOT started: needs a stack, so the paged front end (decision below) |
| L1 one binary from the stages | glue done: `link_implements`, `link_stage`, `of_pg` (paged stages), `out_bytes`; tested on QEMU + Sail (`link_test.py`, 45 cases) |
| L1 partial instance | `Nano.SelfHost.asm_stage_emits`: the compiled `asm` on Sail, run on `genR p`, emits `nanoGen p` |
| L2 stack generator `asm ∘ genR` correct | nano-proof: whole `genR p` on the record machine, both outcomes (`genR_ok`, `genR_oom`); record → word families (`StackFam`); Sail refinement in progress (`StackSail`, `StackSim`); glue to `CompileCorrect`/`CompileRuns` open |
| composition `Nano/SelfHost.lean` | `SelfHosted`, `selfHosted_of` (from L1 + L2), `selfHosted_stages` (three stage theorems + L2) proved; instance waits for L1 (parser stage) and L2 |
| tests (merged tree 7e134c9) | `chain_test.py 4`: 92 sources, Lean accepts 85, nanoElab 82 (0 mismatches); P 328 pairs QEMU+Sail; S 82 programs through the compiled `asm` binary, 328 pairs QEMU+Sail incl. OOM flag. `nano_s_test.sh`: 936 pairs. `link_test.py 6`: 45 cases. `check.sh`: ALL CHECKS PASSED |

## Naming (one consistent set; follows the lanes' latest pushes, 22:16–22:24)
* `genR`, `nanoGen = asm ∘ genR`, `nanoCompile`: the stack generator = the SELF-HOSTED path (`Nano/Gen.lean`, nano-e2e).
  (The owner prompt calls these `nanoGenS`/`nanoCompileS`.)
* `nanoGenIR`, `nanoCompileIR`, `nanoCompileSrcIR` (`Nano/GenIR.lean`, `ProofTop.lean`, `ProofSrc.lean`, nano-proof):
  the PROVED IR-route generator; noncomputable, not the self-hosted path. `Nano/Chain.lean` (nano-mvp) still said
  `nanoGen`/`nanoCompile` for it: renamed here to the `…IR` names; `nanoCompileSrc` (Chain) kept.
* `Nano.Self.*`: stages compiled by the big compiler (`….implements1`). `Nano.Link.*`: linking. `Nano.SelfHost.*`: the target.

## Decisions
* 2026-11-16 22:15. Critical-path gap found: the front end cannot compile a composition of passes as one entry
  (TINYSELF2 F11), so ONE binary `B` for `asm ∘ genR ∘ nanoElab` needs a linker with a machine proof. Done here:
  `Nano/Link.lean`, `link cf cg` = 18-word stub ++ `cg` ++ `cf`; `link_implements`: `Implements1With` for `f` (with
  `retLen = true`) and for `g` give `Implements1With` for `g ∘ f`, work space `4 * M n + 96` where `M n` bounds the
  intermediate length and both stages' work space; needs `cg.length < 2^17` (one `jal`) and the intermediate result
  within `g`'s input bound. The result is again `Implements1With`, so three stages = two links. Axioms = the Sail set.
  Design notes: `f`'s output block and work, the stub's 32-byte frame and `g`'s work are four disjoint parts of the work
  block (`Implements1With` does not say the work block stays mapped after a call, so `g` gets a part `f` never touched);
  `g` is entered by fall-through with the caller's `ra`/`a3`/`sp`, so no epilogue.
* Consequence for the lanes: every stage but the last must be compiled with `retLen = true`; intermediate encodings must
  be byte lists whose length is bounded by a function of the input length (inlining in `genR` is exponential in call
  nesting, so the target will carry a size hypothesis or the stages a larger `maxLen`).
* 2026-11-16 22:40. Merge of nano-e2e 4c64d61, nano-proof 1b1c4fe, nano-mvp 6374c37. `expected-axioms.txt` conflicts
  resolved with `Testing/nano/fix_axioms_conflict.py` (keep both sides, theirs first = check.sh's loop order).
  `Nano/AsmSelf.lean` does not build (see table); everything else in `Nano` builds. Sent the e2e session the linking
  interface (retLen = true for non-final stages, output-length bounds).
* `Nano/SelfHost.lean`: `SelfHosted B space D compile` (fields `code`, `emits`, `correct`, `correctInt`, `runs`) and
  `selfHosted_of` from (L1) `Implements1With` for a byte function `cb` on the domain `D` with `cb src = nanoGen p`,
  (L2) `CompileCorrect`/`CompileRuns riscv compile` with `c.code = nanoGen p`. `D` = the size side conditions.
* 2026-11-16 22:45. Merged nano-proof 777323f (`Nano/StackRec.lean`: record machine, `genE_ok`/`genA_ok`). Its `Nano.S`
  is a copy of `Nano/Gen.lean`; instead of editing either lane's file, `Nano/Bridge.lean` proves `S.genR p = genR p`
  and `S.depth p = depth p` (and the pieces), so nano-proof can keep its copy and the composition uses e2e's `genR`.
* `Nano.Link.link_stage`/`comap`: the linker for stages in the front end's theorem form
  (`Implements1With (·.data.toList) id code f space (2^20) true`, as `frontx_implements_listC` produces).
* 2026-11-16 22:50–23:00. e2e 017698f renumbered the record opcodes (to get the 15-op `asm` through the front end);
  told nano-proof (retargeted in c3c6b2b, now imports `Nano/Gen.lean`; Bridge dropped) and asked e2e to freeze the
  record format. Both e2e and mvp had tightened `nanoElab` differently: e2e's `Nano/Elab.lean` taken whole (mvp did the
  same in b6f978a). Merged main b07a0b9 (check.sh loop: `conleche-hard` before the nano files).
  `Testing/nano/regen_nano_axioms.py`: regenerates the nano tail of expected-axioms.txt after checking every line
  (Sail set or ⊆ {propext, Classical.choice, Quot.sound}).
* 2026-11-16 23:05. TAKEN OVER from the e2e lane (it is active but on elaborator fuzzing): the compiled `genR` stage.
  Design: `genR` is a tree walk (postfix emission, stack-relative slots, inlined calls) that the list front end cannot
  compile, but its OUTPUT is a flat postfix stream. So `genR = mexp ∘ ser`: `ser : Prog → List UInt8` (plain Lean,
  mirrors `genR`) emits 2-byte micro-ops; `mexp` expands a micro-op to 1–5 records and is a one-pass byte function
  (compilable like `asm`). The tree walk moves into `ser`, i.e. into the front-end stage: a one-pass byte-level
  elaborator has to emit `ser p` directly (`serE` of a callee body is call-site independent, so inlining = copying).
  Honest reading: after this, what is NOT yet compiled by our compiler is `ser ∘ nanoElab` (text → micro-ops).
* 2026-11-16 23:45. `bash Testing/scripts/check.sh` on the merged tree 7e134c9: ALL CHECKS PASSED (statement-fingerprint
  WARNING only, not re-frozen). nano-proof fast-forwarded onto nano-int (9c7590a: `genR_ok`/`genR_oom` on the record
  machine, `Nano/StackFam.lean` record → word families).
* LINKER TEST on machines: `python3 Testing/nano/link_test.py 6` — the binary `link nanoAsm.code nanoAsm.code` (776
  words; computes `asm ∘ asm`, theorem `link_stage`) on QEMU and Sail == executed Lean for 45 inputs (records of the
  corpus + 6 random programs, up to 1592 bytes), work space exactly the theorem's `4 K + 96` (rounded up to 8), a1 =
  length, sp/gp restored, every Sail write inside output + work.
* Compile-time finding for stages in the list front end: cost grows fast with the number of stored constant bytes per
  arm. `asm` (4 bytes per record, 4 table expressions): ~80 s. A 3-arm pass with one 20-byte arm: > 20 CPU-min for
  `frontx_compile` alone (stopped). `mexp` (13 arms, 124 stored bytes): running detached since 23:47
  (`Nano/ExpandSelf.lean`, not committed until it finishes).
* 2026-11-16 23:55. Two NEW lanes found (started by the main session): `nano-elab` (Opus, since 22:45: `nanoElab` as
  byte-level stages; stage 1 = lexer + type check `lexB`, proved equal to the spec for every input, compile in
  progress) and a fresh L2 box on `nano-proof` (since 23:22). nano-elab's finding (NANO_ELAB.md): the parser stage
  cannot be a list-front-end stage, nor a fixed chain of them: such a stage is a log-space transducer (constant
  scalars, read-only input, write-only output), and inlining needs a return path of unbounded depth (and can be
  exponentially long). It asks the owner / integrator to choose: (a) non-inlined `Prog` + real calls, or (b) a
  writable array in the list path.
  DECISION (integrator): neither. Keep the spec (`nanoElab`, inlined `Prog`) and L2 (inlining stack generator) as they
  are; the stage that needs a stack is compiled by the PAGED front end (`wp_compile`: growing `ByteArray`, in-place
  updates), which already exists, and is linked like any other stage. Glue done: `Nano.Link.of_pg`
  (`Nano/LinkPg.lean`): a paged stage's theorem `Implements1Pg … 8192 fits …` gives `Implements1With … space …` for
  any `space` under which the run fits, so `link_stage`/`link_implements` compose it with the list-path stages
  (lexer before, `asm` after). Reasons: (a) would discard the L2 proof in progress and still needs a stack for
  precedence / parentheses; (b) is a big-compiler feature (not to be modified here). Target of the front-end chain:
  `ser p` (`Nano/Ser.lean`) or directly `genR p`; needed only for accepted sources (`nanoElab src = some p`).
  Open risk, stated: whether `wp_compile` (single flat loops, one work array per loop state) accepts an explicit-stack
  parser; that is the nano-elab lane's next experiment.
* 2026-11-17 00:20. PROBE of the open risk (parser stage on the paged front end): `Testing/nano/wp_stack_probe.lean`.
  `wp_compile` ACCEPTS an explicit-stack machine (stack cells written with `set!` inside the growing output buffer,
  `sp` scalar), with `….compiles` / `….computes` (Sail axioms only), in this shape and only in this shape:
  1. ONE tail call per step; every state component is a conditional EXPRESSION (`rpn (if … then buf.set! … else …) src
     (…) (…)`). Branching between different calls (`if c then go a else go b`, nested) fails in the generated step
     proof (`Dependent elimination failed … Decidable.rec`); so does mixing calls and the result below the top `if`.
  2. The top-level shape is `if i < src.size then <one call> else buf` (a disjunctive loop condition with an inner
     `if i < src.size` fails the same way).
  3. Side conditions (invariant, measure, `< 2^64`) are closed by a fixed tactic (split, then omega). It worked with:
     every step consumes exactly one input byte (`i + 1`), pushes a FIXED number of bytes (pad with 0 and strip in a
     later list-path pass), invariant `sp ≤ i ∧ i ≤ src.size ∧ buf.size + 2 * (src.size - i) ≤ C ∧ src.size < 2^32`,
     measure `src.size - i`; `sp` itself may be a nested conditional. Conditional `i` / variable push counts with a
     lexicographic measure left goals open (`x2 - 1 < x2`, size goals) in my attempts.
  4. Body size: the plain back end's loop-exit branch limits a body to ~1000 words and paged array accesses are large;
     the probe's body already exceeds it (`decide` on `wfB` fails). An arithmetic `mop` in the body (`i + 1 + 0 * sp`)
     switches `wp_compile` to the checked words (`compBFC`, `pickC`), which passed.
  Consequence for the design: O(1) stack work per input byte (fine for nano's three precedence levels and parentheses);
  unbounded work per token (scope lookup, copying a callee body) must be done by rescanning list-path stages before
  (name → index, arity) or needs steps that do not consume input (not yet working with the fixed tactic).
* 2026-11-17 00:30. PROBE 2, `Testing/nano/wp_copy_probe.lean`: steps that do NOT consume input also pass `wp_compile`
  (3 min): copy mode `0 < rem` (push `buf.get! cp`, `rem - 1`, `cp + 1`, `i` unchanged), else consume one byte and set
  `rem`; measure `(src.size - i) * 4 + rem`, invariant `rem < 4 ∧ cp + rem ≤ 3 ∧ …`; every step pushes exactly ONE
  byte (branch-free size), every condition is the simple `0 < rem`. So inlining by copying an earlier part of the
  output buffer is expressible in a paged stage (bound the copy length with `% C` so the invariant `rem < C` is
  provable without facts about memory contents). What made the earlier attempts fail was a size that depends on the
  branch (conditional `push` vs `set!`): the fixed tactic simplifies sizes before splitting, not after.
* 2026-11-17 00:45. `Nano/ElabU.lean` (pure Lean, 3 standard axioms): the NON-INLINED elaboration. `nanoElabU` runs the
  spec's own parser functions (`pExpr` … of `Nano/Elab.lean`, unchanged) with a def table whose bodies are index
  markers (`Ex.var j` for def `j`), so a call is `Ex.call (Ex.var j) args` and the output is linear in the source;
  `inlineProg` replaces the markers. **`nanoElab_eq : nanoElab xs = (nanoElabU xs).map inlineProg`** (via `par`: the
  seven mutual parser functions commute with replacing def bodies). Consequence: the compiled parser stage need not
  inline (its output is linear, so it is log space again); inlining becomes its own stage (copying, paged front
  end, probe 2). nano-elab's option (a), but only as an internal intermediate: spec, generator and L2 unchanged.
* 2026-11-17 01:00. `Nano/SerU.lean` (pure Lean, standard axioms): the byte format of the non-inlined program and the
  inliner on bytes. `serU u`: per def (oldest first) the body's micro-ops (as `serE`; a call = arguments,
  `[14, j / 256] [15, j % 256]`, `[9, arity]`), closed by `[13, arity]`. `inlB`: copy micro-ops, replace a 14/15 pair
  by the already inlined body code of def `j`, wrap the last def as a program. **`inlB_serU : WF u → u ≠ [] → inlB
  (serU u) = ser (inlineProg u)`** and **`genR_chain : nanoElabU xs = some u → nanoElab xs = some p → WF u → mexp
  (inlB (serU u)) = genR p`**. Key lemma `serE_shift` / `body_code`: the code of a scoped body does not depend on the
  stack depth of the call site, so inlining is byte copying. `WF u`: bodies scoped, calls to earlier defs with the
  right argument count, callee numbers < 65536, arities < 256 (the last two are size conditions for the domain `D`).
  So the front-end chain is now, stage by stage, with every Lean-level equation proved:
  `src —[lexer + NON-inlining parser: to do, nano-elab]→ serU u —[inlB: to compile, paged]→ ser p —[mexp: compile
  running]→ genR p —[asm: compiled]→ code`.
* 2026-11-17 01:30. `Nano/ElabUWF.lean`: `pwf` (what the seven parser functions return is well formed, by the same
  fuel induction as `par`), `nanoElabU_wf`, **`chain_eq : nanoElab xs = some p → ∃ u, nanoElabU xs = some u ∧ (arities
  < 256 → at most 65536 defs → asm (mexp (inlB (serU u))) = nanoGen p)`**. `Nano/SelfHostChain.lean`:
  **`selfHosted_four`**: the target `SelfHosted (link (link (link ce ci) cm) ca) … (Sized K …) nanoCompileA` from four
  stage machine theorems with these exact function specs: `fe src = serU u` whenever `nanoElabU src = some u`
  (front end: lexer + NON-inlining parser), `fi = inlB` (inliner), `fm = mexp` (expander), `fa = asm` (assembler,
  exists). `Sized`: arities < 256, ≤ 65536 defs, intermediate streams ≤ 2^20 bytes and ≤ K, stage work spaces ≤ K.
  Everything except the three missing stage theorems is proved (Sail axioms only).
* 2026-11-17 03:35 (after a 3 h pause: usage limit, every lane stopped at 00:33). Merged main cd78e4f (check.sh loop:
  `round1`), nano-proof df5f32e, nano-parse 30b1d99 (NEW lane, Opus: `Nano/ParseB.lean`, the parser as an
  explicit-stack machine on decoded tokens that emits `ser p` directly, inlining by copy; Lean-side check 3000 inputs,
  0 mismatches; no proof, not compiled yet). Note for that lane: `Nano/ElabU.lean`, `SerU.lean`, `ElabUWF.lean` here
  give a proved alternative target for the parser (`serU u`, no inlining) and the parser lemmas `par`, `pwf`,
  `pParams_len`, `nanoElab_eq`, `serE_shift`/`body_code`; `selfHosted_four` composes four stages, and
  `selfHosted_stack_stages` three (parser emitting `ser p` directly + `mexp` + `asm`, with the lexer linked in front).
* PARKED out of the `Nano` lib (so `lake build Nano` / check.sh finish): `Testing/nano/pending/ElabBSelf.lean.txt`
  (nano-elab's lexer stage compile: its box was archived while the compile was running, > 22 CPU-min, not confirmed to
  build; standalone build attempt started 03:36, result below) and `Testing/nano/pending/ExpandSelf.lean.txt` (the
  `mexp` compile: ran 47 CPU-min without finishing before the pause, and `mexp`'s HDR arm changed since with L2's
  aligned prologue, so it must be redone; recommended form: split into passes with ≤ 4 stored bytes per arm, or a
  paged uniform-step machine). Move a file back to `Nano/` when it is known to build.
