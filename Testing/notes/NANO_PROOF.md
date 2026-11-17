# nano code generator and its proof (branch nano-proof)

Owner of `nanoGenIR : Prog → List UInt8` (Nano/GenIR.lean) and its proof (Nano/Proof*.lean).
nano-e2e had no `nanoGenIR` when this branch started; this one is new (same name/signature as the ROADMAP).

## Route: (b) lower to the IR, reuse `ir_compile_correct`'s machine theorem
- Why: `Riscv/Frontx/IndIr.lean` already instantiates `CompileCorrect`/`CompileRuns` through `Ir.compile` +
  `Ir.machine_run`; the structured-code layer (`SC`/`TC`, `flatT_ok`) and the inductive path's helpers (`rd8_ok`:
  8 LE input bytes → word, `wout_loop`: word → 8 LE output bytes) are reusable as is. Only nano → IR needs proving
  (straight-line code, no loops), versus re-proving register allocation/branches against Sail in route (a).
- Lowering (`Nano.lower`): one function `main`, one region; parameters read with `rd8`, expression to fresh virtual
  registers (`cE`/`cA`, mutual like `den`/`denA`), calls INLINED (the AST already carries the callee body), result
  written with `wStep`. All vregs live in frame slots (trivial allocation), so code size and frame grow with the
  inlined tree (exponential in call-nesting for DAG-shaped call graphs). Acceptable for v1.
- Self-hosting gap: `nanoGenIR` calls `Ir.compileW` (allocation, layout, emission of the big compiler). It is plain
  Lean but not yet compiled by our front end; the v2 fixed point needs either that or a raw emitter (route (a)) for
  the straight-line subset proved against the same `lower` meaning.

## Spec instantiation
`Program Nano.Prog`: `nanoRun p input` = words of the input (8-byte LE, exactly `arity` of them, `wordsOf`), then
`Prog.eval`, output `leN 8 v.toNat`.

## Log
- 2026-11-16: `Nano/GenIR.lean` (`cE`/`cA`, `ldArgs`, `mainTC`, `lower`, `nanoGenIR`), `Nano/Proof.lean` (`nanoRun`,
  `Program Prog` instance, `cE_ok`/`cA_ok`, `ldArgs_ok`, `lower_ok`), `Nano/ProofTop.lean` (`nanoCompileIR`,
  `nanoGenIR_code`, **`nano_compile_correct : CompileCorrect riscv nanoCompileIR`**, **`nano_compile_runs : CompileRuns
  riscv nanoCompileIR`**). Axioms: machine theorems = the Sail set (same as `ir_compile_correct`), `lower_ok` ⊆
  {propext, Classical.choice, Quot.sound}. `Testing/scripts/axioms_nano-proof.lean` added to check.sh's loop;
  check.sh also builds `Nano` and greps `Nano/*.lean` for forbidden words (decided: the nano files are proof sources).
- 2026-11-16: register reuse. The IR back end allows at most 254 frame slots (`maxSlots`, one per vreg), so the
  first lowering (a fresh register per node) failed to compile programs with > ~240 nodes (`nanoGenIR` = []). Now a
  compound expression leaves its value in its first fresh register (`.let_ nx ...`); registers grow with the nesting
  depth only. Limit that remains: nesting depth + arity + 10 ≤ 254 (else `nanoCompileIR p = none`, `nanoGenIR p = []`).
- Tests: `Testing/asm/nano_test.sh` (emit with `Testing/asm/emit_nano.lean` → `ir-words/nano_*`, gitignored;
  `ir_test.py` on QEMU + Sail at `memoryNeeded` and `memoryNeeded - 1`). 39 programs (6 full trees of depth 5–10,
  up to 4146 words; 30 random with lets, calls, out-of-range variables; 3 sources through `nanoElab`) × 8 inputs
  = **312 program×input pairs**: QEMU == Sail == `Prog.eval`, OOM flag at `memoryNeeded - 1`, writes only in
  output + work. Also checked: emitted words == `nanoGenIR p`.
- 2026-11-16: merged origin/main + origin/nano-e2e; renamed to `nanoGenIR`/`nanoCompileIR` (file Nano/GenIR.lean),
  nano-e2e's Nano/Gen.lean and Testing/nano/* untouched. Added Nano/ProofSrc.lean: from source TEXT,
  `nanoCompileSrcIR src = nanoElab src >>= nanoCompileIR`, `Program Src` = `nanoElab` then `nanoRun`;
  **`nano_src_correct : CompileCorrect riscv nanoCompileSrcIR`**, **`nano_src_runs : CompileRuns riscv nanoCompileSrcIR`**.
  check.sh: ALL CHECKS PASSED (statement-fingerprint WARNING only, from main's changes; not re-frozen).

## Route (a) for the raw path (`asm (genR p)`): findings
The raw generator as of nano-e2e 7c57cbd cannot satisfy `CompileCorrect` whatever the proof effort:
1. the result is stored at a1 (= input LENGTH under `StartCorrect`; the output address is a3/x13);
2. inputs read with `ld 8i(a0)`, result written with one `sd`: `StartCorrect` aligns only the work block, and
   `G.step_ld`/`G.step_sd` need 8-alignment (a misaligned Sail access traps);
3. no stack bound check, so `CompileRuns` (a0 = oomFlag exactly when the work block is too small) is false.
The main session asked nano-e2e to move genR/asm to the spec convention (bytewise I/O via lbu/slli/or and
srli/sb at a3, value stack in the work block with a bound check). Proof plan once that lands: record → word lemmas
by `decide +kernel` per (op, registers) family (checked: `asm [0,5,2,c] = wordBytes [encL 3 (8c) 5 2]` for all c
< 256 in ~1 s); per-`Ex` stack invariant on Sail states against the work block (`G.step_*` + `Next`); glue to
`StartCorrect`/`CompileCorrect` as in `Riscv/Back/IrTop.lean` `machine_run`.
- 2026-11-16: merged origin/main + origin/nano-e2e (c06682c). Fixed a build break in nano-mvp's Nano/Chain.lean
  (old IR names → `nanoCompileIR`/`nanoGenIR`/`nanoGenIR_code`; nothing else changed there).
- Route (a) for nano-e2e's raw generator, in progress: **Nano/StackRec.lean**. A record machine (`Nano.R.exec`, the
  semantics of `Nano/Asm.lean`'s table) and, proved on it, `genE_ok`/`genA_ok` (the records of a scoped expression
  push `den e env` on the work-block value stack, bound check passing when `W + 8·depE ≤ T`), `pro_ok` (argument
  words read bytewise and pushed), `wr_loop` (result written bytewise at a3), all block lemmas. The proofs survived
  nano-e2e's opcode renumbering by editing only the `exec` table and record literals.
  Remaining: (1) `genR` end to end on the record machine (prologue `mv t6, sp; mv t3, a0`, `pro`, `genE`, `ld`, `wr8`,
  `ret`); a compile-time check `ScE p.2 p.1 ∧ depth p ≤ 256` is needed (genE loads slot 0 for an out-of-scope variable,
  where `den` gives 0, and offsets are 8-bit); (2) refinement: each record's `asm` word executes on Sail as `exec`
  says (record → `encL/encS/encI/encR/jalr/bgeu` word lemmas by `decide +kernel` per register family, checked
  feasible: ~1 s each; then `G.step_*` with `Next`), memory model `Nat → UInt8` vs Sail's map on the RAM blocks;
  (3) glue `StartCorrect` → `CompileCorrect riscv` as in `Riscv/Back/IrTop.lean` `machine_run` (CompileRuns also
  needs the overflow path: a0 := -1; ret).

## L2 PROVED (2026-11-17): the stack path `asm ∘ genR` on Sail
**`Nano.nano_stack_correct : CompileCorrect riscv nanoCompileA`**, **`Nano.nano_stack_runs : CompileRuns riscv nanoCompileA`**
(`Nano/StackTop.lean`), for the `Program Prog` instance of `Nano/Proof.lean` (`nanoRun`: `arity` 8-byte LE words,
`Prog.eval`, result as 8 LE bytes). Axioms: exactly the Sail set. Int64: `Nano.nano_stack_chain_int` (= `chain_int_of
nano_stack_correct`, via `computes_int`/`nanoRun_int`).
* `nanoCompileA p = if stackOk p then some ⟨nanoGen p, 8, fun _ => [.alloc (depth p)]⟩ else none`,
  `stackOk p = ScE p.2 p.1 && depth p ≤ 256` (variables in scope: `genE` loads slot 0 for an out-of-scope variable
  where `den` gives 0; 8-bit slot offsets). `memoryNeeded = 8 · depth p` (`memoryNeeded_eq`); `nanoCompileA_code`.
* Plugged in: `Nano.nano_stack_chain`/`nano_stack_chain_int` (Nano/Chain.lean, `chain_of`/`chain_int_of nano_stack_correct`),
  **`Nano.SelfHost.selfHosted_stack`** (L1 only → `SelfHosted B space D nanoCompileA`) and
  **`selfHosted_stack_stages`** (three compiled stages, L2 discharged) in Nano/SelfHost.lean.
* Structure: `Nano/StackRec.lean` (record machine, now with CHECKED memory accesses: `ld`/`sd` only 8-aligned inside
  `[a2, sp)`, `lbu` only in the input block, `sb` only in the 8 output bytes; else stuck) → `Nano/StackRun.lean`
  (`push_fail`, `genE_fail`/`genA_fail`, `pro_fail`, `prologue`, **`genR_ok`** / **`genR_oom`**: whole program, both
  outcomes) → `Nano/StackFam.lean` (record families `Fam`, `af_genR`: every record of `genR p` is in one; per family
  `asm [op,a,b,c] = wb (encoder word)` by `decide +kernel` over the 8-bit field) → `Nano/StackSail.lean` (`Ctx`, `Rel`:
  registers equal, pc = pc0 + 4·index, a2/sp/ra fixed, bytes equal on input/work/output, Sail memory outside work and
  the 8 output bytes = start state; bridges `rel_reg`/`rel_sd`/`rel_sb`/`rel_pc`, `instr_of`) → `Nano/StackSim.lean`
  (`case_*` per family from `G.step_*`, **`sim`**: a record step is one retired instruction, `sim_halt` (`ret`),
  `sim_star`) → `Nano/StackTop.lean` (`stack_run`: StartCorrect → record start state → both outcomes).

### Generator change (integrator: please re-merge; affects the compiled `mexp` stage)
* `genR`'s prologue `r 0 31 2 0` (t6 := sp) is now `r 5 31 2 3 ++ r 1 31 31 3` (t6 := (sp >> 3) << 3).
  Why: Sail `ld`/`sd` are proved only for 8-aligned addresses (`G.step_ld`/`step_sd`), and `StartCorrect` aligns only
  the work START (`workLength` arbitrary), so with t6 := sp every slot is misaligned when `workLength % 8 ≠ 0`.
  Changed in Nano/Gen.lean (`genR`), Nano/Expand.lean (`mexp` micro-op 0 = HDR now expands to 3 records), Nano/Ser.lean
  (`mexp_ser`'s HDR lemma). Nothing else changed in the generator. Overflow is still exact: pushes fail iff
  `workLength < 8 · depth p` (`W` aligned, so the aligned top leaves `⌊workLength/8⌋` slots).
* Found (not changed): `asm`'s `sb` encoding (op 16) puts only `a >>> 4` in byte 3, dropping imm[11:5]; correct only
  for offsets < 32. `genR` uses offsets 0–7, so the `Fam` for op 16 requires `c < 32`. Fix in `asm` if `sb` is ever
  used with larger offsets.
* `Testing/scripts/check.sh` on nano-proof had committed conflict markers from an earlier merge; replaced by nano-int's.

### What remains for the target
* Only (L1): a binary `B` computing `nanoGen` from source (`selfHosted_stack` / `selfHosted_stack_stages`).
* `nanoCompileA` is partial (`stackOk`); `SelfHosted.correct` is vacuous for programs it rejects. A lemma
  `nanoElab src = some p → ScE p.2 p.1` (the elaborator resolves names) would make it total up to `depth p ≤ 256`;
  that bound could go into `D`.
