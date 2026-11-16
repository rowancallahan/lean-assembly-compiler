# nano code generator and its proof (branch nano-proof)

Owner of `nanoGen : Prog → List UInt8` (Nano/Gen.lean) and its proof (Nano/Proof*.lean).
nano-e2e had no `nanoGen` when this branch started; this one is new (same name/signature as the ROADMAP).

## Route: (b) lower to the IR, reuse `ir_compile_correct`'s machine theorem
- Why: `Riscv/Frontx/IndIr.lean` already instantiates `CompileCorrect`/`CompileRuns` through `Ir.compile` +
  `Ir.machine_run`; the structured-code layer (`SC`/`TC`, `flatT_ok`) and the inductive path's helpers (`rd8_ok`:
  8 LE input bytes → word, `wout_loop`: word → 8 LE output bytes) are reusable as is. Only nano → IR needs proving
  (straight-line code, no loops), versus re-proving register allocation/branches against Sail in route (a).
- Lowering (`Nano.lower`): one function `main`, one region; parameters read with `rd8`, expression to fresh virtual
  registers (`cE`/`cA`, mutual like `den`/`denA`), calls INLINED (the AST already carries the callee body), result
  written with `wStep`. All vregs live in frame slots (trivial allocation), so code size and frame grow with the
  inlined tree (exponential in call-nesting for DAG-shaped call graphs). Acceptable for v1.
- Self-hosting gap: `nanoGen` calls `Ir.compileW` (allocation, layout, emission of the big compiler). It is plain
  Lean but not yet compiled by our front end; the v2 fixed point needs either that or a raw emitter (route (a)) for
  the straight-line subset proved against the same `lower` meaning.

## Spec instantiation
`Program Nano.Prog`: `nanoRun p input` = words of the input (8-byte LE, exactly `arity` of them, `wordsOf`), then
`Prog.eval`, output `leN 8 v.toNat`.

## Log
- 2026-11-16: `Nano/Gen.lean` (`cE`/`cA`, `ldArgs`, `mainTC`, `lower`, `nanoGen`), `Nano/Proof.lean` (`nanoRun`,
  `Program Prog` instance, `cE_ok`/`cA_ok`, `ldArgs_ok`, `lower_ok`), `Nano/ProofTop.lean` (`nanoCompile`,
  `nanoGen_code`, **`nano_compile_correct : CompileCorrect riscv nanoCompile`**, **`nano_compile_runs : CompileRuns
  riscv nanoCompile`**). Axioms: machine theorems = the Sail set (same as `ir_compile_correct`), `lower_ok` ⊆
  {propext, Classical.choice, Quot.sound}. `Testing/scripts/axioms_nano-proof.lean` added to check.sh's loop;
  check.sh also builds `Nano` and greps `Nano/*.lean` for forbidden words (decided: the nano files are proof sources).
- 2026-11-16: register reuse. The IR back end allows at most 254 frame slots (`maxSlots`, one per vreg), so the
  first lowering (a fresh register per node) failed to compile programs with > ~240 nodes (`nanoGen` = []). Now a
  compound expression leaves its value in its first fresh register (`.let_ nx ...`); registers grow with the nesting
  depth only. Limit that remains: nesting depth + arity + 10 ≤ 254 (else `nanoCompile p = none`, `nanoGen p = []`).
- Tests: `Testing/asm/nano_test.sh` (emit with `Testing/asm/emit_nano.lean` → `ir-words/nano_*`, gitignored;
  `ir_test.py` on QEMU + Sail at `memoryNeeded` and `memoryNeeded - 1`). 39 programs (6 full trees of depth 5–10,
  up to 4146 words; 30 random with lets, calls, out-of-range variables; 3 sources through `nanoElab`) × 8 inputs
  = **312 program×input pairs**: QEMU == Sail == `Prog.eval`, OOM flag at `memoryNeeded - 1`, writes only in
  output + work. Also checked: emitted words == `nanoGen p`.
