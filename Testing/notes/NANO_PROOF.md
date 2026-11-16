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
