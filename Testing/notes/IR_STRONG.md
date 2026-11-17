# IR_STRONG: strengthened statements (`CompileCorrectL` / `CompileRunsL`) and the chaining adapter

Branch `ir-strong` (from main + s3-rec). Owner goals: ROADMAP "Spec strengthening" item 1 and NANO_PARSE_S3.md
"Findings" (1)-(4).

## Statements (Compiler/AllocSpec.lean, added only)
- `KeptRegisters machine s s'`: every register of `machine.mapping.kept` (RISC-V: `sp gp tp s0..s11`, the list of
  `abiSavedKept`) reads the same in the observations.
- `CompileRunsL` = `CompileRuns` with the frame narrowed to the result prefix `[outputAddress, +|y|)` and the work
  block, plus `KeptRegisters` and `machine.configured finishState`.
- `CompileCorrectL` = `CompileCorrect` plus `register mapping.outputLength = |y|` (a1), the same narrowed frame,
  `KeptRegisters`, `configured`.
- `CompileRunsL.runs : CompileRunsL m c → CompileRuns m c`, `CompileCorrectL.correct : ... → CompileCorrect m c`.

## Decisions
- DECISION: the IR has no output write pointer (the output is a growing list written at arbitrary indices, Sem.lean
  `setOut`), so the exit stub cannot compute `end − start`. Instead `main` RETURNS the output length (its one
  return value, in `r0` after `ret`), and the stub moves it to a1 (`RLen`). The IR-level statements are for
  `Ir.ProgL` (an IR program whose run counts only when `main` returns `[w n]` with `n = |output|`); S3's lowering
  makes `main` return its output counter.
- DECISION: (4) needs no new invariant: the IR context's `outL` is only an upper bound for writes, so the machine run
  is instantiated with `outL := |final output|`; its `Unch` is then exactly (4).
- DECISION: (2) is carried as `T.keepC C.s0 s` in the IR invariant (every target op already yields `keep`/`keepF`/
  `keepC`); the frame register (`gp`, x3) is restored by the stub's `leave`.

## Log
- step 1: AllocSpec additions + the two implications (checked with `lake env lean Compiler/AllocSpec.lean`).
- step 2a: IR stub `stub3 = [mov a1 r0; leaveC 0; leave; ret]` (a1 := main's first result). `Ctx.Fin`'s normal-return
  case now also states `keepC C.s0 s'`, `fr s' = fr C.s0`, `r.vs = [w n] → a1 = n` (EmitStep/EmitStepOk `done_ok`).
  `Ir.machine_runL` (Riscv/Back/IrTop.lean): exact frame (result prefix + work), `Cfg`, and on normal return
  `KeptRegisters` + a1; `machine_run` (old statement) now derived from it. `Ir.ProgL`, `Ir.compileL`,
  `Ir.ir_compile_correctL : CompileCorrectL riscv compileL` PROVED.
- GAP (OOM path): the out-of-memory exit (`encK .exit`: `ld ra,-16(top); li a0,-1; ret`) does not restore the frame
  register gp (x3), so `KeptRegisters` fails on that path; `CompileRunsL` needs an IR-specific exit that also
  reloads gp from the stub's cell `top - 8`.
- step 2b: OOM path closed. `rvT.encX := encXG` = `srli/slli t0 (top); ld ra,-16(t0); ld gp,-8(t0); li a0,-1; ret`
  (`law_exitG`, Riscv/Back/IrTarget.lean; the shared `encK .exit` of the other back ends is unchanged). `Target.c_exit`
  takes the cell `top - 8` and yields `keepC s s' ∧ fr s' = v`; `MR`/`Pre` carry the stub's gp cell (`gpc`, mirrors
  `stub`); `Exited` and `Fin`'s OOM case state `keepC C.s0 s' ∧ fr s' = fr C.s0`. `Ir.ir_compile_runsL :
  CompileRunsL riscv compileL` PROVED; `machine_runL` states `KeptRegisters` unconditionally.
- step 3: S3. `mainTC` ends with `ret [r8]` (r8 = `outLoop`'s index = output length); `out_loop` states the final
  index; `lower_result` (Compiler/S3/LowerMain.lean): the RTL run's output is `out` and `vs = [w |out|]`
  (`lower_meaning` derived from it). `S3.compile_runsL : CompileRunsL riscv S3.compile`,
  `S3.compile_correctL : CompileCorrectL riscv S3.compile` PROVED (Riscv/Back/S3Top.lean).
- step 4: the ADAPTER (Riscv/Back/LinkL.lean). FINDING: `CompileCorrectL` (Spec/Top machine) observes memory only at
  `UInt64` addresses, while `Implements1With.unchangedOutside` frames every `Nat` key of the Sail memory map; addresses
  `≥ 2^64` are not reachable from the abstract statement. So the adapter's hypothesis is
  `Proven.Top.CompileCorrectRV compile` = `CompileCorrectL riscv compile`'s conclusion with the frame on every `Nat`
  address (`CompileCorrectRV.correctL : CompileCorrectRV c → CompileCorrectL riscv c`). The IR proof already has it
  (`Ctx.Unch`), so `machine_runL` states it; `Ir.ir_compile_correctRV`, `S3.compile_correctRV` PROVED.
  `Proven.Top.implements_of_compileL : CompileCorrectRV compile → compile program = some compiled →
  compiled.code = wordBytes code → Computes program f encA encB →
  (∀ a, |encA a| ≤ maxLen → memoryNeeded compiled (encA a) ≤ space |encA a|) → maxLen ≤ 2^20 →
  Implements1With encA encB code f space maxLen retLen` (any `retLen`, in particular `true` as `link_stage` needs).
  `S3.implements` = the adapter on `S3.compile_correctRV`. `CompileRunsL` is not needed by the adapter.
- tests: `Testing/asm/ir_test.py` now asserts a1 = output length for every `s3*` program and gp = caller's gp after the
  out-of-memory exit (all IR programs). S3 words regenerated (`emit_s3.lean`); QEMU + Sail, 10 cases x 2 each:
  s3_small, s3_find, s3_append, s3_filter, s3_mirror, s3_eqtree ok. Negative control: the pre-change s3_find words
  fail the a1 check (a1 = 0, expected 1).

## Other back ends (not done here; what each needs)
- Inductive path (`Compiler/Ir/IndLow*`, through the IR): its `main` must return the output length (as S3's
  `mainTC`: `ret [index]`), then `Ir.machine_runL` gives `CompileCorrectL`/`CompileCorrectRV` as for S3.
- Hand-written IR programs (`Compiler/Ir/Examples.lean`): `Ir.ProgL` requires `main` to return `[w |output|]`.
- Paged back end, nano stack, frontx (`Implements1`-based): `implements1_top` already yields every clause of
  `CompileCorrectL`/`CompileCorrectRV` when the code is proved with `retLen = true`; with `retLen = false` only a1 is
  missing: their exit code must set a1 (nano: `li a1, 8`).
- FINISH: merged origin/main (already up to date at 441ede4); `bash Testing/scripts/check.sh`: ALL CHECKS PASSED (16 min).
  The statement-fingerprint WARNING is pre-existing drift: `expected-statements.txt` was frozen at 793ac7c, 303
  commits before main; only closure hashes differ (all statement hashes equal), including theorems whose files this
  branch does not touch (e.g. `Ind.ind_ok`, `compileP_ok`). Not re-frozen (rule).
