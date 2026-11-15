# Agent overview

Read this first. The top-level `README.md` is for people; this file is for agents working in the repo.

## Current state (2026-11-15)

- Build: the generated per-register step files (`Words`, `BranchWords`, `MemWords`, `ArrWords`, `Arr2Words`, ≈ 52 min CPU)
  are out of the build (`Riscv/Legacy/Steps/`); `Riscv/Steps/Compat.lean`/`CompatArr2.lean` give the same names from the
  generic `Gen*` lemmas. Clean `lake build Riscv` 2438 s → 456 s; `check.sh` after a change to `Riscv/Steps` ≈ 5 min.

- RISC-V (Lean 4.29.0, Sail model `opencompl/sail-riscv-lean` at `../deps/sail-riscv-lean`, unmodified): kernel-checked
  expressions (`compile_ok`), loops (`compileS_ok`, `gcd_ok`), store/byte arrays (`compileStore_ok`, `compileAF_ok`),
  sorts equal to `List.mergeSort` (`sortCode_implements`, `msortCode_implements`), the list front end
  (`compileP_ok`, `compile%`), and the machine-independent middle layer (`Proven.Mach.Machine.compAF_ok`, only
  `propext`/`Classical.choice`/`Quot.sound`) re-deriving the RISC-V theorems through an interface (`Riscv/Back/`).
  Full list with statements: `DETAILS.md`; middle layer: `MACH.md`; arrays: `ARRAYS.md`; loops: `LOOPS.md`;
  front end: `PIPE.md`; fuzzing: `FUZZ.md`; targets and plans: `ROADMAP.md`.
- Optimising back end (`OPT.md`): the front end (`compileP`, `compileXA`, `compileXB`) emits the optimised words;
  the `Implements1` examples have optimised versions (`Riscv/Examples/Implements1Opt.lean`, `…_implements1O`);
  every `compile%` pipe also has an `Implements1` theorem (`compileX1_ok`, `Compiled.implements1`, `PIPE.md`).
- Automatic front end (`Riscv/Frontx/`, lib `Frontx`, a default target; notes `Testing/notes/frontx/`): Lean
  definitions → `BStmt` programs with automatic equation proofs; `frontx_implements g` emits optimised code
  (`compBFO`) and `g.implements1 : Implements1With …` (8 examples in `Riscv/Frontx/Machine.lean`; axiom file
  `axioms_m.lean`; QEMU/Sail test `python3 Testing/asm/frontx_test.py check 40 crcraw`).
- Branchy merge sort (`OPT.md`, last section): `msortProgB_mergeSort`, `msortCodeO2_implements1`
  (`Riscv/Examples/MsortB.lean`, `MsortBOpt.lean`), 1.06–1.17× gcc -O2 instructions.
- Calls (`CALLS.md`): `Spec/Tree.lean`, `treeEval_implements` (`Riscv/Examples/TreeEval.lean`), `calls_test.py`.
- ARM on DeepMind's AArch64 semantics (`Arm/apc/README.md`, `Arm/apc/check.sh`): `apc : Machine` (9 laws), `compile_apc`/`gcd_apc`/`sort_apc`, bridge `apc_eq_sail` to Sail for the 216 expression words.
- ARM (Lean 4.34.1, generated model `Arm/model/`, built copy `/home/user/armv9-lean`): AArch64 backend for `Exp`
  proved at the decode+execute layer (`Arm/proofs/README.md`); fetch / full step / `ret` chaining in progress.
- Not proved: `Riscv/Legacy/Sort.lean` (`sorry`, hand-written merge sort), `Riscv/Legacy/SortSteps.lean` (kernel
  deep recursion); both superseded and excluded from the build (`RiscvLegacy` lib, not a default target).

## Rules

- No `sorry`, no `axiom`, no `extern`, no `native_decide`, no `bv_decide`. `Testing/scripts/check.sh` enforces this
  and compares `#print axioms` of the main theorems with `Testing/scripts/expected-axioms.txt`.
- `Spec/` is frozen-ish and owner-reviewed: do not change definitions there without the owner. New statement
  definitions go to `Spec/` only when needed to state a theorem.
- Work in the repo `/home/user/lean-assembly-compiler` directly (no working copy + rsync). Commit often, small
  logical commits; `git pull --rebase` before `git -c push.negotiate=true push origin main`.
- One Lean process per agent (other agents share the box); long builds as tracked background tasks; `swapon /swapfile`
  if swap is missing. Lake resumes an interrupted build.
- Never rebuild the ARM model (`Arm/model/`, `/home/user/armv9-lean`); ARM proofs build with `Arm/proofs/check.sh`
  (`lean -o` against the built model).

## Where things live

| Path | What |
|---|---|
| `Spec/Encode.lean` | `Bytes` class: byte encodings and the decode/encode round trip |
| `Spec/Code.lean`, `Spec/ArrCode.lean` | source languages `Exp`, `AExp`/`AStmt` (+ big-step `AExec`) and their meaning |
| `Spec/Riscv.lean` | machine-level statement on the Sail RISC-V state: `Cfg`, `Retires`, `runsTo`, `Region`, `disjoint`, `bytesAt`, `Implements` |
| `Compiler/{Iface,Logic,Exp,Stmt,Mem,Arr}.lean` | middle layer: machine interface, Hoare logic, generic compilers and proofs (namespace `Proven.Mach`) |
| `Compiler/Front/` | `Pipe` combinator language, `compileP`, `compile%` (`PipeFront`), `reify%` (`Reify`) |
| `Riscv/Steps/` | `sail_eval` tactic, register facts, register-generic step lemmas `Gen*.lean` (`STEPS.md`), `Compat*.lean` (the old generated names, proved from `Gen*`) |
| `Riscv/Legacy/Steps/` | the old generated `*Words.lean` + `gen_*.py` (not built; `Compat.lean` replaces them) |
| `Riscv/Direct/` | direct RISC-V compiler proofs (`Compiler`, `Loop*`, `Mem*`, `Arr*`, `Arr2*`, `Sort*`); still the base of the instance |
| `Riscv/Back/` | the RISC-V instance of the middle-layer interface and the re-derived theorems (`compile_ok'`, ...) |
| `Riscv/Examples/` | `LoopExamples` (sum, gcd), `ArrExamples` (sum/take/inc), `PipeExamples` (`compile%`) |
| `Arm/CompilerArm.lean` | AArch64 code generator (4.29 lib; staged by `Arm/proofs/check.sh` as `Proven.CompilerArm`) |
| `Arm/model/`, `Arm/gen/`, `Arm/proofs/`, `Arm/shrink/` | generated model, regen script + patch + `DIFFS.md`, proofs, model-shrinking experiments |
| `Testing/asm/` | QEMU vs Sail C emulator harnesses (`triple.py`, `loop_test.py`, `arr_test.py`, `msort_test.py`, `pipe_test.py`, `memtest.py`, fuzzers) and `emit_*.lean` word emitters |
| `Testing/asm-arm/`, `Testing/setup/box.sh` | AArch64 merge-sort harness; reproducible box setup |
| `Testing/scripts/check.sh` | build + axioms + forbidden-word check |

Module names follow folders (`Spec.Code`, `Compiler.Front.Pipe`, `Riscv.Steps.Compat`, ...); namespaces inside the
files were NOT changed (`Proven`, `Proven.Mach`, `Proven.Mach.Riscv`, ...). There are no lib root files: the
lakefile uses `globs`. Two pairs of modules cannot be imported together (duplicate declarations):
`Riscv.Examples.LoopExamples` / `Riscv.Examples.ArrExamples` (`sumProg_wf`) and `Compiler.Front.Pipe` /
`Riscv.Direct.Arr2Code` (`BExp`); hence three axiom files in `Testing/scripts/`.

Commands (repo root): `lake build` (clean `lake build Riscv` ≈ 8 min on 4 cores, was ≈ 41 min with the generated step files), `lake build Riscv.Direct.Loop` (one module + deps),
`lake env lean Testing/asm/emit_pipe.lean` (re-emit words), `python3 Testing/asm/pipe_test.py sort 20`.

## New step lemmas

Do not generate per-register files any more: state the instruction form once with register/immediate
variables in `Riscv/Steps/Gen*.lean` (`by genc; gstep` or `genm; gmem`, see `STEPS.md`) and instantiate it.
The old generators (`Riscv/Legacy/Steps/gen_*.py`) still print the archived files, which are not built and
clash with `Riscv/Steps/Compat.lean` (same names).

## Definitions that should later migrate to `Spec/` (not moved in the reorganisation; files were not split)

- `Riscv/Direct/Loop.lean`: `Env`, `Env.set`, `Stmt`, `Exec` (the `Stmt` source language; `Compiler/Stmt.lean` has a copy in `Proven.Mach`).
- `Riscv/Direct/Arr2Code.lean`: `BExp`, `BEnv`, `BState`, `BStmt`, `BExec`, `AExp.toB`/`AStmt.toB`/`AState.toB` (+ `AExec.toB` proof).
- `Compiler/Front/Pipe.lean`: `BOp`, `BCmp`, `BExp`, `WExp`, `Stage`, `Pipe` and their `denote`, `leBytes`, `Pipe.space`.
- `Riscv/Direct/SortMachine.lean`: `ImplementsMapped`, `leU`; `Riscv/Direct/SortMergeMachine.lean`: `ImplementsMapped2`;
  `Compiler/Front/PipeMachine.lean`: `ImplementsPipe` (all into `Spec/Riscv.lean`).
- `Riscv/Direct/MemModel.lean`: model-free `Block`, `Layout`, `Layout.ok`, `readCells`, `writeCells`, `le8`.
- The reverse direction: `Spec/Code.lean` and `Spec/ArrCode.lean` also hold the RISC-V encoders and code generators
  (`encR`, `encI`, `T`, `A`, `i*` words, `gen`, `compile`, `A8`, `gen8`, ...) which belong in `Riscv/`.
- `Compiler/Front/` currently imports `Riscv/Direct` (`compileP` = RISC-V `compileAF`, `reify%` uses `compile_ok`);
  it should be re-based on the middle layer so the front end is machine-independent.

## Standing decisions (from the owner; copied from `ROADMAP.md`)

- Scope: a SUB-compiler for pure functions, bytes in → bytes out (`Spec/Encode.lean`). No IO, no OS interaction.
  The OS (or a boot stub) only loads blocks and reads the result; "a correctly functioning OS hosts the process" is a stated assumption.
- The compiler is one pure Lean function. Any number of internal passes/optimisations is fine if proved:
  no `sorry`, no `axiom`, no `extern`, no `native_decide`/`bv_decide`.
- Front end: translate Lean definitions ourselves with a kernel-checked equation per function; do not use Lean's compiler IR.
- Structure: front (Lean → program) / middle (program → abstract ops + all Hoare logic, machine-independent) / back (per target, thin).
  Design on RISC-V; ARM follows in the background.
- Two backends with separate proofs, each equal to the Lean function; no combined ARM = RISC-V theorem needed.
- Arithmetic: integers and modular arithmetic only. NO floats, nothing over the rationals/reals.
- Speed matters: generated code should aim to match or beat Lean's native compiler.
- Tier 1 = the explicit compiler (proved passes, invisible in the spec); tier 2 = hand/agent-optimised code for one
  function, proved against the same spec.
- Resources in the spec: ONE bound, `space n` = extra bytes of memory the code may use for an input of n bytes.
  Registers: a fixed convention, not a counted resource.
- Memory: blocks are lists of cells; layouts of pairwise-disjoint blocks; owner reviews byte layouts in `Spec/Encode.lean`.
