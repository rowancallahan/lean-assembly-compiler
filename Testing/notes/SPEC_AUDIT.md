# Spec audit (vacuity, weakness, held-out checks)

Practices from the AlphaProof-Code paper applied to the RISC-V side: non-vacuity witnesses, mutation tests,
a frozen ("held-out") spec, `comparator`, statement fingerprints. Everything listed here is kernel-checked: no `sorry`,
`axiom`, `native_decide` or `bv_decide`. `decide +kernel` is used to evaluate concrete lists and words.

Files: `Riscv/Examples/VacuityBase.lean`, `VacuityExp.lean`, `VacuitySort.lean`, `MutationBase.lean`,
`MutationExp.lean`, `MutationSort.lean` (namespace `Proven.Vacuity`); `Spec/FROZEN.sha256`,
`Testing/scripts/{spec_check.sh, statement_check.sh, stmt_hash.lean, expected-statements.txt, axioms_d.lean,
axioms_e.lean}`, `Testing/scripts/comparator/`.

## 1. Non-vacuity (V1)

**`Cfg` is satisfiable.** `witness_cfg pc ra sp a0 a1 a2 a3 mem : Cfg (witness ...)` holds for *every* choice of
register values and memory, and `cfg_nonvacuous : ∃ s, Cfg s`. The witness register map is 50 explicit
`ExtDHashMap.insert`s: the Sail reset values for the control registers, one PMA region `{default with rwx}`,
`x1 = ra`, `x2 = sp`, `x10..x13 = a0..a3`, every other `x` register `0`. Lookups are proved by
`simp [get?_insert, contains_insert]` (Register has derived `DecidableEq`, so `simp` decides key equality). It
never evaluates a hash map with `decide`.
Memory is a fold of inserts, `loadBytes m a bs`. The generic lemma `loadBytes_get` (`(loadBytes m a bs)[k]? = if a ≤ k <
a+|bs| then bs[k-a]? else m[k]?`, proved by induction) gives every `bytesAt` / `codeAt` / `instrAt` fact without any
concrete map computation. Whole files take about 1–5 s each to check.

**The headline hypotheses are jointly satisfiable**, and on the witness each theorem gives the expected concrete fact:

| theorem | witness | concluded fact |
|---|---|---|
| `compile_ok` | `sC (compile (1+1)) 0 0`: code at `0x80000000`, `ra = 0x80001000` | `compile_ok_concrete`: runs to `ra` with `a0 = 2` |
| `gcd_ok` | `sC (compileF gcdProg) 12 18` | `gcd_ok_concrete`: runs to `ra` with `a0 = 6` |
| `sortCode_implements` | `sS sortCode`: input `[3,1,2]` at `0x80002000`, scratch `0x80003000`, output `0x80004000` (3 bytes), stack `[0x80005000, +0x100)` | `sortCode_concrete`: output bytes `[1,2,3]` |
| `msortCode_implements` | `sS msortCode` (same layout; frame 71 ≤ 256) | `msortCode_concrete`: output bytes `[1,2,3]` |

`IM_apply` / `IM2_apply` take any code of at most 1000 words and any `f` with `|f [3,1,2]| = 3`. They discharge all
22 (resp. 23) hypotheses of `ImplementsMapped` / `ImplementsMapped2` at the witness. `compile_ok_hyps` and
`gcd_ok_hyps` state the conjunction of all hypotheses explicitly.

## 2. Execution witness (V2)

`exec_e11 : ∃ s', Steps 9 (sC (compile (1+1)) 0 0) s' ∧ PC s' = ra0 ∧ getX s' 10 = 2 ∧ s'.mem = ...` is proved
WITHOUT `compile_ok` / `gen_ok`. It chains the nine per-word Sail step lemmas (`step_zero`, `step_shl`, `step_inc`,
`step_zero`, `step_shl`, `step_inc`, `step_op .add`, `step_res`, `step_ret`), each proved by symbolic evaluation
(`sail_eval`) of `run_hart_active`, on the concrete witness. The file checks in about 2 s. A direct `sail_eval` of
`try_step` on the fully concrete state was not attempted: the per-word lemmas already are that evaluation, made
generic in `s`.

## 3. Mutation tests (V3)

Tools (`MutationBase.lean`):
- `retires_det`: `Retires` is deterministic, because it ends with `try_step 0 false s = .ok false s'`, which is a
  function of `s`. `steps_det` and `steps_split` follow.
- `park := jal x0, 0`. In `parked_stays`, once `PC = ra` with `park` at `ra`, every later state has the same memory
  and `x` registers.
- `runsTo_unique`: two `runsTo s P`, `runsTo s Q` whose final states are parked at `ra` agree on memory and `x`
  registers. The spec quantifies over *all* memory at `ra`, so it can be instantiated with a parked `ra`, which makes
  its "returns with output v" claim unique. One concrete input where a mutant's output differs therefore refutes
  the spec for that mutant.
- `AStmt.run` (fuel interpreter) with `run_sound` turns a concrete source run (by `decide +kernel`) into an `AExec`
  derivation.

A mutant is killed through its source image: `compileAF_ok` / `compile_ok` of the mutated source gives the
mutant's real behaviour. Each mutant differs from the original in exactly one word, checked by `decide +kernel`
(`*_diff`).

**Killed (proved `¬ spec`):**

| id | code | change (one word) | input | spec says | mutant gives |
|---|---|---|---|---|---|
| M1 | `sortCode` word 100 | outer `i := i + 1`: `add` → `sub` | `[3,1,2]` | `[1,2,3]` | `[3,1,2]` |
| M2 | `sortCode` word 84 | stored value `a7 ? a6 : a5` → `a7 ? a6 : a6` (register field) | `[3,1,2]` | `[1,2,3]` | `[3,3,3]` |
| M3 | `sortCode` word 33 | copy-loop increment `add` → `sub` | `[3,1,2]` | `[1,2,3]` | `[0,0,3]` |
| M4 | `sortCode` word 75 | shift test `a5 <u a6` → `a5 <u a5` (register field) | `[3,1,2]` | `[1,2,3]` | `[3,1,2]` |
| X1 | `compile (a0+a1)` word 2 | `add` → `sub` | `5, 3` | `8` | `2` |
| X2 | `compile (min_u a0 a1)` word 2 | `sltu` → `slt` | `-1, 1` | `1` | `-1` |
| X3 | `compile (a0+5)` | drop word 6 (`addi t1,t1,1`) | `0` | `5` | `4` |

Theorems: `mut1_killed` … `mut4_killed` (also `sort_mutants_killed`), and `mutX1_killed` … `mutX3_killed`.
`ExpSpec code f` is `compile_ok`'s conclusion for arbitrary code, and `compile_spec` restates `compile_ok` in that
form.

**Not killed / not attempted:**
- E1 `sortCode` word 76: shift test `sltu` → `slt`. This is an **equivalent mutant**: both operands are zero-extended
  bytes `< 2^63`, so signed and unsigned comparison agree on every input. The same holds for `ult` → `slt` on
  `0 <u a4` and `a2 <u a1`, since lengths are `≤ 2^20`. These mutants are correct code, not a spec gap.
- M5 (`a4 - a7` → `a4 + a7`, word 93) and M6 (cE `and` → `or`, word 77): the mutated source has no `AExec`
  derivation on `[3,1,2]` because a load goes out of bounds, so the source route cannot be used. They are very
  likely killed: the machine reads or writes outside the blocks, which breaks `unchangedOutside`, or it misses the
  output. Proving it needs direct model evaluation of about 100 steps.
- Non-source-image mutants (flipping `beqz` ↔ `bnez` in the loop code, deleting a store, changing a branch
  offset): not attempted. They need direct evaluation of the whole sort on the model. The tools above (determinism,
  parking) apply unchanged once such a run is available.

## 4. Held-out spec, comparator, statement fingerprints (V4)

- `Spec/FROZEN.sha256` holds the sha256 of every file under `Spec/`, sorted. `Testing/scripts/spec_check.sh` fails
  on any change, new file or removed file. Re-freeze with `Testing/scripts/spec_check.sh --freeze`. `check.sh` runs
  it as a WARNING while the owner tidies `Spec/`.
- **comparator** (`leanprover/comparator`; deprecated upstream in favour of `lake comparator` in Lean 4.35):
  commit `2a00b30` is the last one on Lean v4.29.0. It builds with its pinned `lean4export` (`048394e`) and
  `Lean4Checker`. `landrun` (Go, `main`) builds too, but this kernel has Landlock ABI v7, so it runs with
  `--best-effort`. The wrapper `Testing/scripts/comparator/bin/landrun` also re-inserts the `--` that new landrun
  versions swallow, which breaks `lean4export <Mod> -- <decls>`. The set-up is `Testing/scripts/comparator/`, a lake
  project that `require`s this repo by path, with the Sail package symlinked so the model is not rebuilt.
  `Challenge.lean` is the held-out statement of `sortCode_implements` with a `sorry` proof, `Solution.lean` proves
  the same statement by `Proven.sortCode_implements`, and `config.json` permits exactly the 77 axioms of
  `expected-axioms.txt`. Run it with `Testing/scripts/comparator/run.sh` (one-time set-up in its header).
  **Result: "Lean default kernel accepts the solution / Your solution is okay!"** in 195 s (about 1.8 GB for
  `lean4export`): the statement matches, only permitted axioms are used, and the kernel replay passes. Limitation:
  the challenge imports `Riscv.Direct.SortMachine`, which holds `ImplementsMapped` and `sortCode`, so the
  "held-out" part is only the theorem statement. A full held-out copy would move the statement definitions
  (`ImplementsMapped`, `leU`, and the compiler that defines `sortCode`) into a trusted challenge module. The
  fingerprints below cover that gap cheaply.
- **Statement fingerprints** (the cheap equivalent, which also covers the definitions): `Testing/scripts/stmt_hash.lean`
  (`lake env lean --run`) imports the modules and computes the dependency closure of each headline *statement*
  (not its proof). The closure includes definitions' bodies, theorems' types only, inductives with constructors,
  and opaque/axiom types. It hashes the pretty-printed statement and `(name, levels, Expr.hash type[, body])` over
  the sorted closure. `Testing/scripts/statement_check.sh` compares the result with `expected-statements.txt`.
  A weakening of any definition a theorem depends on (e.g. `Cfg`, `unchangedOutside`, `calleeSavedKept`,
  `ImplementsMapped`, `bytesAt`, the compiler itself) changes `closure=` even when the theorem's text is unchanged.
  Re-freeze with `--freeze`; `--list` prints each statement and the project-local definitions it depends on.
  The current values are 8 statements, each with about 6900–7100 closure constants (most of them the Sail
  model) and 80–226 project-local definitions; the check takes about 15 s and the hashes are stable across runs.
  `check.sh` runs it as a WARNING, because the closure includes the compilers (`compile`, `compileAF`, ...), which
  other agents are still editing.

## 5. The headline theorems, hypothesis by hypothesis (V5)

Legend: **[L]** discharged by the loader/OS/caller (calling convention, placement), **[R]** a real restriction,
**[C]** the fixed machine configuration.

### `compile_ok (e) (he : e.depth < 11) (h : Cfg s) (hpc) (hc : codeAt s pc (compile e)) (hok : codeOK pc _) (hra)`
- `e.depth < 11` **[R]**: expressions need at most 11 temporaries (`t0..t6, a4..a7`). There is no spilling.
- `Cfg s` **[C]**: M-mode; hart active; `misa` fixed (RV64 IMAFDCBSU…); `mstatus = 0xA00000000`, so MIE = 0 (no
  interrupts) and **FS = VS = 0, so floating-point and vector instructions trap**; no PMP (`pmpcfg = 0`); no HTIF;
  `elp = 0`; `mseccfg = 0`; one PMA region = RAM `[2^31, 2^32)`, rwx; the listed registers are present.
- `PC = pc`, code bytes at `pc` (`codeAt`), `pc` 4-aligned and code inside RAM (`codeOK`) **[L]**.
- `ra` even **[L]**. Only bit 0 is required: C is enabled, so 2-aligned returns are legal.
- Conclusion: some finite trap-free run (`Steps`: every instruction `Retire_Success`) reaches `PC = ra` with
  `a0 = e.denote(a0..a3)`, `Cfg` restored, **memory exactly unchanged** (`s'.mem = s.mem`, which also means no new
  map keys), and `calleeSavedKept`.

### `gcd_ok`
Same as `compile_ok` for the fixed program `compileF gcdProg`, with no depth hypothesis; the result is `a0 = gcdSub a0 a1`.

### `sortCode_implements : ImplementsMapped sortCode (·.mergeSort leU)` (and `msortCode_implements`, `ImplementsMapped2`, `stackLen := 71`)
Hypotheses, for input bytes `x`:
1. `|x| ≤ maxLen = 2^20` **[R]** (1 MiB).
2. `Cfg s` **[C]**; `PC = entry`, `entry % 4 = 0`, code bytes at `entry` **[L]**.
3. `a0 = input.base`, `a1 = |x|`, `a2 = scratch.base`, `a3 = output.base`, `sp = stack.base + stack.len`, `ra = x1`
   **[L]** (calling convention).
4. `ra % 4 = 0` and the 4 bytes at `ra` disjoint from the code **[L]**. This is stronger than the hardware needs
   (2-alignment) and harmless.
5. input bytes = `x`, `input.len = |x|`, `|x| ≤ scratch.len`, `|f x| ≤ output.len`, `stackLen ≤ stack.len` **[L]/[R]**:
   the caller provides the space. Insertion sort uses no scratch or stack. The merge sort uses a 64-byte frame
   below `sp` plus up to 7 bytes of alignment, so 71. `sp` need not be aligned.
6. all five regions in RAM and pairwise disjoint **[L]**.
7. `ImplementsMapped` only: the output bytes are present in the memory map. `ImplementsMapped2` also requires the
   scratch bytes **[L]** (OS hosting assumption). These hypotheses are not in `Spec/Riscv.lean`'s `Implements`;
   see weakness W1.

Conclusion: a trap-free run to `PC = ra`; the first `|f x|` output bytes are `f x`; memory outside
input ∪ scratch ∪ output ∪ stack is unchanged (for every address, including absent keys); `calleeSavedKept`;
`Cfg s'`.

### Weaknesses and surprises found
- **W1 `Implements` (the definition in `Spec/Riscv.lean`) is proved for no code.** The sort theorems use
  `ImplementsMapped` / `ImplementsMapped2` (defined in `Riscv/Direct/`, outside `Spec/`), which add the "output
  (and scratch) bytes are mapped" hypotheses. The front end uses `ImplementsPipe` (`Compiler/Front/`).
  `Spec/Implements1.lean` (new, WIP) includes the hosting hypotheses and should become the single notion. Until
  then, the reviewed statement and the proved statements differ.
- **W2 the input may be clobbered.** `unchangedOutside s s' [input, scratch, output, stack]` lets the code
  overwrite the input region. `sortCode_ok` / `msortCode_ok` do prove the input unchanged, but the `Implements*`
  forms drop it. `Implements1` fixes this (`unchangedOutside [output, work]`).
- **W3 `calleeSavedKept` covers only `sp, s0..s11` (`x2, x8, x9, x18..x27`).** It omits `gp` (`x3`) and `tp`
  (`x4`), which the RISC-V psABI says a function must not change. `msortCode_ok` proves `gp` kept internally, but it
  is not in the spec. The FP callee-saved registers `fs0..fs11` are omitted too. That is harmless only because
  `Cfg` fixes `FS = 0`, so FP instructions trap and no trap-free run can touch them.
- **W4 "nothing else changed" does not cover CSRs.** The final state only has to satisfy `Cfg` (the 11 control
  fields) and the conditions above. A one-word mutant that writes `mscratch`, `mtvec`, `mepc`, `mcause`, `mie`, `mip`,
  `mideleg`/`medeleg`, `satp`, `pmpaddr*` (ineffective while `pmpcfg = 0`) or the counters satisfies the spec. So
  does any change to the model's `cycleCount` / `sailOutput`. `minstret` must change, so a full "all other registers
  equal" clause would need to exclude it. Suggested strengthening: `∀ r ∉ xregs ∪ {PC, nextPC, minstret,
  minstret_increment, …}, s'.regs.get? r = s.regs.get? r`.
- **W5 output length is not returned.** The spec writes `|f x|` bytes but says nothing about `a0` on return. For a
  length-varying `f` the caller must compute `|f x|` itself. This is fine for sorts and maps.
- **W6 `runsTo` is "some step", not "the first return".** It is still strong enough: the spec quantifies over the
  memory at `ra`, so it covers the parked instance, and that forces the first arrival at `ra` to have the right
  output. This is exactly the argument the mutation proofs use, and the spec would be weaker if `ra`'s contents
  were fixed by a hypothesis.
- **W7 axioms.** The 77 axioms of the RISC-V theorems are `propext`, `Classical.choice`, `Quot.sound` plus 74 opaque
  declarations of the generated model (75 `axiom`s in the model sources; `plat_term_read` is unused): 67 `riscv_f*`
  / `riscv_*To*` softfloat functions, `get_16_random_bits`, reservation hooks (`load_/match_/cancel_/valid_reservation`),
  `plat_term_write`, `sys_enable_experimental_extensions`. Each has an inhabited type (functions into
  `BitVec`/`Bool`/products, or `SailM` actions), so they cannot introduce `False`. They are uninterpreted, so the
  theorems hold for every implementation of them. They appear only because `run_hart_active`'s definition
  mentions them; under `Cfg` the FP paths trap (FS = 0) and the proofs never need their values. They are dead
  code here, but they enlarge the trusted base syntactically. Stubbing them in the model (definitions instead of
  axioms) would remove them from `#print axioms`.
- **W8 the model setting is bare M-mode.** There is no paging, PMP, interrupts or U-mode. A real OS would run the
  code in U-mode with `satp` paging. The "a correctly functioning OS hosts the process" assumption bridges this
  gap, and it is a stated one.
- **W9 `maxLen = 2^20`** is a real bound on input size; the proofs need `|x| < 2^32` (msort) / `< 2^63` (insertion).
