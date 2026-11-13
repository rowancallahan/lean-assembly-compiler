# Lean 4.29.0 -> 4.34.1 for the RISC-V side

Status: **step 1 done, step 2 done (model builds), step 3 partly done (Proven builds up to `Proven.Step`; `Proven.Words` has 78 failing lemmas), step 4 not reached.**
Everything below was done in copies (`/home/user/deps434/sail-riscv-lean`, `/home/user/p434/{deps,proven}`); the 4.29 build in `../deps` is intact.
Reproduce: `lean434/port_model.sh DIR` (model) and `lean434/proven_434.patch` (Proven side, `patch -p0`-style unified diff of 6 files vs this branch).

## Step 1: Lean 4.34.1
`lean-4.34.1-linux.tar.zst` from the GitHub release extracts into `~/.elan/toolchains/leanprover--lean4---v4.34.1`; 21 s. Works with elan (`lean-toolchain` pin).

## Step 2: model `opencompl/sail-riscv-lean`
Upstream check: `origin/main` (51c635c4, 2026-08-20) is the newest commit and pins **v4.29.0** with lean-sail `v5` (`lean-toolchain` history: nightly-2026-01-22 -> nightly-2026-03-05 -> v4.29.0). No branch is on a 4.3x toolchain, so there is no newer model to try. The ARM model uses lean-sail `v10`, which names the function `sail_assert` (see below); v6..v9 exist but the generated RISC-V model was not regenerated against them.

Error classes on the unmodified model with 4.34.1 (copy of 51c635c4, Sail v5 builds fine, 10/135 jobs):
1. **`assert` is now a keyword** (experimental intrinsic verification syntax): 368+ errors `LeanRV64D/<Mod>.lean:<line>:13: Function expected at  false  but this term has type Bool ... applied to "Pattern match failure at unknown location"` (e.g. `ZawrsInsts.lean:225`, `ZicondInsts.lean:225,245`, ... 30 modules, `maxErrors` stops at 100 per file); plus `Step.lean:449` (inline `then assert (hart_is_active ..)`). Mechanical: rename the function `assert` -> `sail_assert` (the name lean-sail v10 uses) in `Sail/ConcurrencyInterfaceV1.lean:192`, `Sail/ArchSem.lean:304`, `LeanRV64D/SpecializationV1.lean:38,38` and the ~970 call sites (958 `assert false "Pattern match failure ..."` etc.). 4 sed commands.
2. **Elaboration blow-up (hang) in `LeanRV64D/RvfiDii.lean` `print_rvfi_exec`** (lines 1186-1224, 19 statements `(pure (print_bits "..." (get_x (<- readReg r))))`): 4.29 builds the file in 6 s; 4.34.1 ran >30 min and 12 GB RSS (killed). Bisected: first 8 statements +1.3 s, 10 statements +5 s, i.e. exponential in the number of such statements, caused by the new `do` elaborator. Fix: `set_option backward.do.legacy true in` before that one `def` (3 s). Setting the option for the whole model is NOT possible (`the legacy do elaborator only supports a term after <-` in PhysMemInterface, Types, PlatformConfig, ...).
3. Nothing else: after 1 and 2 the whole model (135 jobs) builds with only warnings (unused-`open` ambiguity in Sail, intrinsic-syntax warnings). Wall times: failing build runs 78 s / 53 s / 21 s; the successful rebuild after the last fix 8 s (rest cached); the heavy modules are the same as on 4.29 (`InstsEnd` 174 s vs 212 s on 4.29). Rough clean build ~7-10 min with 4 cores.
All fixes are mechanical; none changes a definition's meaning (item 2 changes only which `do` elaborator is used for a debug-print function the proofs do not touch; item 1 is a rename). Note the proofs depend on the model's definitions unchanged: they are, modulo the rename `Sail.ConcurrencyInterfaceV1.assert` -> `sail_assert`, which the proofs do not mention (`grep assert Proven/` empty).

## Step 3: `Proven` against the 4.34.1 model (toolchain 4.34.1; the Sail dependency in `.lake/packages/Sail` must be the patched copy)
| module | result |
|---|---|
| `SailEval` | builds unchanged (2.7 s); no Meta API renames needed |
| `Spec` | builds unchanged (2 s) |
| `Regs` | builds unchanged (96 s) |
| `Step` | needed 3 fixes (below), then builds (18 s) |
| `Code` | builds unchanged (1 s) |
| `Words` | 78 of 233 lemmas fail (lines 281..627, all other lemmas incl. add/sub/and/or/xor/shifts/consts now pass), 212 s |
| `Compiler`, `Reify` | not reached (depend on `Words`) |

Error classes in `Proven`:
1. `Step.lean:195` `sail_eval: stuck at (match 4 with | 0 => .. | 1 => .. | n.succ => ..) s` (the `fetch` lemma): `reduceMatcher?` under reducible transparency no longer reduces a matcher on the literal `4`, and `SailEval` only retries at default transparency when a discriminant changed. Fix (in `SailEval.lean`, 4 lines, small, not a redesign): in the `unless changed` branch try `reduceMatcher? e` at default transparency before `stuck`.
2. `Words.lean:41` (every `step_word`; originally 102 errors): `simp made no progress` with note `target expression is not type-correct under the implicit transparency level ... function expected  run_hart_active 0 s`; `set_option linter.tacticCheckInstances true` says: mark `EStateM` `@[implicit_reducible]`. `simp` now type-checks its goal at `.implicit` transparency and cannot see through `SailM`. Fix: `attribute [local implicit_reducible] EStateM LeanRV64D.Functions.regidx_bit_width LeanRV64D.Functions.log2_xlen` in every file that uses `step_word`/`sail_eval` (Step, Words (+`gen_words.py`), Compiler, Reify); `local` is mandatory (`failed to set reducibility status, X has not been defined in this file`). The last two names were found by following the next errors: `sail_eval: simp failed ... failed to synthesize Decidable (extractLsb 6#5 ((fun x y => x - y) (<- regidx_bit_width) 1).toNat 0 = 6#5)` (also for `log2_xlen` in the shift words, 11 lemmas).
3. `Step.lean:351` (in `step_word_core`) `simp only [Proven.getX_eq] at hQ` now fails with `simp made no progress` because `hQ : True` is already beta-reduced. Changed to `try simp only ... at hQ` (a `try` is the minimal change; the alternative is dropping the line for the `Q := fun _ => True` words).
4. **Open** (`Words.lean:281`-`627`, 78 errors, `unsolved goals`): the words for `ult`, `slt`, `eq` and `ite` (the comparison/branch words). Example, `op_ult_0` goal `refine_1`: `... .insert x5 (if xval s.regs 5 < xval s.regs 6 then 1#64 else 0#64) = ... .insert x5 (if xval s.regs 5 < xval s.regs 6 then 1#64 else 0#64)` both sides print identically (so they differ in a hidden `Decidable`/`LT` instance or in implicit arguments; `simp` leaves it unsolved and one `rfl` try inside the same context also did not close it). Not diagnosed further. Likely cause: the `ite_ult/ite_slt/...` normal-form simp lemmas in `Words.lean:15-37` and `BitVec` `<`/`slt` instance changes between 4.29 and 4.34; expect a per-lemma instance fix or restating those lemmas with `decide`-instance arguments.

## Estimate
- Model: done, ~1 hour of work (the hang bisection took most of it); needs regeneration/patching of lean-sail/model if upstream later moves (use `port_model.sh`).
- Proven: `SailEval` + `Step` are ported. Remaining: item 4 (comparison words, 78 lemmas) — unknown cause, plausibly 0.5-1 day; then `Compiler`/`Reify` (not yet attempted; expect `compile_ok` proof to rely on the `Words` statements unchanged) and step 4 (`#print axioms Proven.compile_ok`, four-way test: the Python side does not depend on the Lean version). Risk: the unknown number of further simp-normal-form differences in `Compiler.lean` (~300 lines of proof).
- Combined single-file import of both models: also needs both lean-sail versions (v5 for RISC-V vs v10 for ARM) to coexist as differently named packages/namespaces (`Sail` clash); not investigated. Porting the RISC-V model to Sail v10 would remove that clash but means regenerating the model with a newer Sail compiler.
No theorem was weakened or `sorry`'d.
