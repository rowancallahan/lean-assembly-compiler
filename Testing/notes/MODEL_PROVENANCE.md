# Machine-model provenance (owner: "provenance of the ARM and RISC-V models is very important")

Last checked 2026-11-20 against `nano-v2-src`. Every fact cites the file or command that shows it. "Not recorded" means
no file proves it; the line then says how it was inferred. Keep this file updated whenever a pin, patch, flag or
toolchain changes.

| model | repo @ commit | release? | Lean / lean-sail | patches | used by |
|---|---|---|---|---|---|
| Sail RISC-V (trusted) | `opencompl/sail-riscv-lean` @ `51c635c` | no (nightly bot output) | 4.29.0 / lean-sail `v5` = `0794631` | none | RISC-V theorems (`nano-v2-src`, `main`) |
| Sail ARM | `rems-project/sail-arm` @ `5416ef6`, generator `rems-project/sail` @ `ef5dca5` | no | 4.34.1 / lean-sail `v10` = `e4745c8` | 1 generator patch + 1 generator flag; ARM sources unmodified | `Arm/proofs`, `Arm/apc` bridges |
| DeepMind arm64 | `google-deepmind/code-verification` @ `b0f729a` | no | ours: 4.34.1 (theirs: 4.34.0) / no lean-sail | none | `Arm/apc` (`Apc`, `Blocks`: `C_correct_armDM`) |
| RISC-V regenerated (`rv-regen-434`) | not yet on origin | n/a | target 4.34.1 / `v10` | n/a | nothing yet |

## 1. Sail RISC-V model (trusted for every RISC-V theorem)

* **Repo and commit:** `https://github.com/opencompl/sail-riscv-lean` @ `51c635c460125ac87955d061fcd902ce03b8011f`
  (2026-08-20 06:16 UTC, branch `main`).
  * Shown by `git -C ../deps/sail-riscv-lean log -1` and `git remote -v`. The working tree has no local changes
    (`git status --short` is empty).
  * Used unmodified on `nano-v2-src` and `main`. `Testing/notes/BRANCHES.md` says so; `rv434-experiment` is the only
    branch with hand edits, and it is untrusted.
* **How this repo reaches it:** `lakefile.toml` has `[[require]] name = "Lean_RV64D", path = "../deps/sail-riscv-lean"`
  (a path dependency, so `lake-manifest.json` records no commit for it). The checkout comes from the
  `origin/build-cache` branch (`sail-riscv-lean.tar.zst`; restore steps in `Testing/notes/BUILD_PROFILE.md` and
  `BUILD_CACHE_TEST.md`).
* **Release:** none. `git ls-remote --tags` on the repo shows no tags. Commit 51c635c is a daily bot commit
  (`.github/workflows/update-sail-build.yml`, `cron: "0 6 * * *"`).
* **Generator versions: NOT RECORDED upstream.** The commit message is "Update main to output generated at ", with the
  hash missing.
  * The workflow clones `rems-project/sail` and `riscv/sail-riscv` at their default-branch HEADs, unpinned. It builds
    with `cmake --build build/ --target generated_lean_rv64d`.
  * Inferred by timing (`Testing/notes/RV_MODEL_434.md` on `rv434-experiment`, "Regeneration route"): Sail `8eb1fb6b`
    (2026-08-18; backend targets 4.29.0 and lean-sail v5) and sail-riscv `b7d1357` (2026-08-19). This is not verified
    by regeneration.
* **Lean toolchain:** `leanprover/lean4:v4.29.0` (`../deps/sail-riscv-lean/lean-toolchain`, repo `lean-toolchain`).
* **lean-sail:** `rems-project/lean-sail` tag `v5` = `079463134b9c50450b8393e1566a09fc492a34d9`. Shown by the model's
  `lake-manifest.json` and the repo's `lake-manifest.json` (`"inputRev": "v5"`); `git ls-remote --tags` shows `v5` is a
  lightweight tag on that commit.
* **Patches:** none on the trusted branches.
* **Content hash:** sha256 over the sorted per-file sha256 of `LeanRV64D.lean` + `LeanRV64D/*.lean` (160 files) is
  `d6dbd722e6dd33f2918a54384ad6c0bf7fd213d4267d9163a11253de776008be`. Command:
  `find LeanRV64D LeanRV64D.lean -name '*.lean' | sort | xargs sha256sum | sha256sum`.
* **Axioms it adds:** the model declares opaque platform and float primitives as `axiom`
  (`LeanRV64D/RiscvExtras.lean`, e.g. `plat_term_write`, `load_reservation`).
  * 74 of them reach the REVIEW theorems: `cancel_reservation`, `get_16_random_bits`, `load_reservation`,
    `match_reservation`, `valid_reservation`, `plat_term_write`, `sys_enable_experimental_extensions`, and the
    `riscv_f16*/f32*/f64*`, `riscv_i*To*`, `riscv_ui*To*` float conversions.
  * They are pinned in `Testing/scripts/review_axioms.txt` and checked by `Testing/scripts/review_axioms.sh`. Older
    theorems are pinned in `Testing/scripts/expected-axioms.txt`.
* **Reproduce:**
  * Restore the cache: `git show origin/build-cache:sail-riscv-lean.tar.zst | zstd -dc | tar xf - -C ../deps`.
  * Or clone directly: `git clone https://github.com/opencompl/sail-riscv-lean ../deps/sail-riscv-lean && git -C ../deps/sail-riscv-lean checkout 51c635c`.
  * Then `lake build` on 4.29.0.
  * Regenerating the text from Sail is not reproducible today, because the generator commits are unknown (above).
* **Theorems that depend on it:**
  * `Nano/V2Self/REVIEW.lean`: `C_correctLO`, `C_runsO`, `C_runs`, `self_correct_C`, `self_runs_C`.
  * `Spec/Riscv.lean`, `Spec/RiscvMachine.lean`, `Spec/Implements1.lean` and the `Riscv` lib: `Proven.compile_ok`,
    `gcd_ok`, `msortCode_implements`, … (`Testing/scripts/expected-axioms.txt`).
  * Path to the model: `Nano/V2Self/Proof/Machine/SimW` → `Nano.V2.Enc` / `Nano.V2.Sim` → `Riscv.Steps.*` → `LeanRV64D`
    (module list in `BRANCHES.md`).
  * Model-free: `Cert.sem_C`, `SrcGen.link_pc`, `shiftInv`, and the generic `C_correct_on` / `C_runs_on`.
* **Not the model (tests only):** `../deps/sailsim/sail-riscv-Linux-x86_64`, a Sail RISC-V C simulator binary from
  `origin/build-cache:sailsim.tar.zst`. It is used by test scripts and by no proof.

## 2. Sail ARM model (ARMv9.4-A)

* **ARM sources:** `https://github.com/rems-project/sail-arm`, directory `arm-v9.4-a`, @
  `5416ef6b43e9527c38dc71fb752259c1d01a47e1` (2026-11-09).
  * Pinned in `Arm/gen/regen.sh` (`ARM_REV`); unmodified (`Arm/gen/DIFFS.md`, table).
  * Release: none. `git ls-remote` shows no tags; the commit is `master` HEAD as of 2026-11-20.
* **Generator:** `https://github.com/rems-project/sail` @ `ef5dca5ac2048a19ab971f128bb13477561c021c` (2026-11-12).
  * Pinned in `Arm/gen/regen.sh` (`SAIL_REV`).
  * Not a release: the newest Sail tag is `0.20.3`, and the released Sail has no usable Lean backend for this
    (README of sail-riscv-lean: "The released version of Sail does not support Lean output").
  * Built from source with opam (`regen.sh`: `opam install . --deps-only && make install`).
* **Patches and flags (all on the generator; the ARM Sail sources are unmodified):**
  1. `Arm/gen/patches/sail/0001-lean-backend-fixes.patch`. sha256 `096260358f8ec2480affb057d4a9decb41f42b2635b11fef54f4a47cd50c3620`.
     One file, `src/sail_lean_backend/pretty_print_lean.ml`; 67 changed lines. Explained in `Arm/gen/DIFFS.md`:
     * (a) a `unit`-typed `throw` is printed with a type ascription;
     * (b) a `do` is inserted inside `(( e ) : T)`;
     * (c) if/else chains at least 1000 levels deep (`if_chain_min`) are cut into tail definitions `f_tailK`.
       Only `__DecodeA64_SVE` is affected (11 helpers in `DecodeEnd.lean`). Each helper is the verbatim tail, but
       the equality to the unsplit chain is **not** stated as a Lean theorem.
  2. Flag `SAIL_FLAGS='--lean-partial-function Reduce__1'` (`regen.sh`). It makes `Reduce__1` (`V8Base.lean`) a
     `partial def`, replacing the model's only `sorry`: a termination proof that is false as generated. Cost:
     `Reduce__1` is opaque. With it, `#print axioms __DecodeA64` = `propext, Classical.choice, Quot.sound` (DIFFS.md).
  * Hand-written upstream file `arm-v9.4-a/lean/ArmExtras.lean`, unmodified. Its `decreasing_trivial` extension falls
    back to `sorry`; with the flag, no `sorry` remains (DIFFS.md, "sorry census").
* **Lean toolchain:** `leanprover/lean4:v4.34.1` (`Arm/model/lean-toolchain`).
* **lean-sail:** tag `v10` (`Arm/model/lakefile.toml`). The commit is `e4745c82fe329f162700020dcd31da6b342473b9`
  (`Arm/model/lake-manifest.json`). `e234ce9`, as written in `DIFFS.md`, is the annotated tag object of `v10`, which
  points to `e4745c8` (`git ls-remote --tags`); both name the same code.
* **Generated text:** committed in `Arm/model/` (`Armv9.lean`, `Armv9/*.lean`, 34 modules).
  * sha256 over the sorted per-file sha256 of `Arm/model/Armv9/*.lean` is
    `cbfbcd50df4f655008febb6cbe24a8cd3677b5745ae6cd23df47cfaf9ffbf8ab` (the same pipeline as the last line of `regen.sh`).
  * **Byte-identical regeneration has not been verified** (DIFFS.md, "Not yet verified"); `regen.sh` prints the hash
    to compare.
* **Partition step:** `Arm/gen/partition.py`, called at the end of `regen.sh`, writes `$OUT-part`. Details in
  `Testing/notes/ARM_FAST.md` §9.
  * It moves declarations verbatim into a core layer `Armv9Core.{V8Base,Instrs64,Fetch,Interrupts,Devices}` (the
    closure of the model names used by `Arm/proofs`) plus the rest. Large rests are cut into `Armv9.M.Pnn` parts.
    Names and namespaces are unchanged.
  * Asserts: every declaration is written once with its original text; `partial def Reduce__1` occurs once; file order
    is topological.
  * `Arm/gen/scope_check.py` finds 0 moved declarations that mention a name not in scope at their original position.
  * **Not run:** the (name, type hash, value hash) diff of the partitioned build against an unpartitioned build
    (`dump_hashes.lean` + `dump_summary.py`). No complete unpartitioned build exists, because SysregsAutogen runs out
    of memory. The partitioned dump is ready: 45,241 constants, sha256 `76a23330…` (ARM_FAST.md §9).
* **Built copy:** `/home/user/armv9-lean`, a built copy of `Arm/model` (`Testing/notes/AGENT_OVERVIEW.md`).
  * Agents must not rebuild it (AGENT_OVERVIEW.md, Rules).
  * It is not in every container. It is absent from this one, so `Arm/proofs` and the `Arm/apc` bridges cannot be
    checked here.
  * Which layout it holds (unpartitioned `Arm/model` or the partition) is not recorded in a committed file. **TODO:**
    the Sail agent should record its source hash.
* **Reproduce:** `W=… OUT=… Arm/gen/regen.sh` (needs opam with Sail's deps and z3), then compare the printed hash with
  the one above. Build with `lake build` plus `lake build Armv9.<M>` for the modules `Armv9.lean` does not import
  (DIFFS.md, "Build notes"; V8Base needs about 12 GB).
* **Theorems that depend on it:**
  * `Arm/proofs/Arm/*`: `compile_ok`, `full_word`, `full_ret`, `fetch_ok`, `step_ok`, the `full_*` per-form steps,
    `witness_full`. Axioms are printed by `Arm/proofs/Arm/Axioms.lean`, all `propext, Classical.choice, Quot.sound`
    (`Arm/proofs/README.md`).
  * `Arm/apc/Bridge*.lean`: `bridge_step`, `sim`, `gcd_sail`, `sort_sail`. These relate the Sail model to DeepMind's.
    Built by `Arm/apc/check.sh` step 3.
  * All under `ArmFull` (pinned configuration, `Arm/proofs/gen/pins.py`): hypotheses, not axioms.

## 3. DeepMind arm64 model

* **Repo and commit:** `https://github.com/google-deepmind/code-verification` @
  `b0f729accbc21a0413e7ca4e1da43fa45b5f2e1b` (2026-11-11, "Verify 10 more library routines in the binary; trusted hooks
  37 → 27 (#2)"). Package `arm64` (`arm64-semantics/Arm64/lakefile.toml`, no dependencies, `lake-manifest.json` has an
  empty package list). Apache-2.0 (`Arm/apc/README.md`).
  * Pinned by `Arm/apc/check.sh`, which aborts unless the checkout is at `b0f729a`, and by `Arm/apc/README.md`.
  * Referenced by path (`Arm/apc/lakefile.toml`: `path = "../../../deps/code-verification/arm64-semantics/Arm64"`);
    never copied into this repo.
* **Release:** none. The repo has no tags. Upstream `HEAD` is now `8c8d371` ("Export from internal repository (#5)"),
  one commit after the pin (`git ls-remote`, `git log`).
* **Lean toolchain:** their `lean-toolchain` says `v4.34.0`. We build their package with **4.34.1**
  (`Arm/apc/lean-toolchain`; `check.sh` calls 4.34.1's `lake`; nothing of theirs is edited).
* **Patches:** none. Only `Arm64.lean`, `Arm64/Trusted`, `Arm64/Legacy` are built; `ProofLib` is checked out but
  neither built nor used (`Arm/apc/README.md`).
* **Trust note:** their lakefile sets `precompileModules = true`. The decoder, evaluator and spec elaborators run as
  native code at **elaboration** time. The kernel still checks every proof term; our proofs use no `native_decide`.
* **Reproduce:**
  * `cd /home/user/deps && git clone --filter=blob:none --no-checkout --sparse https://github.com/google-deepmind/code-verification.git`
  * `cd code-verification && git sparse-checkout set arm64-semantics/Arm64 arm64-semantics/ProofLib && git checkout b0f729a`
  * Then `cd Arm/apc && lake build Blocks.ArmDMTop Blocks.AxiomsDM`. Cold, 507 jobs, 8 min on 4 cores, measured
    2026-11-20 in a clean worktree at `f7f03b9`.
* **Theorems that depend on it:**
  * `Arm/apc/Apc/*`: `apc`, `compile_apc`, `gcd_apc`, `sort_apc`, `msort_apc`, `callsCode_implements_apc`, … (printed
    by `Apc/Axioms.lean`).
  * `Arm/apc/Blocks/*`: `a64DM`, `blockOKD`, `dm_*`, and the top theorems `C_correct_armDM` / `C_runs_armDM`
    (`Blocks/ArmDMTop.lean`, `Blocks/AxiomsDM.lean`). All `propext, Classical.choice, Quot.sound`.
  * `C_correct_armDM` = `C_correct_rv2arm a64DM`. `C_correct_rv2arm`, `C_correct_arm` and `C_correct_on` themselves
    are model-free: they quantify over any `A64Sem` / `JTarget` instance.
  * The bridges in §2 use both ARM models.

## 4. Regenerated RISC-V model for Lean 4.34 (`rv-regen-434`, upcoming)

* **Status:** no branch `rv-regen-434` on origin as of 2026-11-20 (`git branch -r`). Nothing depends on it.
* **Plan, per `RV_MODEL_434.md` "Regeneration route":** regenerate with the official Sail Lean backend, Sail ≥ `31342bdb`
  (2026-11-09; targets 4.34.1 and lean-sail v10).
  * Risk: sail-riscv `4f8ce82` (2026-10-01) moved to concurrency interface v2, which changes the API used by
    `Spec/Riscv*` and `Riscv/Steps`.
  * Regenerating the old sail-riscv `b7d1357` with new Sail is untested upstream.
* **When it lands, record here:** Sail commit, sail-riscv commit, any patches or flags (with a DIFFS file),
  lean-sail tag and commit, toolchain, content hash, a regeneration command, and which theorems move to it.
* **Not the same thing:** `rv434-experiment` is the RISC-V model **hand-edited** for 4.34.1 (`Riscv/gen/patch_434.sh`,
  inverse check `verify_434.py`). It is experimental and untrusted, and no result counts from it (`BRANCHES.md`).
