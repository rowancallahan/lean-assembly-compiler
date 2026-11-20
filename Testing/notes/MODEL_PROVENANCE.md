# Machine-model provenance (owner: "provenance of the ARM and RISC-V models is very important")

Last checked 2026-11-20 against `nano-v2-src`. Every fact cites the file or command that shows it. "Not recorded" means
no file proves it; the line then says how it was inferred. Keep this file updated whenever a pin, patch, flag or
toolchain changes.

| model | repo @ commit | release? | Lean / lean-sail | patches | used by |
|---|---|---|---|---|---|
| Sail RISC-V (trusted) | `opencompl/sail-riscv-lean` @ `51c635c` | no (nightly bot output) | 4.29.0 / lean-sail `v5` = `0794631` | none | RISC-V theorems (`nano-v2-src`, `main`) |
| Sail ARM | `rems-project/sail-arm` @ `5416ef6`, generator `rems-project/sail` @ `ef5dca5` | no | 4.34.1 / lean-sail `v10` = `e4745c8` | 1 generator patch + 1 generator flag; ARM sources unmodified | `Arm/proofs`, `Arm/apc` bridges |
| DeepMind arm64 | `google-deepmind/code-verification` @ `b0f729a` | no | ours: 4.34.1 (theirs: 4.34.0) / no lean-sail | none | `Arm/apc` (`Apc`, `Blocks`: `C_correct_armDM`) |
| RISC-V regenerated (§4) | `riscv/sail-riscv` @ `b7d1357`, generator Sail @ `97aa617` (no patches); repo branch `deps-rv-regen434` @ `4cf120c8` | no | 4.34.1 / lean-sail `v10` = `e4745c8` | none (banner comment only) | RISC-V theorems on `release-434` |

## Content hashes (one command for every model)

`Testing/scripts/model_hash.sh DIR` does
`cd DIR && find . -path ./.lake -prune -o -type f -name '*.lean' -print | LC_ALL=C sort | xargs sha256sum | sha256sum`.
Paths are relative to DIR, the order is byte order (locale-independent), and `.lake` (lake's packages and build) is
excluded. It prints the hash and the file count.

| model | DIR | hash | files | old value (other command) |
|---|---|---|---:|---|
| Sail RISC-V regenerated (§4, `release-434`) @ `deps-rv-regen434` 4cf120c8 | `../deps/sail-riscv-lean` | `6ac35da94bf8af379ce9160b39bf3f93b28dd463b0356b6803d40316dcb8bfae` | 161 | none |
| Sail RISC-V @ 51c635c (§1, Lean 4.29 branches) | `../deps/sail-riscv-lean` | `aa2a82c9e3ad746da34678c0405250a1a7b35e6a413e82f5137e32d40d338059` | 161 | `d6dbd722…` = `find LeanRV64D LeanRV64D.lean …` run in DIR |
| Sail ARM, committed | `Arm/model` | `8f79d6b294568b8d6e8d4916be6c8a67bfe475717513dd5b0535c69ff2e7344f` | 35 | `cbfbcd50…` = `find Arm/model/Armv9 …` at the repo root (no `Armv9.lean`) |
| Sail ARM, partitioned (`partition.py` output) | the partition's output dir | `a4b93808fc510f6413a7bdcec606b866a43f11f23a94a93eef094189524cef46` | 118 | `389f6d21…` (Sail agent, `find Armv9 Armv9Core Armv9.lean …`) |
| DeepMind arm64 @ b0f729a | `code-verification/arm64-semantics/Arm64` | `82094c4a51657bcc084fd3136a4741d94154e0ce018771c1e182fad164a6d9d4` | 134 | none recorded |

Single-file hashes, such as the partitioned definition dump `76a23330…` (ARM_FAST.md §9), are plain `sha256sum FILE`.

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
* **Content hash** (`Testing/scripts/model_hash.sh ../deps/sail-riscv-lean`, see "Content hashes" above):
  `aa2a82c9e3ad746da34678c0405250a1a7b35e6a413e82f5137e32d40d338059`, 161 files.
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
  * Content hash (`Testing/scripts/model_hash.sh Arm/model`):
    `8f79d6b294568b8d6e8d4916be6c8a67bfe475717513dd5b0535c69ff2e7344f`, 35 files (`Armv9.lean` + 34 modules).
  * **Byte-identical regeneration has not been verified** (DIFFS.md, "Not yet verified"). `regen.sh` now prints
    `model_hash.sh $OUT` to compare with this value, and `Testing/scripts/bigbox` step 2 compares file by file.
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
  * **Layout of the build used for `Arm/sail` (`C_correct_armSail`, f617794f) and for `Arm/proofs` since 36959daa**
    (recorded by the Sail agent, 2026-11-20): the **partition**, built from scratch in a fresh container:
    * Source: `Arm/model` as committed. Its last change is ae0e92cf. Lean 4.34.1; lean-sail `e4745c8`, checked out by
      hand after copying `Arm/model/lake-manifest.json` (a `lake update` had moved it to `e234ce9`).
    * Partition: `python3 Arm/gen/partition.py Arm/model /home/user/armv9-lean Arm/proofs/Arm`, run at 0d06146f.
      `partition.py` last changed in 020876c4. The proof files read for the core roots were those of 0d06146f.
    * Build: `Arm/gen/build_part.sh /home/user/armv9-lean 1`, 131 jobs, 0 errors. One container restart; lake
      resumed. Peak RSS 13.15 GB (SysregsAutogen.P19).
    * Hashes (sha256 of the `sha256sum` listing, file names included, so the hash depends on the working directory):
      * `cd Arm/model && find . -name '*.lean' | sort | xargs sha256sum | sha256sum` = `8f79d6b2…2e7344f`
        (full: `8f79d6b294568b8d6e8d4916be6c8a67bfe475717513dd5b0535c69ff2e7344f`).
      * `cd Arm/model && find Armv9 -name '*.lean' | sort | xargs sha256sum | sha256sum` = `619d40d1…1e76a08`.
      * Partitioned tree, `cd /home/user/armv9-lean && find Armv9 Armv9Core Armv9.lean -name '*.lean' | sort |
        xargs sha256sum | sha256sum` = `389f6d21…2eb55a370`
        (full: `389f6d2157a7c55ca3fc3c9de2d757d57ee275c30b0f68bfffc672c2eb55a370`). 117 files under `Armv9`/`Armv9Core`.
    * **Reconciled (O, 2026-11-20):** `cbfbcd50…` was run at the repo root as
      `find Arm/model/Armv9 -name '*.lean' | sort | xargs sha256sum | sha256sum`. That hashes the path strings
      `Arm/model/Armv9/…` and leaves out the top file `Armv9.lean`. Reproduced exactly; it is replaced by the
      `model_hash.sh` value above. The `8f79d6b2…` here is the same as `model_hash.sh Arm/model`.
    * Independent rebuild (O, 2026-11-20, for the `Arm/sail` check): `partition.py` of f617794f's `Arm/model` with
      f617794f's proof files gives a tree byte-identical to the one above. Under the command above it is again
      `389f6d21…`; `model_hash.sh` of the partitioned tree is
      `a4b93808fc510f6413a7bdcec606b866a43f11f23a94a93eef094189524cef46`, 118 files. The core roots did not change
      between 0d06146f and f617794f.
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
  * Content hash (`Testing/scripts/model_hash.sh .../arm64-semantics/Arm64`):
    `82094c4a51657bcc084fd3136a4741d94154e0ce018771c1e182fad164a6d9d4`, 134 files (the package directory:
    `Arm64.lean`, `Trusted`, `Legacy`, `Testing`).
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

## 4. Regenerated RISC-V model for Lean 4.34 (used by `release-434`)

The release builds every RISC-V theorem against this model instead of §1's. **It is not the trusted §1 model.**
The full record is `Riscv/gen/PROVENANCE.md` (branch `rv-regen-434`, merged into `release-434`). Summary:

* **Generator:** `rems-project/sail` branch `sail2` @ `97aa617dcd4d01575f773cb58ea1e8686858c8c2` (2026-11-17).
  * Not a tagged release: the newest tag `0.20.3` predates the Lean 4.34 port `31342bdb`.
  * No patches. OCaml 5.2.1 via opam; Z3 4.8.12.
* **Input:** `riscv/sail-riscv` @ `b7d13572fcd4a87d0999eb6303652cd05a47881e` (2026-08-19). This is the same
  specification input inferred for §1, from before the concurrency-interface-v2 move.
* **Base:** `opencompl/sail-riscv-lean` @ `51c635c` (README, `report.py`, `build_log.txt` kept). The generated files
  replace the model. The only hand edit is a one-line banner comment at the top of each file, naming the model as
  regenerated.
* **Lean toolchain:** 4.34.1. **lean-sail:** `v10` = `e4745c8`, as in §2.
* **Where:** orphan branch `deps-rv-regen434` @ `4cf120c8` of this repo, checked out at `../deps/sail-riscv-lean`.
  Reproduce with `Riscv/gen/regen434/regen.sh`.
* **Content hash** (`model_hash.sh`): `6ac35da94bf8af379ce9160b39bf3f93b28dd463b0356b6803d40316dcb8bfae`, 161 files.
  This was recomputed independently (O, 2026-11-20) on a fresh worktree of `4cf120c8`.
* **Diff against §1:** `Testing/notes/rvregen434/model.diff.gz` (164 files, +14,511/−31,093). The definition-level
  comparison and its classification are in the `Riscv/gen/regen434/` tools and `RV_REGEN_434.md`.
* **Theorems on it in `release-434`:** all of §1's (REVIEW `C_correctLO` / `C_runsO` / self theorems, the `Riscv` lib).
  Their axioms are pinned in `review_axioms.txt` of `release-434`.
* **Not the same thing:** `rv434-experiment` is the RISC-V model **hand-edited** for 4.34.1 (`Riscv/gen/patch_434.sh`,
  inverse check `verify_434.py`). It is experimental and untrusted, and no result counts from it (`BRANCHES.md`).
