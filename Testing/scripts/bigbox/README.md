# Big-machine verification kit

`Testing/scripts/bigbox/verify.sh COMMIT` rechecks the machine models and the main theorems from scratch on a big box
(32–64 GB RAM, 8+ cores, 150 GB disk). It prints a PASS / FAIL / SKIP table and keeps every log. The pins it checks
are the ones in `Testing/notes/MODEL_PROVENANCE.md`.

## Running it
Use a fresh Ubuntu 24.04 box, for example AWS `r7i.2xlarge` (64 GB) or `m7i.4xlarge` (64 GB):

    sudo apt-get install -y git curl rsync zstd python3 opam build-essential libgmp-dev z3 pkg-config m4
    git clone https://github.com/rowancallahan/lean-assembly-compiler.git ~/bigbox/repo
    ~/bigbox/repo/Testing/scripts/bigbox/verify.sh <commit>       # e.g. origin/nano-v2-src

* The script checks out `<commit>` in `~/bigbox/repo`. It uses that commit's own copy of the kit, pins and proofs, so
  name a commit that contains this kit.
* Run it again to resume: finished steps are skipped. Delete `~/bigbox/results/<commit>/status/<step>` to rerun a step.
* Results go to `~/bigbox/results/<commit>/`:
  * `summary.txt`, the table;
  * `<step>.log`;
  * `rss-*.txt` (peak MB, seconds, file, per Lean process);
  * `dump-*.txt` (definition fingerprints), `dump.diff`, `regen.diffstat`.
* Nothing is pushed. Build outputs stay under `~/bigbox`.

Knobs (environment variables):

| variable | default | meaning |
|---|---|---|
| `WORK` | `~/bigbox` | everything goes here |
| `JOBS` | RAM in GB / 14 | concurrent Lean processes for the ARM model builds (one V8Base or SysregsAutogen process needs about 12–13 GB) |
| `NOSVE` | 1 if RAM ≥ 48 GB | run step 3b |
| `STEPS` | all | subset, e.g. `STEPS="1 6a 6b"` |
| `OCAML` | `ocaml-base-compiler.4.14.2` | the OCaml for the Sail opam switch (`OPAMSWITCH`, default `bigbox-sail`) |
| `REPO_URL` | the GitHub repo | where to clone from |

The lakefiles reach their dependencies by relative paths, so the layout under `WORK` is fixed: `repo/`,
`deps/sail-riscv-lean`, `deps/code-verification`, `armv9-lean` (a link to the model build used by the ARM proofs).
The header of `verify.sh` lists every directory.

## The steps
| step | what it does | PASS means |
|---|---|---|
| 1 | Installs elan, Lean 4.34.1 and an opam switch. Clones the regenerated RISC-V model (this repo's branch `deps-rv-regen434` @ `4cf120c8`, MODEL_PROVENANCE §4) and `google-deepmind/code-verification` @ `b0f729a`. Asserts that the Sail / sail-arm pins in `Arm/gen/regen.sh` and the dependency pins are the ones in `MODEL_PROVENANCE.md`. | toolchains present; all pins agree |
| 2 | Runs `Arm/gen/regen.sh`: Sail @ `ef5dca5` + `patches/sail/0001-lean-backend-fixes.patch`, built with opam; sail-arm @ `5416ef6`; `make gen_lean` with `--lean-partial-function Reduce__1`. Byte-compares every generated `.lean` with the committed `Arm/model`. | the committed model is exactly what the pinned generator produces |
| 3 | Builds the committed `Arm/model` as generated: no partition, every module, with `rssmon.py`. | the unsplit model compiles; `rss-unsplit.txt` has time and peak RSS per module |
| 3b | (optional, ≥ 48 GB) Same generator with the SVE if-chain split disabled (`if_chain_min = max_int`). Rebuilds the changed modules (expected: `DecodeEnd`) and dumps their fingerprints. | the split is not needed to compile; `dump-nosve.txt` against `dump-unsplit.txt` shows what the split changes (expected: the 11 `__DecodeA64_SVE_tail*` helpers and `__DecodeA64_SVE`'s value) |
| 4 | Against the unsplit model, with no proof edits: `Arm/proofs/check.sh`, `Arm/apc/check.sh` (the Sail↔DeepMind bridges), and `Arm/sail` (`C_correct_armSail` / `C_runs_armSail`) if that directory exists at the commit. Checks every `#print axioms`. | all build; every axiom set ⊆ {propext, Classical.choice, Quot.sound}; a missing `Arm/sail` is stated in the note |
| 5 | Partitions the committed model (`Arm/gen/partition.py`, the layout the ARM proofs normally use), builds it, and dumps (name, kind, universes, type hash, value hash) of every `Armv9.*` constant from both builds (`Arm/gen/dump_hashes.lean`). | the two dumps are identical, so the partition changed no definition. ARM_FAST.md §9 recorded the partitioned dump as 45,241 rows, sha256 `76a23330…`; the note prints this run's |
| 6a | DeepMind model: `lake build Blocks.ArmDMTop Blocks.AxiomsDM` in `Arm/apc` (Lean 4.34.1). | `C_correct_armDM` / `C_runs_armDM` use only the standard axioms |
| 6b | RISC-V: builds the regenerated RISC-V model from source (4.34.1), then all of `Nano/V2Self`, then `Testing/scripts/review_axioms.sh`. | the REVIEW theorems' axioms equal the pinned list (standard + the RISC-V model's platform/float opaques) |

Order of execution: 1, 6a, 6b, 2, 3, 3b, 4, 5. A step whose input step did not PASS is SKIPped and names that step.
Steps 3 and 3b move `armv9-lean` to point at the unsplit build. That is the point of step 4: the proofs, normally
checked against the partitioned model, are rechecked against the model exactly as generated.

## Expected cost on a 64 GB, 8-core box (estimates, not measured)
* Step 2: about 1 h (OCaml and Sail builds, then generation).
* Step 3: about 2–3 h at `JOBS=4`. DIFFS.md: `DecodeEnd` alone took about 20 min; V8Base needs about 12 GB.
* Step 3b: `DecodeEnd` without the split needs more than 27 GB (DIFFS.md). Not known to fit in 64 GB.
* Step 4: about 30 min (`Arm/Words` is about 13 min).
* Step 5: about 2 h.
* Step 6b: about 1–2 h (RISC-V model from source, then `Nano/V2Self`).

## What was dry-run on a 15 GB, 4-core box (2026-11-20)
See the commit message of the kit and `Testing/notes/MODEL_PROVENANCE.md`. Steps 3, 3b, 4 and 5 need the full ARM
model build, which does not fit in 15 GB (`SysregsAutogen` unsplit was killed at 13.2 GB, ARM_FAST.md §9). Only their
script logic was reviewed, not run.

**Since `release-434`** (everything on Lean 4.34.1): step 1 pins the regenerated RISC-V model (`deps-rv-regen434` @
`4cf120c8`), and step 6b runs on 4.34.1. `RV_CACHE` was removed, because `build-cache` holds 4.29 oleans of the old
model. The dry run on `nano-v2-src` (d0487860) used the old layout: steps 1, 2, 6a and 6b PASS there.
