# Provenance: RISC-V model REGENERATED with Sail 97aa617dc (not the trusted model)

Branch `rv-regen-434`. Generated 2026-11-20. The model is generated output only: apart from the one-line banner
comment added at the top of each file, nothing was edited by hand.

| item | value |
|---|---|
| Sail | `https://github.com/rems-project/sail`, branch `sail2`, commit `97aa617dcd4d01575f773cb58ea1e8686858c8c2` (2026-11-17). **Not a tagged release.** The newest tag, `0.20.3`, predates the Lean 4.34 port (`31342bdb`, 2026-11-09), so it still targets Lean 4.29 and lean-sail v5. `97aa617dc` is `3626605b` (the last Lean-backend commit) plus one CI-only commit. It also has the do-printing fixes `47530a5e` and `322a415d`. `sail --version` reports `0.20.3`, the opam package version. |
| sail-riscv | `https://github.com/riscv/sail-riscv`, commit `b7d13572fcd4a87d0999eb6303652cd05a47881e` (2026-08-19): the same input as the trusted model (see below), from before the concurrency-interface-v2 move (`4f8ce82`) |
| base | `https://github.com/opencompl/sail-riscv-lean` @ `51c635c460125ac87955d061fcd902ce03b8011f` (trusted model; its README, `report.py` and `build_log.txt` are kept) |
| OCaml / opam | opam 2.1.5 (Ubuntu 24.04 package); switch `sail` = OCaml 5.2.1; dune 3.25.0, zarith 1.14, menhir 20260209, lem 2026-05-01, linksem 0.8; all `*.opam` packages of the Sail checkout pinned from the checkout and installed |
| z3 / cmake | Z3 4.8.12 (Ubuntu), cmake 3.28.3 |
| lean-sail | `https://github.com/rems-project/lean-sail` tag `v10` = commit `e4745c82fe329f162700020dcd31da6b342473b9` (pinned in `lake-manifest.json` after `lake update`) |
| Lean | `leanprover/lean4:v4.34.1` (emitted by Sail into `lean-toolchain`) |
| generated tree sha256 | `Testing/notes/rvregen434/model_tree.sha256` holds the sha256 of every model file (banner included). Its own sha256 is `01996c3499f8dd365819a2ae2b9ff226501eb5f87e34f5533b75e073d34c2612` |
| `Testing/scripts/model_hash.sh` (from nano-v2-src) | `6ac35da94bf8af379ce9160b39bf3f93b28dd463b0356b6803d40316dcb8bfae 161` (the 161 `.lean` files; also on the orphan branch `deps-rv-regen434` @`4cf120c8`, which runners check out at `../deps/sail-riscv-lean`) |
| diff vs `51c635c` | `Testing/notes/rvregen434/model.diff.gz` (`git apply --index` on a `51c635c` checkout reproduces the tree; this was checked) and `model.diffstat` (164 files, +14511/-31093) |

## Generation command
`cmake --build build --target generated_lean_rv64d` in sail-riscv. It runs this in `model/`:
```
sail --strict-var --strict-bitvector --strict-exponentials --require-version 0.20.2
  --memo-z3-path <build>/model/sail_smt_cache --config <build>/config/rv64d_v256_e64.json
  --lean --memo-z3 --lean-output-dir <build>/model --lean-force-output
  --lean-non-beq-type instruction --lean-non-beq-type ExecutionResult --lean-non-beq-type Step
  --lean-noncomputable --lean-noncomputable-function encdec_{forwards,backwards}{,_matches}
  --lean-noncomputable-function encdec_compressed_{forwards,backwards}{,_matches}
  --lean-import-file ../handwritten_support/RiscvExtras.lean -o Lean_RV64D --all-modules riscv.sail_project
```
cmake was configured with `-DDOWNLOAD_CLI11=OFF -DDOWNLOAD_ASIO=OFF -DDOWNLOAD_JSONCONS=OFF`. These are upstream
switches for targets that do not need the C-emulator libraries. The sandbox proxy refuses `codeload.github.com`
(HTTP 403), and Lean generation does not use those libraries. Generation took 408 s with 1.1 GB peak RSS.

Reproduce: `Riscv/gen/regen434/regen.sh <workdir>`. It clones, builds Sail with opam, generates, overlays the output onto
`51c635c`, adds the banner and runs `lake update`.

## Banner
Line 1 of every `.lean` file and of `lakefile.toml`:
`RISC-V model REGENERATED with Sail 97aa617dc (rems-project/sail sail2, untagged) from riscv/sail-riscv b7d1357 (not the trusted model); provenance: Riscv/gen/PROVENANCE.md in lean-assembly-compiler`

## Provenance of the trusted model (`51c635c`), now confirmed
Sail `8eb1fb6b5bf9f18c0f89f71e94ff0c5894acd7c1` (2026-08-18) with the same sail-riscv `b7d1357`, the same cmake target
and a fresh OCaml 5.2.1 switch reproduces `51c635c`. All 160 files under `LeanRV64D/`, `LeanRV64D.lean`, `lakefile.toml`
and `lean-toolchain` are byte-identical (`diff -r`). Only `lake-manifest.json` differs: the published one is the
result of `lake update`. So every difference between the trusted model and this one comes from the Sail change
`8eb1fb6b..97aa617dc` (118 commits). The RISC-V specification input is the same.
