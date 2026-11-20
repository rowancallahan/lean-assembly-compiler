# CHANGELOG: what changes, and the baseline it builds on

Every change is recorded here with the baseline it was checked against. "Baseline" = the last state of `main`
that was built and checked; later entries say what changed relative to it.

## Baseline B1: main @ 935c0ac1 (2026-11-20, merge of nano-v2-src)

Verified by session O on a clean tree:
- Lean 4.29.0 (main's `lean-toolchain`): full `Nano/V2Self` build, 689 jobs, OK.
  `Testing/scripts/review_axioms.sh` -> `OK: 8 theorems, axioms as pinned`:
  `Cert.sem_C` [propext, Quot.sound]; `NanoMain.shiftInv`, `AuditSpace.spaceC_ex1_eq` [propext, Classical.choice,
  Quot.sound]; `C_correctLO`, `C_runsO`, `C_runs`, `self_correct_C`, `self_runs_C`: standard 3 + the Sail RISC-V model's
  pinned opaque platform/float declarations.
- Lean 4.34.1 (`Arm/apc/lean-toolchain`, DeepMind code-verification @ b0f729a): `lake build Blocks.ArmDMTop
  Blocks.AxiomsDM`, 508 jobs, OK. `C_correct_armDM`, `C_runs_armDM`: [propext, Classical.choice, Quot.sound].
- `Spec/` matches `Spec/FROZEN.sha256` (11 files; last Spec change 1437a980, armMapping.workTop 31 -> 4, owner-approved).
- Runtime checks: `Testing/nano/v2self/arm/test_arm.sh` 74/74, `cross_check.sh` 8/8 (RISC-V and ARM under QEMU build
  each other's compiler; all identical to the self-compile, sha256 bb5558a5... for B2.bin).
- Models: see `Testing/notes/MODEL_PROVENANCE.md` (RISC-V: sail-riscv-lean @51c635c, Lean 4.29; ARM: Sail ARM
  sail-arm @5416ef6 + Arm/gen patches; DeepMind arm64 @b0f729a).
- Benchmark B1 (self-compile, RISC-V, exact count by nanorun): 86,725 B source -> 337,856 B code,
  1,454,349,112 RISC-V instructions executed (about 16,800 per source byte). QEMU wall: RISC-V 0.9 s, ARM 1.7 s.
  ARM/RISC-V executed-instruction ratio on examples/rle.lean: 7,685 / 2,149 = 3.6 (4-word ARM blocks incl. padding).

## In progress (each entry: what changes; built/checked against which baseline)

1. Sail ARM theorem (`C_correct_armSail`, nano-v2-src, session ...aJwAyBAZNhZawDfbr). Changes so far vs B1:
   36959daa VaOK replaces `va < 2^29` in Arm/proofs (address window); dfa782e6 AL1-AL6 + FullSubs compiled
   (Lean 4.34.1 against the partitioned Sail ARM model, standard 3 axioms). DeepMind side rebuilt after 36959daa:
   508 jobs, `C_correct_armDM` unchanged axioms (O). Not yet checked: Arm/apc Bridge*.lean (needs the Sail model).
2. RISC-V model regeneration (branch rv-regen-434, session ...ao3ri9NgTBDs1iibt): Sail sail2 97aa617dc (untagged;
   newest tag 0.20.3 predates Lean 4.34 support) on sail-riscv b7d1357, Lean 4.34.1, lean-sail v10 (e4745c8).
   The generated source differs in substance from B1's model (e.g. read_CSR match -> if-chain), so RISC-V proof
   fixes are expected. Merge criteria: model builds on 4.34.1; REVIEW (C_correctLO / C_runsO) builds against it with the
   same axiom set; definition comparison vs B1's model committed; PROVENANCE.md + per-file headers + regen.sh.
3. Big-machine verification kit (Testing/scripts/bigbox/, session O): unsplit ARM model + proofs + fingerprint diff.
4. Benchmarks: instruction counts (exact) per program and input size, self-compile first; profile by function.

Rule: every merge to main appends an entry here with the commit, what changed, and the build/axiom results on the
previous baseline's toolchain(s) and on the new one.

## Benchmark entry (vs baseline B1, no compiler/shim/Spec change)

- Added `Testing/notes/BENCH.md` and `Testing/nano/v2self/bench/` (run_bench.sh, profile_self.sh, nanorun_prof.c = run/nanorun.c
  plus an optional `NANORUN_PROF` per-word count, make_inputs.py, profile_regions.py, synth_scaling.py, results/).
- Checked: self-compile = 1,454,349,112 instructions (plain and profiling build), output = B2.bin byte for byte.
- Findings: run costs are linear in input size (no superlinear growth); compile cost is superlinear in the number of defs
  (flat and chain families grow about K^2 over K = 10..320, output linear); 11 generic return stubs are ~48% of the
  self-compile's instructions; function names for the profile are not resolved.
- ARM counts not done: no qemu-user / aarch64 toolchain here (package install refused by the session's permission check).

## perf-names (branch `perf-names` from nano-v2-src ff81857; vs baseline B1)

What changed (compiler C, parser stage Par1 only; lexer, Own, Gen, the machine and bridge proofs untouched):
- **Hashed def table.** `v8` (def lookup by name) scanned every def row and compared spellings (`v85`) for every
  identifier, every call head and every def registration: K^2 work for K defs (BENCH.md "Compile cost"). Now `v84` hashes
  the spelling (`s := s*33 + byte`, low 10 bits), the 1024 bucket heads live in a new layout region `[d9 + d10, d11)`, slot 7
  of each def row links the next older row of the same bucket, `v127` pushes each new row on its chain, and `v8` (`v83`)
  walks only that chain. Result and contract unchanged (same row as the linear scan).
- **Layout constants are numerals** (`gen_layout.py`): `d3 := 12352` instead of `d1 + d2`, etc. Each constant is compiled as a
  call, so `d11` cost 11 nested calls per token read; these calls were ~48% of the self-compile.
- Tokens start at `d11 = 185408` (was 184384). The 512-def cap (def ids 512 + j) is unchanged.

Built/checked on the B1 toolchains:
- Lean 4.29.0: `lake build Nano.V2Self.REVIEW` OK (13 min warm); `Testing/scripts/review_axioms.sh` -> `OK: 8 theorems, axioms as
  pinned`; every `Nano/V2Self` module builds (Tests included). Full REVIEW run at the tip; commit (a) differs from it only in
  the generated Cert/SrcLink/B2 for the summed layout constants.
  Proof changes: new `Proof/Parser/ParInvHash.lean` (`v8_lookup`: the chain walk = the linear `idxOf`; `HashRep`, kept in
  `DefsRep`); the Parser frame lemmas carry `HashRep`; `TokAgreeN` covers the token region only; `Cert/` and `SrcLink/`
  regenerated (both generators reproduce the committed files exactly from the old text first).
- Lean 4.34.1 (`Arm/apc`, DeepMind code-verification @ b0f729a): `lake build Blocks.ArmDMTop Blocks.AxiomsDM` OK (509 jobs,
  9.7 min cold; includes `Main.TopOn` and every Parser module ArmDMTop needs, `ParInvHash` included); `C_correct_armDM`,
  `C_runs_armDM`: [propext, Classical.choice, Quot.sound]; `lake build Nano` (all of apc's Nano globs, the whole Parser
  folder) OK. No 4.34-specific edits were needed.
- Fixpoint (nanorun): B1 → B2 → B3, B3 = B2 = 340,296 B, sha256 24759aa0f757e50e92e67d498a84f28ec7a0b13da6f2c9fc3d76cd0679699ed4.
  ARM: `arm/B2_arm.bin` regenerated (translator run under nanorun; the same procedure reproduces the old B2_arm.bin byte for
  byte). `cross_check.sh` not run: no qemu / aarch64 toolchain on this box (RISC-V checked with nanorun only).
- Per commit (self-compile; flat_320; chain_320): (a) hash table 789,993,519; 163.0 M; 104.0 M. (b) numeral layout
  constants 641,996,759; 134.7 M; 83.8 M.
- Benchmark vs B1 (exact RISC-V instructions, nanorun): self-compile 1,454,349,112 → 641,996,759 (−56%); flat_320
  641.9 M → 134.7 M, chain_320 391.3 M → 83.8 M, now linear (≈0.40 M per flat def, 0.24 M per chain def, K = 10..511);
  examples' compile −2.6% … −6.0% (count +0.03%); emitted code byte-identical on all of them, so run costs are unchanged.
  Details: `Testing/notes/PERF_NAMES.md`.

## release-434 (Lean 4.34.1; vs baseline B1 = main 935c0ac1)

One combined release, branch `release-434`, built from three parts plus the checks below. Entries marked TBD are not yet
measured or not recorded in the repo; none is estimated.

### Parts
- **A. Sail ARM theorem** (`Arm/sail`, a separate lake project; `C_correct_armSail`, `C_runs_armSail`: the C compiler via `rv2arm`
  correct on the Sail ARM v9.4-A model). Commits: f617794f (theorem), 36959daa (`VaOK` replaces `va < 2^29`; `ArmFullB s n`
  generalizes over `BTypeNext`), dfa782e6 (symbolic-register full steps for every form `rv2arm` emits, `FullSubs`).
  Lean 4.34.1, standard 3 axioms (`propext`, `Classical.choice`, `Quot.sound`); `Reduce__1` prints as an `opaque`
  (a generated `partial def`). `lake build ArmSail ArmSail.Axioms`: 431 jobs. It needs the partitioned model **by path**
  (`../../../armv9-lean`, see `Arm/sail/NOTES.md`), so it is not part of the root `lake build`. `Spec/` is unchanged:
  `armSail` lives outside `Spec/`. The sailv-fable notes and `NonVacuous.lean` are on `origin/sailv-fable` (8929e5fc).
  - **Temporary exception (owner-approved, 2026-11-20):** on Sail ARM, register 31 (sp) is in `armMapping.kept` but `obsS`
    reads it as 0, so `C_correct_armSail` makes no meaningful claim that sp is preserved; every other kept register is proved
    unchanged. DeepMind ARM (`C_correct_armDM`) does observe sp and proves it unchanged. To be restored by exporting
    SP_EL0/SP_EL3/PSTATE.SP from the full_* lemmas (ROADMAP).
  - Also in the release: the DeepMind AArch64 theorem `C_correct_armDM` / `C_runs_armDM` (`Arm/apc/Blocks/ArmDMTop`,
    `AxiomsDM`), now stated per start state meeting `ArmLoader X W` (37939cd1, f7f03b98, 6d85ab8c; rebuilt after 0d06146f:
    507 jobs, standard 3 axioms).
- **B. RISC-V model regenerated on 4.34.1** (branch `rv-regen-434`): Sail `97aa617dc` on sail-riscv `b7d1357`, lean-sail `v10`.
  All 160 modules build on 4.34.1 (598 s serial, peak 2.9 GB). `C_correctLO` / `C_runsO` (REVIEW) and
  `Testing/scripts/review_axioms.sh` on this model: TBD (result of the merged tree, see the check below). The generated source
  differs in substance from the trusted model: 842 constants changed vs the 4.29 model (raw), 222 values differ after
  normalization (160 short-circuit `&&`/`||` with effects, `read_CSR`/`write_CSR` match to if-chain, `round_down`/`round_up`),
  no kernel proof that old and new compute the same function (`Testing/notes/RV_REGEN_434.md` §3). Repo-side proof fixes:
  `simpa` to `simp`/`exact`, `GenTac`, `EmitOps` (Lean 4.34.1). The default lake target on that branch is `Chain434`
  (the chain without the RISC-V model).
- **C. Perf fix** (branch `perf-names`, merged as b0b2a8f8; details in the "perf-names" entry above and `PERF_NAMES.md`):
  hashed def table in the parser (`v84`, `v83`) and layout constants as numerals. New `B2.bin`, `B3.bin`, `arm/B2_arm.bin`
  (`B2.sha256` is `24759aa0...`, 340,296 B). Self-compile B1 -> B2 -> B3: B3 == B2.

### Numbers (exact RISC-V instructions by `run/nanorun.c`, vs B1)
- Self-compile: 1,454,349,112 -> 641,996,759 (-55.9%; B1's B2 was 337,856 B, now 340,296 B).
- Compile time is linear in the number of defs: flat_K and chain_K, K = 10..511, about 0.40 M instructions per flat def and
  0.24 M per chain def (flat_320: 641.9 M -> 134.7 M; chain_320: 391.3 M -> 83.8 M). The 512-def cap is unchanged.
- Examples compile -2.6% .. -6.0%; emitted code is byte-identical, so run costs are unchanged.
- QEMU wall time of the new compilers, ARM instruction counts: TBD.

### Provenance of the models (commits, not releases; full table in `Testing/notes/MODEL_PROVENANCE.md`)
| model | commit | release |
|---|---|---|
| Sail RISC-V (B1, trusted) | `opencompl/sail-riscv-lean` @ `51c635c` (generator Sail `8eb1fb6b`, sail-riscv `b7d1357`; reproduced byte for byte) | no tag (daily bot output) |
| Sail RISC-V (regenerated, part B) | Sail `97aa617dc` (sail2 branch) + sail-riscv `b7d1357` + lean-sail `v10` = `e4745c8`; `Riscv/gen/PROVENANCE.md` | Sail not a tagged release (newest tag 0.20.3 predates Lean 4.34) |
| Sail ARM (part A) | `rems-project/sail-arm` @ `5416ef6`, generator `rems-project/sail` @ `ef5dca5` + patch 0001 + `Reduce__1` flag; `Arm/model` hash `8f79d6b2...`, partition `a4b93808...` | no |
| DeepMind arm64 | `google-deepmind/code-verification` @ `b0f729a` (hash `82094c4a...`) | no |

### Configuration caveats
- The Sail ARM theorem is for a configured machine: `armSail.configured s` = `ArmFullB s n` for some `n` with a `_PC`; MMU off,
  EL3, no permissions (`a64Sail : A64Sem armSail TT TT`); RAM `[2^31, 3*2^30)`; addresses satisfy `VaOK`
  (below 2^48, not the GIC/UART 64 KiB pages). `armSail` is not in `Spec/` (owner decision, `Arm/sail/NOTES.md`).
- The DeepMind theorem holds for start states meeting `ArmLoader X W`; `perm_init` is not provable on DeepMind's model.
- `Arm/sail` needs the partitioned model at a fixed relative path, built by `Arm/gen/partition.py` + `build_part.sh`
  (about 2 h on a 15 GB box). Do not run `lake update` there.
- The regenerated RISC-V model is not the trusted model of B1; the 4.29 model stays on `main` until part B is merged.
- The REVIEW axiom lists (`review_axioms.txt`) include the RISC-V model's opaque platform/float declarations (B1: pinned); the list on the regenerated model: TBD.
- Unproven glue as before: shims, `nanorun`, `rv2arm.sh`, the QEMU runs.

### Release check
`Testing/scripts/release_check.sh` runs every gate (toolchain files, `Spec/` hash, forbidden words including `admit`, `lake build`,
REVIEW axioms, ArmDMTop, ArmSail, model hashes, fixpoint B2 -> B3 and B1 -> B2 -> B3, examples, `cross_check.sh`) and prints a
PASS/FAIL/SKIP table; a SKIP is not a pass. Result on the release tree: TBD.
