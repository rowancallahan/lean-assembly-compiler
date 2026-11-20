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
- Lean 4.34.1 (`Arm/apc`: `Blocks.ArmDMTop`, `Blocks.AxiomsDM`, the Parser folder): PENDING.
- Fixpoint (nanorun): B1 → B2 → B3, B3 = B2 = 340,296 B, sha256 24759aa0f757e50e92e67d498a84f28ec7a0b13da6f2c9fc3d76cd0679699ed4.
  ARM: `arm/B2_arm.bin` regenerated (translator run under nanorun; the same procedure reproduces the old B2_arm.bin byte for
  byte). `cross_check.sh` not run: no qemu / aarch64 toolchain on this box (RISC-V checked with nanorun only).
- Per commit (self-compile; flat_320; chain_320): (a) hash table 789,993,519; 163.0 M; 104.0 M. (b) numeral layout
  constants 641,996,759; 134.7 M; 83.8 M.
- Benchmark vs B1 (exact RISC-V instructions, nanorun): self-compile 1,454,349,112 → 641,996,759 (−56%); flat_320
  641.9 M → 134.7 M, chain_320 391.3 M → 83.8 M, now linear (≈0.40 M per flat def, 0.24 M per chain def, K = 10..511);
  examples' compile −2.6% … −6.0% (count +0.03%); emitted code byte-identical on all of them, so run costs are unchanged.
  Details: `Testing/notes/PERF_NAMES.md`.
