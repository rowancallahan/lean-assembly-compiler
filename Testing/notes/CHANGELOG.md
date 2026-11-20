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
