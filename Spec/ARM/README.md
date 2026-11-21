# Spec/ARM

- `Sail.lean` — `armSail`, the official Sail ARMv9.4-A model as a `Machine`.
- `DeepMind.lean` — `armDM`, DeepMind's `Arm64` model as a `Machine`, and its page permissions.
- (`../Loader.lean`, model-free, root-built: `CompileCorrectLoaded` / `CompileRunsLoaded`, the statements with a
  loader premise, used for `armDM`.)

**Role.** The ARM top theorems are stated against these machines, so what they claim is reviewed and frozen here
(`Spec/FROZEN.sha256`), as `riscv` is in `../RiscvMachine.lean`. The code is C → RISC-V → `rv2arm` (TRUST.md).
- `ArmSail.C_correct_armSail` / `C_runs_armSail`: `CompileCorrect` / `CompileRuns armSail …` (`Arm/sail/ArmSail/Top.lean`).
- `Proven.Apc.Blocks.C_correct_armDM` / `C_runs_armDM`: `CompileCorrectLoaded` / `CompileRunsLoaded armDM
  ArmDMExecutable ArmDMWritable …` (`Arm/apc/Blocks/ArmDMTop.lean`).

**Main definitions.**
- `armSail`: step = one Sail `step_model` (`SEE = -1; __TopLevel(); __CycleEnd()`); observes pc, x0–x30 (31 reads 0),
  Sail's memory map; `configured` = `ArmSailConfigured` (the pinned EL3 / MMU-off registers `ArmSailPins`, copied from
  `Arm/gen/pins.py`'s output, plus the branch bookkeeping, cycle counter, x0–x30 and pc present); RAM [2^31, 3·2^30).
- `armDM`: step = fetch/decode/execute while `Running`; observes pc, x0–x30, sp as 31, mapped bytes; `configured` =
  `Running`. `ArmDMExecutable` / `ArmDMWritable`: the permissions the loader premise asks for.

**Design (Testing/notes/SPEC_ARM.md, option A).** These files import the ARM models, which the root project does not
have, so the root `lakefile.toml` leaves `Spec.ARM.*` out and each ARM sub-project builds its file. Rejected: making the
models root dependencies (every root build would need two large out-of-repo builds) and an abstract ARM machine in
Spec (the meaning would stay in the instantiation outside Spec).

**Checked.** Proofs are done on the proof-side machines (`Arm/sail/ArmSail/Machine.lean`, `Arm/apc/Blocks/ArmDM.lean`)
and moved here by kernel-checked equalities in the `Top` files: `step` (and for DeepMind `configured`, RAM window,
permissions) by `rfl`; `observe` pointwise (`obs_spec`); Sail's `configured` as an `Iff` (`conf_spec`, via `propext`).
A change on either side that changes the meaning breaks the ARM build. Axioms: `propext, Classical.choice, Quot.sound`.

**Build.** `cd Arm/sail && lake build ArmSail ArmSail.Axioms` (model at `/home/user/armv9-lean`: `Arm/gen/partition.py`
+ `build_part.sh`); `cd Arm/apc && lake build Blocks.ArmDMTop Blocks.AxiomsDM` (`/home/user/deps/code-verification`
@ b0f729a). `Testing/scripts/spec_check.sh` hashes these files with the rest of `Spec/`.
