# Spec/ARM

The ARM machines the ARM theorems are stated against. They import ARM models the root project does not have, so the
root `lakefile.toml` leaves `Spec.ARM.*` out; each file is built by its ARM sub-project.

| file | defines | used by | build |
|---|---|---|---|
| `Sail.lean` | `armSail`: one Sail `step_model` of the official Sail ARMv9.4-A model; observes pc, x0–x30 (31 reads 0), Sail's memory map; `configured` = the pinned EL3 / MMU-off registers (`ArmSailPins`, copied from `Arm/gen/pins.py`'s output) plus the bookkeeping a step reads | `ArmSail.C_correct_armSail` / `C_runs_armSail` (`CompileCorrect` / `CompileRuns`, `Arm/sail/ArmSail/Top.lean`) | `cd Arm/sail && lake build ArmSail ArmSail.Axioms` (needs `/home/user/armv9-lean`, `Arm/gen/build_part.sh`) |
| `DeepMind.lean` | `armDM`: DeepMind's `Arm64` fetch/decode/execute while running; observes pc, x0–x30, sp as 31, mapped bytes; `ArmDMExecutable` / `ArmDMWritable` page permissions | `Proven.Apc.Blocks.C_correct_armDM` / `C_runs_armDM` (`CompileCorrectLoaded` / `CompileRunsLoaded` of `Spec/Loader.lean`, `Arm/apc/Blocks/ArmDMTop.lean`) | `cd Arm/apc && lake build Blocks.ArmDMTop Blocks.AxiomsDM` (needs `/home/user/deps/code-verification` @ b0f729a) |

How these are tied to the proof-side machines (`ArmSail.armSail` in `Arm/sail/ArmSail/Machine.lean`,
`Proven.Apc.Blocks.armDM` in `Arm/apc/Blocks/ArmDM.lean`): the proofs are done on those, and the top theorems are moved
to the Spec machines by kernel-checked equalities in the two `Top` files. `step` (and for DeepMind `configured`, the
RAM window and the permissions) agree by `rfl`; `observe` agrees pointwise (`obs_spec`, by cases); Sail's `configured`
agrees as an `Iff` (`conf_spec`, field by field, through `propext`). So an edit on either side that changes the
meaning fails the ARM builds. Both checks print only `propext, Classical.choice, Quot.sound`.
