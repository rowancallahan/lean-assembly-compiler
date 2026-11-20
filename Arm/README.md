# Arm

AArch64 for the nano compiler (C → RISC-V words → `rv2arm`) and for the earlier `Exp` compiler. Lean 4.34.1.

* `model/`: the Sail ARM v9.4-A model (generated; regenerate with `gen/regen.sh`, provenance in
  `Testing/notes/MODEL_PROVENANCE.md` §2). Built outside the repo (partitioned) for the proofs.
* `proofs/`: per-instruction step lemmas on the Sail model (`check.sh`).
* `sail/`: `C_correct_armSail` / `C_runs_armSail` on the Sail model.
* `apc/`: DeepMind's AArch64 model: `C_correct_armDM` / `C_runs_armDM` (`Blocks/`), the `Exp` compiler (`Apc/`), bridges.
* `CompilerArm.lean`: the AArch64 code generator of the earlier `Exp` compiler.
