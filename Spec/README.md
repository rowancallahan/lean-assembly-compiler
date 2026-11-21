# Spec

What the theorems state: byte encodings, source-program meaning (`Program`, `Computes`), machines (`Machine`, `Runs`,
`StartCorrect`) and the top statements `CompileCorrect` / `CompileRuns` (`Spec/Alloc.lean`). Owner-reviewed and frozen:
`Spec/FROZEN.sha256` (checked by `Testing/scripts/spec_check.sh`). Do not edit.

Machines: `riscv` (`RiscvMachine.lean`, built by the root project); `armSail` (`ARM/Sail.lean`, built by `Arm/sail`)
and `armDM` (`ARM/DeepMind.lean`, built by `Arm/apc`), which import ARM models the root project does not have.
`Loader.lean`: `CompileCorrectLoaded` / `CompileRunsLoaded`, the statements for `armDM` (loader premise on page
permissions).
