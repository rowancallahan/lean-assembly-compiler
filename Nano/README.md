# Nano

The self-hosted nano compiler and everything it is built and proved on. Lean 4.34.1.

* `V2Self/`: **the compiler C** (`C/`), its correctness proofs (`Proof/`), and `REVIEW.lean` (the final theorems and
  everything to trust; start there). See `V2Self/README.md`.
* `Base/`: support modules that V2Self (or the ARM proofs) import, moved here from the old top-level `Compiler/`,
  `Riscv/` and `Nano/V2/` (module = path, e.g. `Nano.Base.Riscv.Steps.Step`; theorem and namespace names unchanged):
  `Base/Compiler` (machine interface, memory/Hoare logic, Opt), `Base/Riscv` (RISC-V step lemmas and the direct /
  back-end facts used), `Base/V2` (the nano V2 language, semantics, encoder, simulator).
