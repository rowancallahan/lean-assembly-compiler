# Nano

The self-hosted nano compiler C and everything it is built and proved on (Lean 4.34.1). One folder per compiler stage, code and proof together; start at `Main/REVIEW.lean`.

| folder | stage / role |
|---|---|
| `Lexer/` | bytes → tokens (`s10`), spec and soundness |
| `Parser/` | tokens → AST (`y16`), grammar `ParSpec` and refinement proof |
| `Ownership/` | linearity check (`o41`), `OwnSpec`, `own_stage` |
| `Codegen/` | AST → machine bytes (`g41`), soundness on success |
| `Run/` | Gen's code on the abstract machine J; RISC-V / ARM adapters; capacity and work bound |
| `SelfHost/` | generated certificates and source link: C's own text compiled by C; bridge lemmas |
| `Main/` | `Prelude`, driver, top theorems, `REVIEW.lean` |
| `Tests/` | non-vacuity witnesses |
| `Base/` | support: `Compiler` (machine interface, Hoare logic), `Riscv` (step lemmas), `V2` (nano language, semantics, encoder) |

Module = path (`Nano.Parser.ParInv`); def/theorem/namespace names are unchanged by the stage layout (namespaces: `NanoMain`, `ParSpec`, `Templates`, `Cert`, `SrcGen`, …). Index of notes: `Testing/notes/NANO_V2_STATUS.md`. The old `Legacy/Nano/V2Self` chain is not built.
