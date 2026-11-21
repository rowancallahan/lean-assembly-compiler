# lean-assembly-compiler

> **Trust note:** the theorems are relative to machine models (Sail RISC-V, Sail ARM, DeepMind ARM) turned into Lean by tools that are partly experimental. See [Testing/notes/TRUST.md](Testing/notes/TRUST.md) before citing a result.

A compiler from small pure Lean programs (bytes in, bytes out) to RISC-V and AArch64 machine code, with
kernel-checked proofs in Lean 4 that the machine code computes the Lean function on the Sail-generated
CPU models. No `sorry`, no extra axioms beyond the models' own, no `native_decide`/`bv_decide`.

| Folder | Contents |
|---|---|
| `Spec/` | what is proved: byte encodings, machines, `CompileCorrect` / `CompileRuns` (frozen: `Spec/FROZEN.sha256`) |
| `Nano/` | **the compiler**: the self-hosted nano compiler C and its proofs (`Nano/V2Self`, start at `Nano/Main/REVIEW.lean`), and the support it builds on (`Nano/Base`: memory/Hoare logic, RISC-V step lemmas, the nano language) |
| `Arm/` | AArch64: the Sail ARM v9.4-A model (`model/`, `gen/`), Sail proofs (`proofs/`, `sail/`), DeepMind-model proofs (`apc/`) |
| `Legacy/` | earlier compilers and chains, kept for reference only: NOT built (old `Compiler/`, `Riscv/`, `Nano/` layout) |
| `Testing/` | check scripts (`scripts/`: `release_check.sh`, `review_axioms.sh`, `bigbox/`), the self-compile fixpoint and examples (`nano/v2self/`), notes |

Build and check (Lean 4.34.1; RISC-V model at `../deps/sail-riscv-lean`, see `Testing/notes/MODEL_PROVENANCE.md`):

```
lake build                         # Spec, Nano (Base + stage folders), Arm.CompilerArm
Testing/scripts/review_axioms.sh   # the final theorems' axioms against the pinned list
Testing/scripts/release_check.sh   # every gate: build, axioms, ARM (DeepMind, Sail), model hashes, fixpoint, cross check
```

The sections below describe the earlier compilers (now under `Legacy/`; module names gained the `Legacy.` prefix).

Proved on RISC-V: expressions (`compile_ok`), loops (`compileS_ok`, `gcd_ok`), byte arrays and memory
(`compileStore_ok`, `compileAF_ok`), sorting equal to `List.mergeSort` (`sortCode_implements`,
`msortCode_implements`), and the list front end (`compileP_ok`, `compile%`), also through the middle layer
(`compAF_ok`). On ARM: expressions at the decode+execute layer; the full step is in progress.

For agents: `Testing/notes/AGENT_OVERVIEW.md` (rules, where things live), `Testing/notes/SESSION_SUMMARY.md`
(log), `Testing/notes/DETAILS.md` (full proved / tested / not-proved list), `Testing/notes/ROADMAP.md`.
