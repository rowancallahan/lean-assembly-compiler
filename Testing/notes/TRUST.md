# What the proofs rest on (read before citing a theorem)

Every correctness theorem here says: the compiled code computes the source function **on a given machine model**.
The theorem is only as good as that model and the tool that turned it into Lean. Owner's position (2026-11-20): we use
these models because they are far closer to the real ISA, and far better for bug prevention, than trusting an
unverified C compiler — but their details are not guaranteed and should be taken with care.

| target | model | how it becomes Lean | caveats |
|---|---|---|---|
| RISC-V | official Sail RISC-V (sail-riscv) | Sail's Lean backend | backend marked **HIGHLY EXPERIMENTAL** by Sail (0.19/0.20); not a tagged release (commits in MODEL_PROVENANCE.md) |
| ARM (Sail) | official Arm-derived Sail ARMv9.4-A (sail-arm) | Sail's Lean backend + patch + partition | same experimental backend; hand-pinned EL3/MMU-off configuration (not reset-reached); sp not claimed (temporary exception) |
| ARM (DeepMind) | DeepMind arm64 Lean model | written in Lean by its authors | third-party model, not Arm's; coverage of what we use only |
| x86-64 (planned) | Sail x86 translated from ACL2 x86isa | ACL2 → Sail translator → Sail Lean backend | community/translated, two generation steps, possibly incomplete or out of sync with current Sail |

Mitigations: the compiler only uses a few dozen basic instructions (moves, ALU, shifts, multiply, compare/branch,
loads/stores, call/return), where these models are most likely right; every model is fuzzed against QEMU on
real binaries; RISC-V and ARM are proved on independent models where possible (Sail ARM and DeepMind ARM);
exact sources, commits, generator versions and patches are recorded in MODEL_PROVENANCE.md and regenerated, not hand-edited.
Unusual behaviour in rare instructions, system state, or encodings we do not emit is outside what we rely on — and
outside what we checked.
