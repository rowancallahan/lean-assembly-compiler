# External review: self-hosting trust, optimisation order, second architecture (2026-11-16)

From an external read-only reviewer (owner's request). It could read con-leche's current `MainTheorem.lean` but not our
files, so statements about our code are architectural. Main-session checks are marked **[checked]**.

## Self-hosting trust (the main finding)

- Self-hosting does NOT reduce the trust base to Sail alone. It can remove the Lean executable and the bootstrap compiler
  from the final workflow, but a root proof checker `R` and its logic remain. "con-leche accepts the proof that con-leche
  is sound" is circular (an always-accept binary passes it): useful evidence, not a foundation.
- Three separate properties: compiler correctness (code implements source), checker soundness (accepted ⇒ valid, con-leche's
  `model_exists` relative to its `SetTheory V` interface), bootstrap integrity (this binary = these sources + proofs).
- Chain: fix sources/specs/axioms → produce con-leche binary `B_K` + proof `P_K` (untrusted producer) → a root checker `R`
  checks `P_K` and con-leche's soundness proof → compose ⇒ `B_K` sound → `B_K` checks later certificates (the compiler's,
  new binaries'); replace `B_K` only through the existing trusted chain. DDC and reproducible builds corroborate
  source/binary correspondence; comparing con-leche and Lean verdicts finds bugs; neither proves soundness.
- The final statement must pin down: acceptance as a designated output (OOM / timeout / unsupported input never accept),
  the bytes actually parsed, that the accepted theorem is the intended one about the intended Sail definitions and exact
  binary, the audited axiom set, and the execution assumption (real hardware = Sail model).
- Compiling only `whnf/infer/defeq` covers only those; parser, declaration installation, driver and the accept output
  must be compiled too for an end-to-end claim.
- Defensible claim: "independent of the Lean executable and the bootstrap compiler; machine-code correctness relative to
  the pinned Sail semantics; an explicitly stated logical root and execution assumption."

**[checked] Hidden prerequisite for a complete self-hosted compiler.** Our front ends are Lean metaprograms: 10 files in
`Riscv/Frontx/` are `elab` commands / `MetaM` / tactics (`IndCmd`, `RecCmd`, `WaCmd`, …) that inspect the environment and
build proofs with tactics. The self-hosting probes count only the pure core (`Ir.*`, `Opt.*`, encoders, `Top.compile`).
A compiled compiler that "compiles itself and con-leche" therefore needs (a) an input format: the kernel terms of the
program (e.g. a lean4export-style dump) and (b) proof production as a PURE function: code + a certificate term, checked by
the compiled con-leche (certificate-checked compilation), not tactics. That is a large, separate design task.

## Optimisations by speed per proof effort (reviewer's ranking)

1. register allocation / spill reduction (untrusted heuristic + existing validator; first check whether the front end
   forces locals into memory cells), 2. inlining small hot helpers (untrusted choice, proved substitution), 3. constant
   folding / branch simplification / dead code, 4. register-only peepholes, 5. self tail calls → loops, 6. unboxed scalars,
   7. in-place arrays (needs a proved ownership discipline; large gains on copy-heavy code). First sequence: spills →
   inlining → cleanup, measured together. Resource-changing passes need a resource theorem (peak may only decrease).

## Second architecture (ARM)

Each target proves its emitted bytes implement the shared low-level IR under a state relation: configuration, state
relation, scalar ops, memory ops, control flow, calls/returns (clobbers, saved registers, link register, stack
alignment), byte encoding reaching the bytes Sail fetches, allocation/OOM exit, platform boundary (ISA vs OS exit), and
composition. Acceptance test: ARM instantiates the shared whole-program theorem without changing front-end or generic
optimisation proofs. ARM specifics: flags, SP vs zero register, link register, immediate ranges.
