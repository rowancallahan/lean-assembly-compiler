# S3: typed source calculus (external review, 2026-11-16) + how it maps onto our code

## Recommendation (reviewer)

- A deeply embedded, typed, first-order calculus: monomorphic algebraic inductives (no function-valued fields), variables,
  `let`, constructors, exhaustive matches, fully applied calls to named functions, a fixed set of primitives. Polymorphism
  is specialised before entry; dependent/indexed types and proofs excluded at first.
- Meaning: `⟦τ⟧ : Type` per type and a compositional `eval_P : Expr Σ Γ τ → Env Γ → ⟦τ⟧`, free of pointers, registers,
  allocation and fuel. Recursion needs a well-foundedness certificate in the program (signature, bodies, call relation,
  WF certificate: structural first, tuple measures and mutual recursion later, without changing the value language).
- Bridge per Lean function: `∀ x, decode (eval_P f_entry (encode x)) = f x`, kernel-checked; the front end that produces
  the program + certificate is untrusted. "Supported" = the front end can produce both.
- One generic theorem: `compile P = B ∧ InitialRep ∧ ResourcesSufficient → ∃ s', SailExec B s s' ∧ FinalRep (eval_P x) s'`,
  with a representation relation `Rep_τ v w h` (value, word/pointer, heap) carrying ownership/framing.

## Checked against our code (main session)

This is already the shape of the inductive path, so S3 generalises it rather than starting over:
- `Riscv/Frontx/IndMem.lean`: `IndProg` (shapes `sh`, functions `pg :: hs`, input/output format) is a deeply embedded
  program; `IndProg.run` gives its meaning through `Pg.sem`; `compile : IndProg → Option CompiledA` is proved ONCE
  (`CompileCorrect riscv compile`, `CompileRuns riscv compile`); `frontx_ind` produces the program plus the per-function
  bridge (`Implements1`).
- S3 = one calculus covering all features (lists, word/paged arrays, inductives, structures, specialised monads and
  higher-order arguments) lowered to the shared IR (`Compiler/Ir/*`, proved once in `Riscv/Back/IrTop.lean`), with the
  front end as a pure function from exported kernel terms (ROADMAP "Front-end input") producing program + bridge.
- The reviewer's note on execution quantifiers: our `Runs` is over the deterministic Sail step, so one run suffices.
