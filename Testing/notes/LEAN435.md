# Does nano's main build on Lean 4.35.0-rc3? (S5 measurement, branch `keep_round1_lean435` off `keep_round1_armfix` a15cdd0)

Setup: `lean-toolchain` = `leanprover/lean4:v4.35.0-rc3`; RISC-V model = orphan branch `deps-rv-regen434` @ 4cf120c checked out at
`../deps/sail-riscv-lean` (as MODEL_PROVENANCE.md §4; it pulls lean-sail `v10` through lake); `lake build Nano.Expr.RvExpr`. Log: 765 jobs.

**Result: does NOT build. One root cause, in the Sail RISC-V model, not in nano.**
* 764 of 765 jobs OK, including every nano module that does not import the model (all of Nano.Lexer/Parser/Ownership/Codegen/Run/SelfHost/Base up to
  the model-importing ones; `Nano.Expr.SelfSrc` built, 138 s). 0 errors in nano's own files. The only failing job is `LeanRV64D.Defs`; everything that
  imports it (including `Nano.Expr.RvExpr`) is therefore not built.
* Errors (102, from one declaration, `LeanRV64D/Defs.lean:759`, `inductive instruction`; maxErrors 100 cut the list):
  | kind | count | message |
  |---|---|---|
  | model breakage (the cause) | 1 | `tag for constructor 'LeanRV64D.instruction.VIMCTYPE' is too big, this is a limitation of the current runtime` |
  | consequences | 2 | ``LeanRV64D.instruction` was not compiled; `compileDecls` must run on inductive types first`` |
  | consequences | 97 | `failed to compile definition, consider marking it as 'noncomputable' because it depends on 'instruction.ctorElim' / 'instruction.<ctor>', which is 'noncomputable'` |
  | meta | 1 | `maximum number of errors (100) reached` |
* `instruction` has about 350 constructors (hand count of the `| ` lines, approximate). 4.35.0-rc3's compiler refuses the constructor tag for it (4.34.1 accepts).
  So the Sail model needs a change (regenerate with fewer constructors per inductive / split the type, or mark the inductive and its dependents
  noncomputable via a patch, or ask lean4 / lean-sail whether the tag limit is a regression in rc3) before the RISC-V theorem and con-leche's can share
  one toolchain. Not attempted ("don't fix big things").
* Warnings only (no errors) in nano's modules: about 7300 warning lines, mostly unusedVariables hints (about 600) and `deprecated` (7280 mentions; e.g.
  Nano/Run/NdCG.lean:265, Nano/Ownership/OwnP14.lean:137, Nano/Parser/NumP27.lean:645/647: `X has been deprecated: Use Y instead`, the
  `if_pos/if_neg/...` renames already seen in DENOTES_SPIKE §5 H2). No renamed-lemma errors appeared in nano.
* Not measured: `ArmSail.ExprSail` (Arm/sail); the root (the model it needs) was not reached, and the 4.35 Arm model was not built. Also not measured:
  whether the model's own non-`instruction` parts compile (lake stopped at `Defs`).
