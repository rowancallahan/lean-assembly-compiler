# Code size and organization check (2026-11-20; report only, nothing refactored)

**Sources.**
* Line counts: `main` @ `d4faa8e3` (`git ls-files … | xargs cat | wc -l`; blank and comment lines included).
* Dead code: `Testing/scripts/deadcode.sh` on `nano-v2-src` @ `76f26ed8`. Its `Nano/V2Self` equals `main`'s up to the
  bigbox kit.
* Module reachability: an import-graph walk (each `import` line of every tracked `.lean`) from the top theorems. Roots:
  `Nano.V2Self.REVIEW`, `Main.ArmTop`, `Blocks.ArmDMTop`/`AxiomsDM`, `Apc.Axioms`, `Arm.Axioms`, the `Arm/apc` bridges,
  `Blocks.BlockOK`.

## 1. Lines per area

| area | files | lines | reached from a top theorem (files / lines) |
|---|---:|---:|---|
| **compiler C** `Nano/V2Self/C` + `Prelude` | 6 | 2,523 | 5 / 2,508 |
| proof `Lex` | 4 | 943 | all |
| proof `Parser` | 88 | 21,476 | all |
| proof `Own` | 35 | 5,067 | all |
| proof `Gen` | 7 | 4,467 | all |
| proof `Machine` (incl. the ARM adapter `Arm*`, `A64Sem`) | 81 | 19,333 | all |
| proof `Bridge` | 44 | 9,714 | all |
| proof `Main` | 10 | 935 | all |
| proof `Tests` | 9 | 1,031 | 2 / 208 (the others are the owner's non-vacuity tests, kept by rule) |
| proof `Cert` (**generated**) | 50 | 5,569 | all |
| proof `SrcLink` (mostly **generated**) | 65 | 5,659 | all |
| proof `CertArm` | 9 | 1,655 | 1 / 201 (`Src` only) |
| `Nano/V2Self/Legacy` (old chain, scripts only) | 14 | 1,439 | 0 |
| **ARM, Sail side** `Arm/proofs` | 30 | 7,147 | 18 / 6,173 |
| **ARM, DeepMind side** `Arm/apc` | 44 | 6,505 | 40 / 5,902 |
| `Arm/sail` | — | — | not on `main` yet (branch `sail-a64-wip`) |
| `Arm/CompilerArm.lean`, `Arm/shrink` | 4 | 275 | |
| `Spec/` | 11 | 999 | 9 / 787 |
| `Compiler/` (the earlier compilers' middle layer) | 74 | 21,709 | 41 / 12,967 (used by `Arm/apc`) |
| `Riscv/` (earlier RISC-V back ends) | 200 | 54,132 | 51 / 11,814 via nano; the rest are the earlier compilers' own theorems (`Testing/scripts/expected-axioms.txt`) |
| `Riscv/Legacy` (does not build; not a target) | 7 | 4,466 | 0 |
| earlier nano chain: `Nano/*.lean` top level, `Nano/V2`, `Nano/V2S` | 131 | 28,190 | 7 / 1,754 (`Nano/V2`: `Gen`, `Lang`, `Sem`, `Enc`, `Sim`, …) |
| `Testing/**/*.lean` (test drivers, oracles, scratch) | 375 | 37,275 | 0 (not proof) |
| scripts (`*.sh`, `*.py`, whole repo) | 161 | 12,791 | |
| notes (`*.md`) | 142 | 27,910 | |
| **generated model** `Arm/model` (Sail ARMv9.4-A) | 34 | 591,936 | external (MODEL_PROVENANCE.md) |
| generated model `../deps/sail-riscv-lean` (not in repo) | 160 | — | external |

Hand-written proof that the self-hosted C's theorems need: about 62k lines (`Nano/V2Self/Proof` without `Cert`,
`SrcLink`, `Tests`). The ARM back end adds about 12k (`Arm/proofs` + `Arm/apc` reached).

## 2. Dead code

* **Declaration level** (`deadcode.sh`, `Nano/V2Self` only):
  * With REVIEW's roots (RISC-V): 297 `DECL-DEAD`. 106 of them are `ArmRA`, which only the ARM theorems use.
  * With the ARM top theorems added as roots (`C_correct_rv2arm`, `C_runs_rv2arm`, `C_correct_arm`, `C_correct_on`,
    and their `runs` forms; scratch run, not committed): **203 dead of about 10.5k declarations**, 43,072 constants
    reachable.
  * By folder: Machine 115, Bridge 37, Parser 29, Cert 8 (7 are `Cert.Tac` tactic helpers, a known false positive),
    Gen 6, Own 4, Lex 2, SrcLink 1, Main 1.
  * Largest groups: `Machine.Templates` 25, `Machine.ExprEV` 11, `Machine.Call` 9, `Machine.Loop` 6, `Bridge.MainOk` 6,
    `Machine.StartRun` 5, `Machine.Expr` 5, `Machine.ArmRA` 5.
* **Module level** (nothing on any top theorem's path imports them):
  * `Nano/V2Self/Legacy` (14 files, 1,439 lines);
  * `CertArm` except `Src` (8 files, 1,454);
  * `Arm/proofs`, 12 files, 974 lines: the early experiments `AddExec`/`AddDecode`/`AddWord`; the drafts
    `FullBlrDraft`/`FullCsetDraft`; and the AL forms `FullAluAdd`/`AluLogic`/`AluShift`/`FullMul`/`FullCmp`/`FullSubs`/
    `FullBrLdur`, which only `Arm/sail` uses (not on `main`);
  * `Arm/apc`: `Apc/Opt`, `Apc/Wide`, `Apc/Emit`, `Apc/Emit2` (603 lines; excluded from the lakefile because `WOp.mop`
    has no ARM proof);
  * `Riscv/Legacy` (4,466; does not build);
  * the earlier nano chain except the 7 `Nano/V2` modules above (about 26k lines). These are still tested by scripts,
    but no current theorem needs them.
* Not covered: the tool does not scan `Arm/proofs`, `Arm/apc`, `Compiler/` or `Riscv/` at declaration level (its roots
  and closure are `Nano/V2Self`).

## 3. Consolidation opportunities (ranked by lines saved ÷ risk)

1. **`MainConv` / `MainConvF` / `MainConvX` (Bridge, 22 files, 4,018 lines).** These are three parallel inductions over
   the same AST: the existence contract (`MainConv*`), the failure kinds (`F`) and the capacity half (`X`).
   Same-numbered files are 60–78 % line-identical (`MainConv6`~`X6` 0.78, `7`~`F7` 0.74, `5`~`X5` 0.69). One induction
   generic in the per-node obligation (a record of the three conclusions, or a motive parameter) would remove most of
   two copies. Estimate −2,000 lines.
2. **`EVS*` (safety retrofit, 2,156 lines) versus `EVX*` (the contracts, 1,447 lines)** (Machine). Pairs are 58–67 %
   identical (`EVSTail`~`EVXT` 0.67, `EVSLoop`~`EVXL` 0.66, `EVSComp`~`EVX` 0.58, `EVSCall`~`EVXC` 0.58). EVS restates
   each EVX contract with the safety invariant added. Stating the EVX contracts with safety from the start would drop
   one family. Estimate −1,200 lines. Also `StartRun`~`StartSafe` (0.61) and `CapProg`~`EVSProg` (0.52), the same
   pattern.
3. **The rv2arm block table exists four times:**
   * `Testing/nano/v2self/arm/ArmBlock.lean` (the oracle);
   * `Arm/apc/Blocks/ArmBlockDefs.lean`, a verbatim copy checked by `check_copy.sh`;
   * `Proof/Machine/ArmEnc.lean`, rewritten, with `ArmRA*` proving it equal to the RA model;
   * `rv2arm.lean`/`rv2arm.py`, the translator.

   `ArmEnc` is the proven one. Making `Blocks` use `ArmEnc` (with `ArmBlock` kept only as the test oracle) removes the
   copy and its check script. The table is proven equal once instead of checked by text.
4. **Two ARM routes on DeepMind's model.**
   * The `A64Sem` route (`Blocks.A64DM`/`A64Inst` → `C_correct_rv2arm`) gives the top theorems.
   * The older `BlockOK` route (`Blocks.BlockOK`, `Blocks.Axioms`, `KMem`: 501 lines only it uses) proves `blockOKD`,
     which no top theorem needs. Retire it, or state it as a corollary of `a64DM`.
5. **Two proofs of the earlier `Exp` compiler on two ARM models.** `Arm/proofs` (Sail: `compile_ok`) and `Arm/apc/Apc`
   (DeepMind: `compile_apc`, …; about 3.2k lines used only by `Apc.Axioms`), plus the bridges that relate the models.
   * Once `Arm/sail` lands (`C_correct_armSail` via `A64Sem`), the same generic route serves both models. Per-model code
     then shrinks to the `A64Sem` instance (`A64Inst` for DeepMind, `ArmSail/A64` for Sail) plus per-form step lemmas.
   * The `Apc`-only part (the 3.2k lines above, not on `ArmDMTop`'s path) becomes a candidate for retirement. That is
     an owner decision: it also carries the older compiler's ARM result.
   * Separately, `Apc/Small.lean` is a verbatim copy of `AState`/`armStep`/`emitted` from `Arm/proofs/Arm/{Small,Words}`
     and IS on `ArmDMTop`'s path. Making it an import is blocked only by `Arm/proofs` needing the Sail model.
6. **RISC-V versus ARM adapters are already shared by design.** Both instantiate `JTarget` (`RvTarget` 188 + `SimW`/
   `SimX` 884 against `ArmTarget` 1,138 + `ArmRA*` 1,392). The duplication left is the per-instruction relation
   proofs. Not worth merging further; noted so nobody tries.
7. **Old code still in the tree:**
   * `Nano/V2Self/Legacy` (1.4k), used only by `Testing/nano/v2self` scripts;
   * `Riscv/Legacy` (4.5k; `sorry`, does not build);
   * the earlier nano chain `Nano/*.lean` + `Nano/V2S` + the unused `Nano/V2` files (about 26k);
   * the unused `CertArm` files (1.5k);
   * the dead `Arm/apc/Apc/{Opt,Wide,Emit,Emit2}` (0.6k).

   Moving them to an archive tag (`git tag archive/…`) and deleting them from the tree removes about 34k lines of
   Lean that no theorem needs. The scripts that use them (`Testing/nano/v2self/*` for Legacy) move with them.
8. **The 203 dead declarations** (list: `deadcode.sh` plus the ARM roots). Prune per module, starting with `Templates`
   (25), `ExprEV` (11) and `Call` (9), as in the earlier O-P units (NANO_V2_DEADCODE.md). Low risk, about 2–3k lines.
9. **Tooling:** give `deadcode.lean` the ARM roots (`DEADCODE_ARM=1` importing `Main.ArmTop`) so that `ArmRA` stops
   showing as dead. Extend it to `Arm/proofs` and `Arm/apc`, which are not scanned today.

Not proposed: merging `Cert`/`SrcLink` (generated, about 11k lines; their size follows C's text) or touching `Spec/`.
