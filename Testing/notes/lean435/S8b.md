# SURVEY-S8b: `Arm/apc` on Lean 4.35.0

Toolchain: `lean-4.35.0-linux` (commit eb6cafb7), GitHub release asset. Source: `nano-v2-src` at the commit this
note is added to. Dependency: `google-deepmind/code-verification` at `b0f729a`, sparse checkout as in
`Arm/apc/README.md`. Scratch copy only; nothing but this file changed. 4 cores, 15 GB.
Not built: the Sail ARM model and anything needing it.

## Headline

**No 4.35.0-specific failure was found in `Arm/apc`.** Every module that fails on 4.35.0 fails for a reason that
predates it:

1. `Arm/apc` no longer builds at this branch head on *any* toolchain: `lakefile.toml`, `stage.sh` and `Apc/Wide.lean`
   are stale against `Compiler/` (the `MOp` operations and three new `Compiler.Opt` modules).
2. `Compiler/Opt/Flow.lean` has 5 errors on 4.35.0; the same 5 errors (same lines) occur on 4.34.1. It is a 4.29 -> 4.34
   change, newly visible here only because `Flow` was not in the apc import closure before.

With scratch-only repairs for those (listed below), all 35 `Apc` modules except `Apc.Emit2` compile on 4.35.0, and
`Emit2` fails only because of the `sorry` stub I put in `Apc/Wide.lean`.

## DeepMind `arm64` package

| target | result | wall | note |
|---|---|---|---|
| `arm64` (`lake build`, 192 jobs, incl. C compile and `libarm64_Arm64_Trusted.so`) | **OK**, 0 warnings | 53 s | largest single process 871 MB RSS |

Their lakefile sets `warningAsError = true`, so zero warnings is a real result: nothing of theirs is deprecated on
4.35.0. Nothing of theirs edited. (They have no `lean-toolchain` file in the sparse checkout; lake of 4.35.0 was called
directly.)

## Our middle layer as seen from `Arm/apc` (`Spec.*`, `Compiler.*`, 39 jobs)

| module(s) | result | category |
|---|---|---|
| `Spec.{Code,ArrCode,Encode,Tree}` | OK | - |
| `Compiler.{Iface,Logic,Exp,Stmt,Mem,Arr,BLang,CLang,Frame,BExp,BStmt,Call,CStmt,CProg,Wide,MOp}` | OK | - |
| `Compiler.Opt.{IR,Alloc,Live,SR,Color,Fn,Sel,Exp,Stmt,Arr,BSel,BFn,Lower,Hoist,Peep}` | OK (deprecation warnings) | deprecated name |
| `Compiler.Opt.Flow` | **error** (5), also on 4.34.1 | simp lemma changed / elaboration (see below) |

All of these are small (each under 6 s; whole set well under a minute).

### `Compiler.Opt.Flow` (not a 4.35.0 regression)

First error: `Compiler/Opt/Flow.lean:266:8: Type mismatch: After simplification, term ht has type decide (s.reg a' = 0#64) = true but is expected to have type s.reg a' = 0#64`.
Others: 373:49, 494:88 (unsolved goals), 516:25, 525:29 (type mismatch).

Cause (checked with `pp.explicit`): after `simp [Tst.eval, Cond.eval, Arg.eval]` the proposition is simplified but the
`Decidable` instance argument still mentions the unsimplified terms (e.g. `instDecidableEqBool (Cond.lt.eval a b) true`,
`instDecidableEqBitVec (Arg.eval s (Tst.a ..)) ..`). `decide_eq_true_eq` / `decide_eq_false_iff_not` / closing by `rfl`
then fail at reducible transparency.

Fixes tried on a 4-line reproduction, all work on 4.35.0:
- `set_option backward.isDefEq.respectTransparency false` (file-wide: `Flow` then compiles with no other change);
- per site: `show (!decide (s k = 0)) = true ↔ _; simp`, or append `exact decide_eq_false_iff_not` / `rfl` after the `simp`.
`dsimp only [...]` first does **not** help.

This is the same family as the "Lean 4.34 simp normal form" one-line edits already recorded in `stage.sh`. Expect more of
it in the parts of `Compiler/` and `Riscv/` that have only ever been built on 4.29.0; the file-wide option is a cheap
first pass.

## `Apc` modules (35, including the 15 staged into `Apc/Src`)

Wall time is lake's per-module time during a 4-job build; RSS from a separate single-file run.

| module | lines | result on 4.35.0 | category | wall | peak RSS |
|---|---|---|---|---|---|
| `Apc.Small` | 57 | OK | - | 0.9 s | |
| `Apc.Flags` | 61 | OK | - | 1.5 s | |
| `Apc.Sym` | 167 | OK | - | 6.7 s | |
| `Apc.Mach` | 774 | OK (warnings) | deprecated name, unused simp arg | 24 s (16 s alone) | 1.9 GB |
| `Apc.Mem8` | 188 | OK (warnings) | unused simp arg | 3.8 s | |
| `Apc.Frame` | 365 | OK (warning) | - | 14 s | |
| `Apc.Stack` | 98 | OK | - | 2.6 s | |
| `Apc.Agree` | 60 | OK | - | 14 s | |
| `Apc.AgreeAll` | 12 | OK | - | 222 s (191 s alone) | 2.2 GB |
| `Apc.WideDec` | 71 | OK | - | 256 s (232 s alone) | 5.0 GB |
| `Apc.Msort` | 105 | OK | - | 9.6 s | |
| `Apc.Call` | 197 | OK (warnings) | unused simp arg | 5.7 s | |
| `Apc.Calls` | 177 | OK (warning) | deprecated name | 4.3 s | |
| `Apc.Emit` | 7 | OK | - | 1.0 s | |
| `Apc.Src.*` (15 staged files, 2819 lines) | - | OK after the stale-`stage.sh` repair; about 300 deprecation warnings | deprecated name | each under 10 s | |
| `Apc.Wide` | 295 | **error**, pre-existing | other (stale against `Compiler.Wide`) | 2 s | |
| `Apc.Src.Search`, `Apc.Opt`, `Apc.Axioms` | 288 (Opt) | OK **only with `Apc.Wide` stubbed by `sorry`** | - | 1-2 s each | |
| `Apc.Emit2` | 13 | error, artefact of my stub (`#eval` refuses `sorry`) | - | | |

The `decide +kernel` enumeration in `WideDec` and the 216-word `AgreeAll` are the only heavy modules and both pass
unchanged. The README's "≈ 5 min" for `WideDec` is consistent with 4.35.0 (no slowdown seen; no 4.34.1 timing taken on
this box).

### Pre-existing breakage (independent of the toolchain), with the scratch repair used

| what | first error | scratch repair |
|---|---|---|
| `lakefile.toml` globs miss `Compiler.MOp` | `Compiler/BLang.lean:10:0: object file .../Compiler/MOp.olean of module Compiler.MOp does not exist` | add `Compiler.MOp` |
| globs miss `Compiler.Opt.{Flow,Hoist,Peep}` | `Compiler/Opt/Fn.lean:4:0: object file .../Compiler/Opt/Flow.olean ... does not exist` | add the three |
| `stage.sh`: staged `Apc/Src/Arr2Code.lean` lacks an import | `Apc/Src/Arr2Code.lean:52:13: Unknown identifier Mach.MOp` | prepend `import Compiler.MOp` |
| `Apc/Wide.lean`: `WOp.mop` and law `w_mop` do not exist on the ARM side | `Apc/Wide.lean:33:2: Missing cases: (WOp.mop MOp.mul ...)` (5 cases), `Apc/Wide.lean:251:26: Fields missing: w_mop` | stub: `.mop => []`, `w_mop := sorry` (survey only) |

The last one is real work: encode and prove `mul`/`udiv`/`sdiv` and the two remainders (`msub`) on DeepMind's semantics
for arbitrary registers, in the style of the existing `w_bin`.

### Warnings (not errors here; `Arm/apc` does not set `warningAsError`)

About 300 deprecations in one full build, nearly all in files staged from `Riscv/`: `if_pos` -> `ite_eq_left`,
`if_neg` -> `ite_eq_right`, `dif_pos` -> `dite_eq_left`, plus `X` -> `ite_true` / `ite_false` (old name not recorded). 42 "unused simp argument", 8 unused variables.

## Needs the Sail ARM model (not built)

`Bridge.lean`, `BridgeBr.lean`, `BridgeRun.lean`, `BridgeMem.lean`, and the `Br/Agree`, `Br/AgreeAll` variants that
`check.sh` generates (they import `Arm/proofs` oleans and `/home/user/armv9-lean`). 826 lines.

## Effort estimate (prover-hours)

| item | caused by 4.35.0? | estimate |
|---|---|---|
| DeepMind `arm64` | - | 0 |
| `Apc.*` proofs as they stand | no errors | 0 |
| lakefile globs, `stage.sh` import | no | 0.25 |
| `Compiler.Opt.Flow` (5 sites, fix known) | no (4.34) | 0.25 with the option, about 0.5 per-site |
| `Apc.Wide`: `mop` encodings + `w_mop` | no | 3-6 (not attempted; a guess from the size of `w_bin`) |
| deprecation renames (optional) | yes, warnings only | 0.5, mechanical |
| bridge files | unknown | not assessed here |

So the 4.35.0 bump itself costs about **0 prover-hours** for `Arm/apc` excluding the bridge; getting `Arm/apc` green
again at this branch head costs roughly 4-7, on any toolchain.

## Not done

- No 4.34.1 build of `Apc` for a like-for-like timing (only `Compiler.Opt.Flow` and its 13 imports were built on 4.34.1).
- `Apc.Opt`, `Apc.Src.Search`, `Apc.Axioms` were only checked downstream of a `sorry`-stubbed `Apc.Wide`.
- `check.sh` itself was not run (it hard-codes the 4.34.1 elan path and the Sail side).
