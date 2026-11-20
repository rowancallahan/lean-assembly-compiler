# Diffs from upstream for the RISC-V Lean model on Lean 4.34.1

Upstream: `opencompl/sail-riscv-lean` @ `51c635c460125ac87955d061fcd902ce03b8011f` (generated for Lean 4.29.0),
Sail Lean library `rems-project/lean-sail` `v5` @ `0794631` (unchanged).
Patch: `Riscv/gen/patch_434.sh <checkout>` (checks the commit and a clean tree, asserts the site counts).
Nothing is regenerated; the Sail sources and the generator are not involved.

## Changes

1. `lean-toolchain`: `v4.29.0` -> `v4.34.1`.
2. `lakefile.toml`, lib `LeanRV64D`: `leanOptions.backward.do.legacy = true`.
   The option exists on both toolchains. Its default is `true` on 4.29.0 and `false` on 4.34.1
   (`Lean/Elab/Do/Switch.lean`). Setting it selects the same `do` elaborator that produced the 4.29 build.
   It only affects how `do` blocks are elaborated, not what any name means. Same option the ARM model sets
   per file (`Arm/model/Armv9/*.lean`, lean4#13858, #15685). Without it (new elaborator, and the calls
   spelled `PreSail.assert`) an earlier run had 17 type errors (`Mem.lean:287-303`, `BaseInsts.lean:264`);
   with it those sites need no change.
   `cleanup.letToHave` is left at its default (`true` on both toolchains).
3. 1256 call sites `assert p "msg"` -> `LeanRV64D.assert p "msg"` (1255 do-statements at line start, plus
   `then assert` in `Step.lean:449`), 74 files. 4.34 has a do-element `assert P`
   (`Lean.Parser.Term.doAssertion`, `nonReservedSymbol "assert"`, priority default+10), which takes these
   lines before the term parser sees them. Every site is inside `namespace LeanRV64D`, where `assert`
   resolved to `LeanRV64D.assert` (`SpecializationV1.lean:38`, an `abbrev` for `PreSail.assert` at `SailM`).
   Writing the full name gives the same constant. `Sail...PreSail.assert` is a different constant
   (generic monad); spelling the calls that way is what produced the earlier PreSailM type errors.
   Three `"loop dummy assert"` string literals are untouched.

4. 2005 nested actions `(← do S)` -> `(← (do S))`, 43 files (`Riscv/gen/wrap_nested_do.py`: inserts `(` after
   `← ` and `)` before the matching close paren, skipping strings and comments).
   4.34 parses the operand of `←` as a do-element, so `do S` there is the do-element `do`, and the legacy
   elaborator rejects it ("the legacy `do` elaborator only supports a term after `←`",
   `Lean/Elab/Do/Legacy.lean:1354`; 99+ errors in `PlatformConfig.lean` alone). With the parentheses the
   operand is the term `(do S)`; parentheses are not in the elaborated term, so it is the term `do S` was on 4.29.

## Check (constant-by-constant)

See "Mechanical check" below.
