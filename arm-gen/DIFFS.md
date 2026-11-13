# Diffs from upstream for the ARM Lean model

| Component | Upstream pin | Diff |
|---|---|---|
| ARM Sail sources (`rems-project/sail-arm`, `arm-v9.4-a`) | `5416ef6` (2026-11-09) | none |
| Generator (`rems-project/sail`, Lean backend) | `ef5dca5` (2026-11-12) | `patches/sail/0001-lean-throw-unit-type-and-let-do.patch` (7 lines) |
| Sail Lean support library (`rems-project/lean-sail`) | tag `v10` (`e234ce9`) | none |
| Hand-written Lean (`arm-v9.4-a/lean/ArmExtras.lean`, part of sail-arm) | as pinned | none |

## Patch 0001 (generator only)
Two printing fixes in `src/sail_lean_backend/pretty_print_lean.ml`:
1. A `throw` of type `unit` in monadic position is printed as `(sailThrow (e) : SailM Unit)`.
   Without it Lean cannot infer the result type when both branches of a statement-level `if` throw.
2. `let x <- (( e ) : T)` is printed as `let x <- (( do e ) : T)`, so a nested `(<- ...)` inside a
   term-level `if` has an enclosing `do`.
Neither changes meaning. Without the patch `Instrs32` and `Instrs64` do not compile; all other modules do.

## Build notes
- The generated top-level `Armv9.lean` does not import the instruction, decoder, system-register or fetch
  modules, so `lake build` alone builds only 16 of 34 modules. Build the rest by name (`lake build Armv9.Fetch` etc.).
- `V8Base` needs about 12 GB of memory; `SysregsAutogen` similar.

## Things to read yourself (trusted, hand-written, upstream)
- `ArmExtras.lean` (about 20 lines): defines `putchar`, `sleep_request`, `wakeup_request`, `dec_str`, `hex_str`,
  and a `decreasing_trivial` extension that falls back to `sorry`.

## `sorry` census (so far)
- `Armv9.V8Base`: 1 definition (`Reduce__1`). Other modules: none reported yet; build still in progress.

## Not yet verified
- Byte-identical regeneration (rule 1): needs a second run of `regen.sh` from a clean checkout.
- Complete build of all 34 modules.
