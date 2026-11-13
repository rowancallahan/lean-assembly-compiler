# Diffs from upstream for the ARM Lean model

| Component | Upstream pin | Diff |
|---|---|---|
| ARM Sail sources (`rems-project/sail-arm`, `arm-v9.4-a`) | `5416ef6` (2026-11-09) | none |
| Generator (`rems-project/sail`, Lean backend) | `ef5dca5` (2026-11-12) | `patches/sail/0001-lean-backend-fixes.patch` (one file, about 80 changed lines) |
| Sail Lean support library (`rems-project/lean-sail`) | tag `v10` (`e234ce9`) | none |
| Hand-written Lean (`arm-v9.4-a/lean/ArmExtras.lean`, part of sail-arm) | as pinned | none |

## Patch 0001 (generator only: `src/sail_lean_backend/pretty_print_lean.ml`)
Three printing changes. None touches the ARM Sail sources.
1. A `throw` of type `unit` in monadic position is printed as `(sailThrow (e) : SailM Unit)`.
   Without it Lean cannot infer the result type when both branches of a statement-level `if` throw.
2. `let x <- (( e ) : T)` is printed as `let x <- (( do e ) : T)`, so a nested `(<- ...)` inside a
   term-level `if` has an enclosing `do`.
   Without 1 and 2, `Instrs32` and `Instrs64` do not compile.
3. An if/else chain along the body of a non-pure function is cut every 100 levels: the rest of the chain
   becomes an auxiliary definition `f_tailK` with the same parameters, called in tail position.
   No binder is crossed along the chain, so the tail mentions only the parameters.
   Without it `__DecodeA64_SVE` is a single definition nested about 1,160 deep (37 MB of text) and Lean
   exceeds 27 GB of memory elaborating it. With it `DecodeEnd.lean` shrinks from 71 MB to 12.7 MB.
   **This one changes the shape of the output**: 122 auxiliary definitions appear (`DecodeEnd` 64,
   `SysregsAutogen` 50, `V8Base` 6, `MapClauses` 2). Each is the verbatim tail of the original chain, so the
   original function equals the composition by unfolding. That equality is not yet stated as a Lean theorem.

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
