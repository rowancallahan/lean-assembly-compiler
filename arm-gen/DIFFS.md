# Diffs from upstream for the ARM Lean model

| Component | Upstream pin | Diff |
|---|---|---|
| ARM Sail sources (`rems-project/sail-arm`, `arm-v9.4-a`) | `5416ef6` (2026-11-09) | none |
| Generator (`rems-project/sail`, Lean backend) | `ef5dca5` (2026-11-12) | none (`patches/sail/` is empty) |
| Sail Lean support library (`rems-project/lean-sail`) | tag `v10` (`e234ce9`) | none |
| Hand-written Lean (`arm-v9.4-a/lean/ArmExtras.lean`, part of sail-arm) | as pinned | none |

Generated output: 593,455 lines, Lean 4.34.1. Generation time 23.5 min.

## Things to read yourself (trusted, hand-written, upstream)
- `ArmExtras.lean` (about 20 lines): defines `putchar`, `sleep_request`, `wakeup_request`, `dec_str`, `hex_str`,
  and a `decreasing_trivial` extension that falls back to `sorry`. Any termination proof closed by that fallback
  makes the definition depend on `sorryAx`. Count pending the build.

## Not yet verified
- Byte-identical regeneration (rule 1): needs a second run of `regen.sh`.
- Clean Lean build, `sorry`/axiom census (rule 2).
