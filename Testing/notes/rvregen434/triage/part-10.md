# Triage part 10 (final_classes.tsv lines 208-222)

Read-only analysis. No build or proof run. Uses found with
`git grep -nw NAME -- Riscv Nano Compiler Spec ':!Riscv/gen' ':!*LeanRV64D*'`.
`Riscv/gen` holds only PROVENANCE.md and regen434 on this branch, so the generated model is not in the tree. Old/new shapes come from `model.diff.gz`.

| name | class | #uses | verdict | fix |
|---|---|---|---|---|
| valid_wide_vxtype | shortcircuit | 0 | UNUSED (direct) | - |
| valid_widening_fp_conversion | shortcircuit | 0 | UNUSED (direct) | - |
| virtual_memory_supported | shortcircuit | 0 | UNUSED (direct) | - |
| vmem_read_addr | unit_stmt_ascription | 0 | UNUSED (direct) | - |
| vmem_write_addr | unit_stmt_ascription | 0 | UNUSED (direct) | - |
| wF | unit_stmt_ascription | 0 | UNUSED | - |
| wV | unit_stmt_ascription | 0 model uses (the `wV` hits are an unrelated Nano theorem) | UNUSED | - |
| wX | unit_stmt_ascription | 1 (`sail_eval` unfold list) | LIKELY-OK | none expected; see wX |
| within_mmio_readable | shortcircuit | 0 | UNUSED (direct) | - |
| within_mmio_writable | shortcircuit | 0 | UNUSED (direct) | - |
| write_CSR | match_to_if | 1 (`rfl` bridge, `wr_misa`) | NEEDS-FIX (check) | see write_CSR |
| write_vxsat | unit_stmt_ascription | 0 | UNUSED | - |
| zicfilp_preserve_elp_on_trap | unit_stmt_ascription | 0 | UNUSED (direct) | - |
| zicfiss_xSSE | shortcircuit | 0 | UNUSED (direct) | - |
| zvk_check_encdec | shortcircuit | 0 | UNUSED | - |

"UNUSED (direct)": no proof names it, but `sail_eval` can unfold it through a caller. Risk is the shared shortcircuit item below, not per-definition work.

## What changed
- shortcircuit (`valid_wide_vxtype`, `valid_widening_fp_conversion`, `virtual_memory_supported`, `within_mmio_*`, `zicfiss_xSSE`, `zvk_check_encdec`): `pure ((← a) && (← b))` becomes `a <&&> (do b)` (`<||>` for `||`). Example: `virtual_memory_supported` is now `(currentlyEnabled Ext_Sv32) <||> (do (currentlyEnabled Ext_Sv39) <||> (do ...))`. `b` runs only if `a` does not decide the result. Since `currentlyEnabled` only reads registers, the result is the same.
- unit_stmt_ascription (`vmem_*_addr`, `wF`, `wV`, `wX`, `write_vxsat`, `zicfilp_preserve_elp_on_trap`): the body (or the `match`) gets wrapped as `let _ ← (( do ... ) : SailM Unit)`. `wF` and `wX` also change `assert` to `sail_assert`. `wX`/`wF`/`wV` keep the 32-way `match r with | 0 => ...` inside the wrapper. `write_vxsat` wraps its `if`.
- match_to_if (`write_CSR`): the huge `match b__0 with | 0x301 => ...` becomes `if b__0 == 0x301#12 then ... else (if (b__0 == 0x300#12 && xlen == 64) then ...)`. The branch bodies are the same (checked for 0x301 only).

## Uses
- `wX`: `Riscv/Steps/GenRegs.lean:111` is `sail_eval [wX_bits, wX]` inside `wX_bits_ok`, after a 32-way `rcases` on `i`. It unfolds `wX`, so the `let _ ← (do match r ...)` wrapper is evaluated. `sail_eval` handles `Bind.bind` on `EStateM` (SailEval.lean:282), so the extra bind with a unit binder should reduce. After it, `r` is a literal, so the `match` reduces. Verdict LIKELY-OK. If it fails, the fallback is to add `bind_pure_comp`-style lemmas for the wrapper (the extra bind returns `PUnit`).
- `wX_bits` is also frozen or unfolded in `GenMem.lean:126`, `GenTac.lean:268`, `GenRegs.lean:1,3`. These are mentions of `wX_bits`, not `wX`, so they depend on `wX_bits_ok` still holding. Not in my slice.
- `write_CSR`: `Riscv/Back/BootV.lean:73` is `theorem wr_misa ... : write_CSR 0x301#12 v = (do ...) := by rfl`, used in the `v_eval` macro's simp set (line ~86). New `write_CSR` is an `if (0x301#12 == 0x301#12) then ...` chain, so `rfl` must evaluate `BEq` on `BitVec 12` literals (by `decide`-style kernel reduction) and then match the do-block. The branch body is `writeReg misa (← legalize_misa (← readReg misa) value); pure (Ok (← readReg misa))`, which is the same bind order as the RHS. Likely still `rfl`, but this is the one real check in my slice.
  Fix if `rfl` fails: `by simp [write_CSR]` (the `if` on `0x301#12 == 0x301#12` simp-reduces with `BEq`/`beq_self_eq_true`), or `by unfold write_CSR; simp`, or `by decide`-guarded `rw [if_pos (by decide)]; rfl`.
  Also, `run_csr` runs `v_eval` through `run_hart_active`, which reaches `write_CSR` only via `wr_misa`, so any simp-order change from the `if` shape should be local to this one lemma.

## Shared patterns (apply across slices)
1. All shortcircuit uses need the same thing: `sail_eval` must reduce `a <&&> (do b)`. I did not see `andM`/`orM`/`<&&>` handled in `Riscv/Steps/SailEval.lean` (it special-cases `Bind.bind`, `ite`, `dite`, and unfolds listed constants). `<&&>` is `andM`. One fix covers all: add `andM`/`orM` to the unfold set, or provide bridge lemmas `andM a b s = (do let x ← a; if x then b else pure false) s` (and the `orM` analogue). Check by running an `execute_*` or `currentlyEnabled`-reaching step lemma. Nothing in my slice names these directly, but `virtual_memory_supported`, `within_mmio_*` and `zicfiss_xSSE` are reachable from `run_hart_active` through `vmem_*`/`translateAddr`/`execute_*`, which the Steps proofs unfold.
2. Unit-stmt wrappers (`let _ ← ((do S) : SailM Unit)`): one bridge lemma `(do let _ ← (x : M Unit); k) = (do x; k)` should be `rfl`-true; the real question is whether `sail_eval` looks through the ascription. Ascriptions are elaborated away, so it should.
3. Generic risk: `Riscv/Steps/*` proofs unfold large callers (`run_hart_active`, `fetch`, `translateAddr`) with `sail_eval`. Shapes of my UNUSED functions only matter through those, so triage the callers, not these names.
