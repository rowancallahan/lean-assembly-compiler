# Triage part 09 (final_classes.tsv lines 185-207)

Analysis only; nothing was built. Uses were searched with `git grep -nw NAME -- Riscv Nano Compiler Spec ':!Riscv/gen' ':!*LeanRV64D*'` on rv-regen-434.

| name | class | #uses | verdict | fix |
|---|---|---|---|---|
| read_CSR | match_to_if | 0 | UNUSED | - |
| reset_misa | unit_stmt_ascription | 1 | NEEDS-FIX (check) | see A |
| reset_sys | unit_stmt_ascription | 0 (comment only) | NEEDS-FIX (check) | see A |
| reset_tvecs | unit_stmt_ascription | 1 | NEEDS-FIX (check) | see A |
| round_down | do_or_parens_only | 0 | UNUSED | see D |
| round_up | do_or_parens_only | 0 | UNUSED | see D |
| run_hart_active | unit_stmt_ascription | 14 | NEEDS-FIX (check) | see B |
| run_hart_waiting | shortcircuit+unit_stmt_ascription | 0 | UNUSED (reached only via try_step) | see C |
| rvfi_fetch | shortcircuit+unit_stmt_ascription | 0 | UNUSED | - |
| set_xepc | unit_stmt_ascription | 0 | UNUSED | - |
| should_inc_mcycle | shortcircuit | 0 | UNUSED | - |
| should_inc_minstret | shortcircuit | 0 direct | LIKELY-OK (reached via try_step) | see C |
| sig_store | shortcircuit+unit_stmt_ascription | 0 | UNUSED | - |
| tick_clock | unit_stmt_ascription | 0 | UNUSED | - |
| track_trap | unit_stmt_ascription | 0 | UNUSED | - |
| translateAddr | unit_stmt_ascription | 0 | UNUSED | - |
| trap_handler | unit_stmt_ascription | 0 | UNUSED | - |
| try_step | shortcircuit+unit_stmt_ascription | 7 | NEEDS-FIX (check) | see C |
| update_and_write_pte | shortcircuit | 0 | UNUSED | - |
| valid_narrowing_fp_conversion | shortcircuit | 0 | UNUSED | - |
| valid_wide_mvvtype | shortcircuit | 0 | UNUSED | - |
| valid_wide_mvxtype | shortcircuit | 0 | UNUSED | - |
| valid_wide_vvtype | shortcircuit | 0 | UNUSED | - |

"Check" means I have not seen the proof fail. A build of the named module is needed to confirm.

## What changed (from fdiff.txt)
- unit_stmt_ascription: a unit-valued statement `S` becomes `let _ ← ((do S) : SailM Unit)`, or `: SailME Step Unit` etc. in the early-return monads. The only token change is the added `let _ ←`, `do` and the ascription. Binder shapes stay `bind _ (fun _ => ..)`, so many uses should still be defeq. Normalized hashes differ, so the Expr is not identical.
- shortcircuit: `(a ← x) && (b ← y)`-style code changes to `do (pure (a)) < & & > (do ...)` and similar. This is the new if-chain / `&&` form with the effects nested inside `do`. `should_inc_*`, `valid_wide_*` and `update_and_write_pte` have it. It matters only if a proof reduces the `&&`.
- round_down / round_up: the value changed, not just its shape. `round_down x` was `x.toUInt64.toNat` and is now `x.floor.toInt64.toInt`. `round_up x` was `round_down (x+0.5)` and is now `x.ceil.toInt64.toInt`. Type unchanged (`real -> Int`). `real` is `Float`, so this is a semantic change for negative or large inputs.
- read_CSR: match → if-chain. fdiff.txt has no entry for it.

## Details per use

### A. reset_sys / reset_misa / reset_tvecs (Riscv/Back/BootReset.lean)
- Line 18 mentions `reset_sys` only in a docstring. `resetSysWith` (l.19-52) is a hand-copied body of `reset_sys`.
- Line 23 calls `reset_tvecs ()` and line 25 calls `reset_misa ()`, both inside the copy. They are opaque in the copy.
- Line 61: `theorem reset_eq : reset () = resetWith (cancel_reservation ()) := rfl`. This is the one real risk. The copy was verbatim from the old model, and `reset_sys` now has the `let _ ← ((do ..): SailM Unit)` shape.
  - The ascription is erased at elaboration, so `rfl` may still hold.
  - If the shape differs, `rfl` fails. Fix: re-copy `resetSysWith` from the new `reset_sys` body, keeping the `cancel` hook where `cancel_reservation ()` was. Or prove `reset_eq` by `unfold reset reset_sys resetWith resetSysWith; rfl`, or by `simp only [...]` plus `rfl`.
- Line 148 does `sail_eval [cb_mstatus, cb_mcause, cb_misa, ...]` on `resetWith`. It unfolds `reset_tvecs`, `reset_misa`, `reset_pmp` and so on.
  - The new `let _ ← ((do ..))` is a `bind` of a `do`-block. The `sail_eval` evaluator handles `bind`, so it is probably fine.
  - If it gets stuck on a nested `do`, add `SailME.run`/`bind_assoc`-style lemmas, or use `frozen[...]`.
- Verify with `lake build Riscv.Back.BootReset`.

### B. run_hart_active (14 mentions)
- Riscv/Back/BootV.lean:92, 99, 107, 113: statement and `sail_eval frozen[run_hart_active] [hr, ...]`. It is frozen, so opaque: LIKELY-OK.
- Riscv/Steps/Step.lean:218, 224, 229, 310, 318 are the same pattern, with hypotheses `hr : run_hart_active 0 s = .ok ...` and `frozen[run_hart_active]`. Mentions at 216, 305 and 348 are docstrings.
- Spec/Riscv.lean:34 (statement only) and Spec/RiscvMachine.lean:32 (`match run_hart_active 0 state, try_step 0 false state`). The Spec files must not be edited, and they are opaque.
- The per-word lemmas (`run_hart_active 0 s = .ok ...`) are proved elsewhere, by `sail_eval` with the generated `Riscv/Steps/*` and `Gen*`. These unfold `run_hart_active`'s callees, not `run_hart_active` itself, so changes inside `run_hart_active` (new `SailME Step Unit` ascriptions) matter only if some proof unfolds it. `grep -n "unfold run_hart_active\|simp.*run_hart_active"` found none.
- Verdict: LIKELY-OK. Builds of `Riscv.Steps.Step` and `Riscv.Back.BootV` will confirm.

### C. try_step / should_inc_minstret / run_hart_waiting
- Step.lean:216-224 is `try_step_of`: `try_step 0 false s = .ok false {...}`, by `sail_eval frozen[run_hart_active] [hr, hh, hn, hm, hi, h.priv, h.hart, h.mcountinhibit, h.minstretcfg]; all_goals rfl`.
- BootV.lean:112-113 is the same pattern. Spec/Riscv.lean:35 and Spec/RiscvMachine.lean:32 only mention it.
- `try_step` is unfolded by `sail_eval`. `run_hart_active` is frozen, so its body is not entered. This is the NEEDS-FIX candidate.
- In the new model, `try_step` calls `run_hart_active`, `run_hart_waiting` and `should_inc_minstret` (checked in the model diff).
  - `should_inc_minstret` has the new shortcircuit form `do (pure ..) <&&> (do ..)`. The proof reduces it with `h.mcountinhibit` and `h.minstretcfg`, so the `&&` is evaluated symbolically.
  - If `sail_eval` leaves a goal, the likely cause is the new `<&&>` shape (`and`, `if`), or an `ite` on a `Bool` that the `simp` set no longer folds.
  - The `try_step` body also has new `let _ ← ((do ..): SailM Unit)` wrappers.
- Suggested fixes, in order:
  1. Build `Riscv.Steps.Step` first. Mind the 4.34.1 timings.
  2. If stuck on `&&`, add `Bool.and_eq_true, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.not_eq_true'` or the monadic `bind_pure_comp`/`pure_bind` to the sail_eval simp set.
  3. If stuck on the `ite`, add `split` or `apply_ite`-style steps.
  4. If still stuck, a bridge lemma `should_inc_minstret_eq : should_inc_minstret () = <old form>` (by `unfold should_inc_minstret; simp [...]`, `rfl` or `decide`) can feed one `simp` rewrite.
- This pattern (`try_step_of`, BootV:112) is a single proof, written once and reused. One fix covers both.

### D. round_down / round_up
- No proof uses them. Float semantics changed (toUInt64.toNat → floor.toInt64.toInt). If float rounding is ever used in FP instruction proofs, they need re-checking. Today none are.
- The names are not matched in Frontx (`LeanSvg.Fx.floor` is a different thing).

## Shared patterns
- All uses of these 23 names sit in two proof sites: `Riscv/Back/BootReset.lean` (`reset_eq` by `rfl` plus the `sail_eval` at l.148) and the `try_step_of` / `sail_eval frozen[run_hart_active]` pattern in `Riscv/Steps/Step.lean` and `Riscv/Back/BootV.lean`.
- The class `unit_stmt_ascription` should be defeq-neutral in elaborated terms but the normalized hashes show it is not literally identical. Treat `rfl` proofs that compare against hand copies as the first check.
- The `shortcircuit` class only affects proofs that reduce `&&`/`||` on Bool inside the monad. Here that is only `should_inc_minstret` (via `try_step_of`).
- Everything else in my slice is UNUSED by the proof code.
