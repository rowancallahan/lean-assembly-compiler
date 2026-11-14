# frontx: working plan (helper's own notes; newest first)

## Next: tuple / Option results ("tagged data without allocation", results first)

Generic part (Tree.lean): `LOut.retm r rs` (`rs : List (Nat × BitVec 64)`: extra result variables and their
values), `Sim` case `∃ σ', step = some (.ret r σ') ∧ ∀ p ∈ rs, σ'.env p.1 = p.2`, `sim_retm`, `sim_retm_elim`,
`step_callQ`, `step_retQ`, `prog_okQ` (from `prog_ok`: final variables `< M`, `≠ out` are those of the tree's
final state).

Translator (recursion / non-recursive path of `compileCmd` only, not loops yet):
- result type `α × β` (right-nested) or `Option α` with scalar components: component functions `π_j`
  (`Prod.fst/snd` chains; `Option.isSome` and `fun o => o.getD 0`), `ctx.rty` = type of component 0, extra result
  variables `rv_j` allocated right after the parameters;
- at a `ret` leaf with Lean value `e` (must be a constructor application `(a, b)`, `some v`, `none`):
  `e_j := π_j e` normalised; component 0 is the `ret` expression; for `j ≥ 1` emit `let_ rv_j := e_j` items (not in
  memo/temps); outcome `LOut.retm (rep e_0) [(rv_j, rep e_j)]`, proof `sim_retm` with one `oblig` for the
  `∀ p ∈ [...]` fact;
- `f.runs : … → ∃ σ', Runs tree σ (rep (π_0 (f xs))) σ' ∧ ∀ p ∈ [(rv_j, rep (π_j (f xs)))], σ'.env p.1 = p.2`
  (tactic: `step_callQ` + `frontx_ih` / `sim_retm_elim` + `step_retQ`), `f.exec` by `prog_okQ`.
- then: tuple/Option *parameters* (one variable per component; `match p with | (a, b)`, `match o with | none | some v`
  as tests on the tag variable), structures of scalars the same way, enum-like inductives as a tag word.

## Not started / deferred
- loop inside a loop body, two loops in sequence (= calls: `sub` node, variable renaming of the callee) — see
  the message to the coordinator; NOTES §10.1.
- list parameters as array views (`length`, `sum`, … of the book).
- generated machine-theorem statement; rebase onto reorganised `main` (module renames `Proven.X → Riscv.Direct.X`).
- monomorphisation / specialisation of polymorphic and higher-order definitions (only head-unfolding with a known
  function argument exists: `skipWhile … isWs`).
