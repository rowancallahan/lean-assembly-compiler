# con-leche core knot: design note (external review, 2026-11-16) + checks against our code

Source: an external read-only reviewer (owner's request), given the question and file locations only; it could not fetch the
files, so its repository-specific claims were unverified. Checked here by the main session.

## Recommendation (summary)

1. Target the concrete twin `ConLeche/Cached/CoreC.lean` first (monad fixed to `CheckCM = StateT CState (Except CheckError)`,
   no `CoreFns` record, one `mutual` block from line 401, WF recursion on tuple measures). The generic `Kernel/Core.lean`
   (`[Monad m]`, `r : CoreFns m`) comes second, by specialisation (memoise specialised symbols before compiling bodies).
2. Front end driven by equation lemmas: take the declaration's equation/unfold theorems (discover them, do not guess names),
   rewrite one application, normalise lets/matches/projections/concrete `bind`/`pure`, stop at calls to members of the
   current recursive component and emit IR `call`s. Never unfold the whole component.
3. Keep two certificates apart: body equation (body = original) and call decrease (callee smaller in the WF relation used by
   Lean). Termination measures and accessibility proofs are proof-only; never compute them at run time.
4. Modular proof: per member, `body_correct_f : (∀ c', R c' c → Correct c') → Correct c`; close the component once by
   `WellFounded.induction` on a tagged call type (member tag + arguments, dependent result type); export per-function theorems.
   Quantify over all states (state is not in the measure). Compute SCCs; acyclic parts first.
5. Fuel: source fuel (`whnfLoopFuel = 2^62`) is a value, kept exactly; it is not a step budget and not an unrolling count.
6. `CheckCM α = CState → Except CheckError (α × CState)`: errors carry no final state; short-circuit preserved.
7. Two separate claims: (a) machine code computes `CoreC` (our theorem); (b) `CoreC` implements the verified abstract
   checker (con-leche's own refinement theorems, see `Verify/Knot.lean`; check before choosing the public statement).

Recommended order: (1) audit; (2) one WF (non-structural) function via its equation theorem; (3) small mutual component
with different result types and a non-tail call; (4) lexicographic measure with an inner component that resets/increases;
(5) state + exceptions across recursive calls; (6) large `Nat` fuel constant; (7) `CoreC` component by component, caching
certificates; (8) generic monad + `CoreFns` specialisation.

## Checked against our code (main session)

- IR recursion (reviewer's §6): **supported.** `Compiler/Ir/Sem.lean:196` `step`: a `call` looks up `P.funcs[g]` by id,
  pushes a fresh frame (`alloc (G.slots+1)` event) and continues; any call graph, cycles included. `ir_compile_runs` /
  `ir_compile_correct` (`Riscv/Back/IrTop.lean:227,239`) are simulation proofs of this semantics, so the back end needs no
  change. The missing piece is the source → IR front end with proofs (items 2–4).
- `Nat` fuel 2^62: our scalars are 64-bit words with visible range hypotheses, so the constant fits; needs the 0-ary
  constant feature (ROADMAP "Next Opus rounds", round 1).
- Lean 4.29 well-founded definitions are irreducible by default; use the generated equation lemmas, not `unfold`/`decide`.

## Plan

Opus round after round 1 (constants + monomorphisation + translator crashes): reviewer's steps 2–5 on small examples
(book/our own WF functions first), then `CoreC` component by component. IR S3 (composition) runs before or alongside,
since `CoreC` bodies need inductives + monad + structures in one function.
