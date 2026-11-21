# Astra round 9 — parsing fuel loops in C (ADVICE; owner may override)

Relayed advice, not owner decisions.

Tail bit: inherit into if-branches, let body, parentheses; FALSE for condition, operands, call args,
pair fields, let value. Parse Z with self-calls forbidden, B with the bit set. Resolve self-calls by
binding identity (not spelling); fuel arg must be exactly the predecessor binder n.
TRAP: `f n s + 1` is NOT tail. Never emit CONTINUE when a call merely STARTS in a tail frame; record a
provisional self-call and validate when the enclosing expression completes (or know operator structure first).

Parser must reject (unless a checker on THIS path does it): wrong fuel var, fuel used as data, wrong arity
(check before dropping the fuel arg), self-call in a let value (even `let x := f n s; x`), shadowing
(compare resolved bindings), wrong state type/ownership. Lean acceptance does not cover these.

State: flattened layout of σ; CONTINUE e must have the same SHAPE, not just word count. Evaluate e into a
separate next-state area, commit all, dec fuel, jump. Fuel slot separate; exit type τ may differ.

Heap: fixed regions (frames, bindings, AST, scratch), indices, bounds-check every push; each frame saves
the binding-stack height. Reserve parent AST record before children, backpatch on completion; infix needs
operator frames / delayed parent discovery — preorder output must not force early tail classification.

Tests: typed random trees + independent recursive tail oracle in the harness; mutate contexts
(allowed: branch, let body, parens; rejected: operand, condition, pair field, arg, let value) and
fuel binder/arity/shadowing/shape/ownership. Include `f n s + 1` and `(f n s) + 1`. Shrink failures.

Proof sketch: induction on the grammar (tail-enabled = only branch choice / let body remain, so
f n s' ≡ CONTINUE s'), then induction on fuel.
