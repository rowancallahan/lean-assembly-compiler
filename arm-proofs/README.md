# Proofs against the generated ARM model (hand-written)

Check: `cd armv9-lean && lake env lean --tstack=400000 ../arm-proofs/<file>` (model must be built).

| File | Statement | Layer | Time |
|---|---|---|---|
| `AddExec.lean` | `add_x9_x10`: if R9 = a and R10 = b, the model's execute function for 64-bit shifted-register ADD with d=9, n=9, m=10, shift 0, no flags returns ok with R9 := a + b and nothing else changed | execute function only: not decode, not fetch, not the full step | ~9 s |

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
Not yet: decode (`__DecodeA64 pc word` reaching this execute call), full step (`__TopLevel`), other instructions, general register numbers.
