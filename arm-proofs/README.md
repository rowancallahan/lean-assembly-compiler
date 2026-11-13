# Proofs against the generated ARM model (hand-written)

Check: `cd armv9-lean && lake env lean --tstack=400000 ../arm-proofs/<file>` (model must be built).

| File | Statement | Layer | Time |
|---|---|---|---|
| `AddExec.lean` | `add_x9_x10`: if R9 = a and R10 = b, the model's execute function for 64-bit shifted-register ADD with d=9, n=9, m=10, shift 0, no flags returns ok with R9 := a + b and nothing else changed | execute function only: not decode, not fetch, not the full step | ~9 s |
| `AddDecode.lean` | `decode_add_word`: if SEE < 1, `__DecodeA64 pc 0x8b0a0129` equals the model's ADD shifted-register decode function applied to Rd=9, Rn=9, Rm=10, with SEE set to 14 | top-level A64 decoder only | ~7 s |

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
Not yet: decode (`__DecodeA64 pc word` reaching this execute call), full step (`__TopLevel`), other instructions, general register numbers.

**Axiom caveat for `AddDecode.lean`:** `#print axioms` lists `sorryAx`. It is not from the proof: the
statement mentions `__DecodeA64`, which reaches `Reduce__1`, whose termination proof in the generated
model is `sorry` (and cannot be proved as generated: for input width 0 or 1 the recursive call is not
smaller, because the Sail type constraint on the width is not carried into the Lean type). Every theorem
that mentions the decoder inherits it. Fix under test: generate with `--lean-partial-function Reduce__1`.
