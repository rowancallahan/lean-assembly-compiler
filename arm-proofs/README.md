# Proofs against the generated ARM model (hand-written)

Check: `cd armv9-lean && lake env lean --tstack=400000 ../arm-proofs/<file>` (model must be built).

| File | Statement | Layer | Time |
|---|---|---|---|
| `AddExec.lean` | `add_x9_x10`: if R9 = a and R10 = b, the model's execute function for 64-bit shifted-register ADD with d=9, n=9, m=10, shift 0, no flags returns ok with R9 := a + b and nothing else changed | execute function only: not decode, not fetch, not the full step | ~9 s |
| `AddDecode.lean` | `decode_add_word`: if SEE < 1, `__DecodeA64 pc 0x8b0a0129` equals the model's ADD shifted-register decode function applied to Rd=9, Rn=9, Rm=10, with SEE set to 14 | top-level A64 decoder only | ~7 s |
| `AddWord.lean` | `add_word`: if SEE < 1, R9 = a, R10 = b, then `__DecodeA64_DataProcReg pc 0x8b0a0129` returns ok with registers = old registers with SEE := 14 and R9 := a + b, memory unchanged | sub-decoder + decode + execute | ~10 s |

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
Not yet: decode (`__DecodeA64 pc word` reaching this execute call), full step (`__TopLevel`), other instructions, general register numbers.

Model variant: `Reduce__1` is generated `partial` (see `arm-gen/DIFFS.md`), so no file here lists `sorryAx`.
