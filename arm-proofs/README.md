# Proofs against the generated ARM model

## AArch64 backend correctness (`Arm/`, Lean 4.34.1)

Build/check everything in order: `./check.sh` (oleans go to `build/`, not committed). Needs the built model in
`/home/user/armv9-lean`. `Proven/Code.lean` and `Proven/CompilerArm.lean` are byte-identical copies of the 4.29 sources.
`Arm/Words.lean` is generated: `python3 gen/gen_words.py > Arm/Words.lean`.

| File | Statement | Layer | Time |
|---|---|---|---|
| `Arm/Base.lean` | `xget`/`xset` (X0..X30 as `Nat`-indexed functions on the register map), `read_gpr_ok`, `write_gpr_ok`, `xget_xset`, `AddWithCarry_64_sub`, Sail shift-by-`Int` normal forms | helpers | ~31 s |
| `Arm/Exec.lean` | for symbolic `d n m < 31`: each decode function the backend reaches (add/sub/and/orr/eor/lslv/lsrv/asrv shifted-reg, subs (cmp), subs imm (cmp #i), csinc (cset lo/lt/eq), csel ne, movz, add imm, orr with xzr (mov)) returns `ok` with only `X[d]` (or PSTATE.NZCV) updated | decode function + execute | ~36 s |
| `Arm/Flags.lean` | `sub_flags`: NZCV written by `subs` = N:(x-y).msb, Z:x-y=0, C:y≤x (unsigned), V:(x-y).toInt ≠ x.toInt-y.toInt | helper | ~1 s |
| `Arm/Small.lean` | `AState`, `armStep` (the small machine), `ArmCfg`, `Abs`, `Frame`, `Step`, family lemmas | L2 machinery | ~2 s |
| `Arm/Words.lean` (generated) | for each of the 216 emitted words: `dec_*` (`__DecodeA64 pc w s` = the decode call, SEE < 1), `word_*` (L1: `__DecodeA64 pc w s = .ok () {s with regs := xset (s.regs.insert .SEE k) d v}`), `step_*` (L2); `emitted`, `armStep_ok` (L2) | top-level A64 decoder + decode + execute | ~550 s |
| `Arm/Compiler.lean` | `compile_ok_exec` (L3) | decode+execute of `gen e 0 ++ [iRes]` | ~24 s |
| `Arm/Axioms.lean` | `#print axioms` | | ~1 s |

Total clean check ~645 s (one process). Axioms of everything (`Arm/Axioms.lean`): `propext`, `Classical.choice`, `Quot.sound`. No `sorry`.
`ArmCfg s := s.regs.get? .SPESampleInFlight = some false`. Not covered: fetch, PC update, interrupts, `ret`, `__TopLevel`.

## Earlier single-word experiments (hand-written)

Check: `cd armv9-lean && lake env lean --tstack=400000 ../arm-proofs/<file>` (model must be built).

| File | Statement | Layer | Time |
|---|---|---|---|
| `AddExec.lean` | `add_x9_x10`: if R9 = a and R10 = b, the model's execute function for 64-bit shifted-register ADD with d=9, n=9, m=10, shift 0, no flags returns ok with R9 := a + b and nothing else changed | execute function only: not decode, not fetch, not the full step | ~9 s |
| `AddDecode.lean` | `decode_add_word`: if SEE < 1, `__DecodeA64 pc 0x8b0a0129` equals the model's ADD shifted-register decode function applied to Rd=9, Rn=9, Rm=10, with SEE set to 14 | top-level A64 decoder only | ~7 s |
| `AddWord.lean` | `add_word`: if SEE < 1, R9 = a, R10 = b, then `__DecodeA64_DataProcReg pc 0x8b0a0129` returns ok with registers = old registers with SEE := 14 and R9 := a + b, memory unchanged | sub-decoder + decode + execute | ~10 s |

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
Not yet: decode (`__DecodeA64 pc word` reaching this execute call), full step (`__TopLevel`), other instructions, general register numbers.

Model variant: `Reduce__1` is generated `partial` (see `arm-gen/DIFFS.md`), so no file here lists `sorryAx`.
