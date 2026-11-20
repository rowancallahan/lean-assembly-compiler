# `Arm/sail`: the C compiler's correctness on the official Sail ARM model

Lean 4.34.1. `lake build ArmSail ArmSail.Axioms` from this directory, after the partitioned model is built in
`/home/user/armv9-lean` (`python3 Arm/gen/partition.py Arm/model /home/user/armv9-lean Arm/proofs/Arm`, then
`cp Arm/model/lake-manifest.json /home/user/armv9-lean/` and `Arm/gen/build_part.sh /home/user/armv9-lean 1` on a
15 GB box, about 2 h; Testing/notes/ARM_FAST.md §9). Sail and `armv9` are path requirements on that build, so lake
reuses its oleans. Do not run `lake update` in the model directory: it moves Sail off the pinned rev.

## Statement

* `armSail : Proven.Top.Machine` (`ArmSail/Machine.lean`, outside `Spec/`): `step` = one Sail `step_model`
  (`ArmProof.stepModel`); `observe` = `_PC`, `x0..x30` (registers ≥ 31 read 0), the bytes in Sail's memory map;
  `configured s` = `(∃ n, ArmFullB s n) ∧ _PC present`; `mapping = armMapping`; RAM `[2^31, 3·2^30)`.
* `a64Sail : JT.A64Sem armSail TT TT` (`ArmSail/A64.lean`), `TT = fun _ _ => True` (no permissions: MMU off, EL3).
* `C_correct_armSail : CompileCorrect armSail (compileOn ArmRA.rv2arm)` and
  `C_runs_armSail : CompileRuns armSail (compileOn ArmRA.rv2arm)` (`ArmSail/Top.lean`): `C_correct_rv2arm a64Sail` /
  `C_runs_rv2arm a64Sail` with the loader premise `ArmLoader TT TT` discharged (`loader_ok`), as in `cc_of_P`.
* `ArmSail/Axioms.lean` prints the axioms.

## What was changed in `Arm/proofs/Arm` for this

* **Address assumption** (`Fetch.lean`): `VaOK n := n < 2^48 ∧ n / 2^16 ≠ 0x2C00 ∧ n / 2^16 ≠ 0x3C00` (translation
  range; not the GIC or UART 64 KiB device page) replaces `n < 2^29` in every fetch / load / store lemma. Only
  `dev_ne` and `setw56` used the bound (plus `< 2^48` for translation). `va29` recovers the old form; `vaRam` covers
  the RAM window.
* **`BTypeNext`** (`Full.lean`): `ArmFullB s n` is the configuration with `BTypeNext = n`; `ArmFull s := ArmFullB s 0`.
  `br` / `blr` leave `0b01` / `0b10` and no other instruction rewrites it (BTI is off, so it is never read), so the
  per-form lemmas take any `n` and keep it; `full_gen` goes from `n0` to the `n1` the instruction leaves. The 216-word
  path (`full_word`, `compile_ok`) still uses `ArmFull`.
* **New forms**: `FullSubs.lean` (`subs xd, xn, xm` with symbolic `d`; FullCmp's `cmp` is only `d = 31`), and the AL
  drafts made to compile: `FullAluAdd` (add/sub reg), `FullAluLogic` (and/orr/eor), `FullAluShift` (lslv/lsrv/asrv),
  `FullCmp` (cmp, cset), `FullMul` (madd/mul), `FullBrLdur` (br/blr/ldur).
* 8-byte `ldr`/`str [xn, #8·imm12]` already existed (`full_ldr` / `full_str`, symbolic imm; `[x16]` is imm 0).

## Spec

`Spec/` is unchanged. Putting `arm : Machine` into `Spec/Machines.lean` would need the Sail model (or at least
`Armv9Core` + the proof layer that defines `stepModel`, `xget`, `ArmFullB`) in Spec's import closure, i.e. Spec would
depend on the generated model and the lean-sail package. That is an owner decision.
