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
* `ArmSail/Axioms.lean`: `a64Sail`, `C_correct_armSail`, `C_runs_armSail` depend on `propext, Classical.choice,
  Quot.sound` only (no `sorryAx`); `Reduce__1` prints as an `opaque` (the generated `partial def`), same three axioms.
  Run: `lake env lean ArmSail/Axioms.lean`.
* Build (2026-11-20, 4 cores / 15 GB, Lean 4.34.1): `lake build ArmSail ArmSail.Axioms`, 431 jobs, the model's
  oleans replayed. Fresh, the non-model part (Arm/proofs/Arm incl. `Words` ~550 s, the Nano closure of `ArmTop`)
  takes about 25 min with `LEAN_NUM_THREADS=3`.

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

## Proof notes (`ArmSail/*`)

* `Machine.lean`: `obs_eq` (`Abs` + `_PC` ⟹ `obsS s = obsA pc a s.mem`), `abs_ex` (every `ArmFullB` state has an
  abstraction: x from `xget`, NZCV from PSTATE), `goes1`/`goes2` (one / two full steps are `GoesK`), `set_obsA`,
  `memword` (an observed `WordAt` is Sail's `MemWord`), `pre` (bundles a field's premises: configuration, `Abs`, pc,
  `VaOK` from the RAM window, the fetched word).
* `Enc.lean`: model-free encoding facts copied from `Arm/apc` (mask, fields, offsets, conditions after `subs`).
  `immt` is proved with `rw`, not `simp`: the `simp` proof of `movk`'s immediate made the kernel recurse too deep.
* `Fields.lean`: one `F_*` per field, each `pre` → `full_X` → rewrite the slices to the field numbers →
  `goes_set`/`goes_jump`/`goes1`. `cmpbr` = `full_subsr` then `full_bc` (`condP_abs`, `cond_sub`); stores compare
  `wrD` (`wrD_get`) / `insert` with `store8` / `store1`; `br` uses `full_brB` (ends in `ArmFullB _ 1`).

## Configuration caveats (non-vacuity review, branch `sailv-fable`)

`C_correct_armSail` / `C_runs_armSail` cover a **hand-pinned EL3 configuration** (`ArmFullB`), not a state shown to be
reached from the model's reset. The pins are consistent (`ArmProof.witness_full`; `ArmSail/NonVacuous.lean` adds any
PC / `x0..x30` / memory), but these differ from what `__InitSystem` / `TakeReset` leave:

* `SCTLR_EL3 = 0`: reset sets the RES1 bits 29:28, 23, 18, 16, 5:4 (`Arm/model/Armv9/V8Base.lean:81216-81227`).
* `OSLSR_EL1 = 0`: cold reset sets `OSLK = 1` (`Sysregs.lean:660`).
* `CNTCR = 0`: `__InitSystem` sets `EN = 1` (`Reset.lean:111`); `PhysicalCount = 0` stays pinned only because the
  counter is off.
* `FeatureImpl = featV` (only `FEAT_AA64EL0`): reset rebuilds it from the `FEAT_*_IMPLEMENTED` registers
  (`V8Base.lean:8395`); `featV` is accepted by the model (`HaveEL` is constantly true) but is not an Armv9.4-compliant
  feature set.

All four are software- or configuration-writable after reset; that path is not proved.

Stack pointer: `obsS` reads register 31 as 0 while `armMapping.kept` contains 31, so "sp kept" is `0 = 0` on `armSail`
(`armDM` observes `t.sp` and has no such gap). The model's SP is `SP_EL0` when `PSTATE.SP = 0`, else `SP_EL3`
(`SP_read`, `V8Base.lean:63122`); `PSTATE.SP` is not pinned, and no `full_*` conclusion mentions either register.
