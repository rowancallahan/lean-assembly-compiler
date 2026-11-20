# Proof/Machine

**What it does.** The bridge from Gen's emitted code to a machine run. Input: Gen's words for a parsed program
(Proof/Gen: words = templates). Output: every safe J run of those templates is a run of the target machine
(`JT.sim_star`), lifted to the host contract (`Host*`), used by Proof/Main (`C_correct_on`, `C_runs_on`).

**Files, by layer.**
* J and templates: `Call`, `CallA`, `Expr`, `Templates`, `Heap`, `Loop` (the IR `CallProbe.J`, Gen's templates, plain
  `Star` runs of the leaf templates); `NdSem` (a node's J template); exactness `ExprExact`, `CallExact`, `MachExact`,
  `NdCG*` (Gen's words = `template.map encG`); `Bridge`, `ExprBridge`, `TmGood` (encoders, `GoodX`).
* Safe-run layer (the one the top uses): `JLay` (`LayW`, `SafeX`, `SStarX`), `SafeRun` (leaf runs as `SStarX`),
  `EVSDefs`…`EVSProg` (contracts `EVHwS`/`EVHtS`/`DefXS`, node theorem `runVS/runTS/runLS`, defs/program),
  `StartSafe`, `StartAllS`, `GenRunS` (whole program).
* Exits: `RoomRun` (out of room → stub word 1), `CapRun`, `CapNode`, `CapProg`, `CapStart` (buffer cap → stub 6),
  `SemCases`, `RunsDef`, `RunsShift` (exact work bound).
* Plain layer (`EVX*`, `HeapEV`, `ExprEV`, `NdRun`, `NdDef`, `NdProg`, `NdTop*`, `StartRun`, `GenRun`, `GenMain*`):
  semantics (`SemW`/`SemT`, `loopS`, `semAt`), side conditions (`OkV/OkT/OkL`, `DefOK`) and helpers shared by the
  safe layer. No tail/loop/node/def/program run theorem lives here any more (they were only consumed by a conjunct
  `gen_runS` discarded).
* Targets: `Target`, `RvTarget` (+ `SimW`, `SimX`, `SimXB`, `RvStep`, `RvEnc`), `ArmTarget` (+ `A64Sem`, `ArmEnc*`,
  `ArmRA*`), host lift `HostOn`, `HostGen`, `HostOk`, `HostOom`; `NoW`, `JNorm`.

**Design decisions.**
* One safe-run predicate for the shared layer: `SafeX`/`SStarX` (`JLay`). The older `Safe`/`SStar` (no start-code
  instructions, beq +2 only) remains only inside the RISC-V Sail lift (`SimW.sim_stepW`/`sim_starW`), which the RV
  adapter builds on. Rejected: keeping both in the shared layer (every template proved twice).
* Templates are proved once, as safe runs; there is no plain-run twin of a contract.
* Known limits: J is RISC-V-shaped (immediates ±2048, jal ±2^18 J words, fixed short branch skips in `SafeX`); code
  layout is uniform (`addr base pc = base + 4·blockLen·pc`), which blocks non-padded variable-length targets
  (see Testing/notes/CLEANUP_PLAN.md).

**Build/check.** `lake build Nano.V2Self.REVIEW`, `Testing/scripts/review_axioms.sh`; ARM: `Arm/apc` `Blocks.ArmDMTop`.


## Target interface and adapters (`Target.lean`, `RvTarget.lean`, `ArmTarget.lean`, `Host*.lean`)

What it does: states once what a machine must provide for Gen's J programs to run on it (`JT.JTarget` + `Laws`),
and lifts the J-level run theorems to any such machine (`HostOn`, `HostGen`, `HostOk`, `HostOom`). Fed by the J runs
(`SStarX`, EVS*/Cap*); used by `Main/TopOn.lean` (`C_correct_on`, `C_runs_on`).

* `JLay.lean:LayW` — the generic layout: code base, work cells, input/output bytes, entry memory. No code words.
* `Target.lean:JTarget` — machine `M`, `blockLen`, `enc` (words of one J instruction), `reg`, `scratch`,
  `lay : LayW → List J → Prop`, `m0`, `inv : LayW → List J → M.State → Prop`, `valid`, `loader`.
* `Target.lean:JTarget.Rel` — J state ↔ machine state through `observe`; `Laws` — what a target proves
  (`steps`, `addi_ok`, `ret_ok`, `lay_init`, `inv_init`, `m0_obs`, `reg_map`, `kept_map`, `ram`).
* `Target.lean:StepAt j` — the obligation for one J instruction `j`: at `C[pc]? = some j`, a `SafeX` step is a
  machine run keeping `Rel`. `StepLaws` — one field `StepAt (.k …)` per J constructor (14).
  `StepLaws.step_ok` / `Laws.step_ok` — the dispatch over `C[pc]?`, proved once. Tactic `jcase` reduces `hS`/`hs`
  to `j`'s clauses inside a field proof.
* `RvTarget.lean:rv_at`, `rvSteps` — each field is one Sail simulation lemma (`SimW`/`SimX` `sim_*`).
* `ArmTarget.lean:arm_at`, `armSteps` — each field is that kind's block run (`blk_*`).
* `RvTarget.lean:rvTarget`, `rvLaws` — RISC-V (one RV64 word per J instruction), from the Sail simulation
  (`SimW`/`SimX`/`RvStep`) through `relW_of` / `rel_of`.
* `ArmTarget.lean:armTarget`, `armLaws` — AArch64 over any `A64Sem` machine (4-word rv2arm blocks).
* `HostGen.lean:tbytes`, `enter` — a target's code bytes for a J program; a `StartCorrect` state enters `Rel`.

Design decisions:
* The code words are target-private. `LayW` has no words field and `JTarget` no `words`: RISC-V keeps its words in
  `SimW.lean:LayRv` (`LayW` + `W`), built from the program by `RvTarget.lean:rvLay K C` (`W = C.map encJX`), so
  `rvTarget.lay K C = (rvLay K C).Ok`. Rejected: a generic `LayW.W : List Nat` with `K.W = T.words C` threaded
  through `enter`/`lay_init`/`inv_init` — it is one-word-per-instruction RV data that ARM filled with zeros and
  used only for its length.
* `inv` and `lay` take the J program `C`, so a target states code-dependent facts (ARM: `PermOK … (16 * C.length)`)
  from `C` directly instead of through a recorded word list.

* The step law is per J constructor (`StepLaws`), not one `step_ok` with a `cases` inside each target: a new J
  instruction adds one constructor clause in `step`/`SafeX`, one `StepLaws` field, one dispatch line, and one field
  proof per target; existing fields are untouched. Each field is stated uniformly through `SafeX`/`step`
  (`StepAt`) instead of restating the side condition and result per kind (rejected: 14 hand-written statements
  that must be kept in sync with `SafeX` and `step`). The former dispatchers `SimX.sim_stepX` and
  `ArmTarget.arm_step` are gone; their case bodies are the fields.

Assumes: `SafeX` J steps (ranges, work cells) from the run layer. Guarantees: `Laws.step_ok` (from `steps`; one safe J step = a
machine run keeping `Rel`), hence `host_ok` / `host_tiny` / `host_room` for `tbytes T Cj`.

Known limits: `enc : J → List (BitVec 32)` with `enc_len = blockLen` and `addr = base + 4·blockLen·pc` fix uniform
32-bit-word blocks; `SafeX` carries RV immediate/jump ranges; `Laws.ram ≤ 2^32`. A variable-length target (x86-64)
needs these generalised (not done here).

Build / check: `lake build Nano.V2Self.Proof.Machine.RvTarget Nano.V2Self.Proof.Machine.ArmTarget
Nano.V2Self.Proof.Machine.HostOom`, then `Nano.V2Self.REVIEW` and `Testing/scripts/review_axioms.sh`.
