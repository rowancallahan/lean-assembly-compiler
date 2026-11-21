# Proof/Machine

**What it does.** The bridge from Gen's emitted code to a machine run. Input: Gen's words for a parsed program
(Proof/Gen: words = templates). Output: every safe J run of those templates is a run of the target machine
(`JT.sim_star`), lifted to the host contract (`Host*`), used by Proof/Main (`C_correct_on`, `C_runs_on`).

**Files, by layer.**
* J and templates: `Call`, `CallA`, `Expr`, `Templates`, `Heap`, `Loop` (the IR `CallProbe.J`, Gen's templates, plain
  `Star` runs of the leaf templates); `NdSem` (a node's J template); exactness `ExprExact`, `CallExact`, `MachExact`,
  `NdCG*` (Gen's words = `template.map encG`); `Bridge`, `ExprBridge`, `TmGood` (encoders, `GoodX`).
* Safe-run layer (the one the top uses): `JLay` (`LayW`, `SafeX`, `SStarX`), `SafeRun` (leaf runs as `SStarX`),
  `EVSDefs`…`EVSLoop` (contracts `EVHwS`/`EVHtS`/`DefXS` and the success fragment rules), `EVSRun` (`RunCxS`),
  `CapNode` (outcome contracts `EVO`/`EVOt`/`DefO`, node theorem `runVO/runTO/runLO`), `CapProg` (`progRunO`),
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
  instructions, beq +2 only) and their Sail lift `SimW.sim_stepW`/`sim_starW` had no users left and are deleted;
  the RV adapter uses the per-instruction `sim_*` lemmas (`rvSteps`). Rejected: keeping both predicates (every
  template proved twice).
* The tail, loop, node, def and program run theorems exist once, as safe runs. Plain-run contracts and proofs
  remain for the leaves and compositions (`EVH` in `HeapEV`, `EVHw` in `EVX`/`EVXP`/`EVXF`, `DefX` in `EVXC`,
  `ExprEV`, `StartRun`) next to their `…S` twins; removing them is CLEANUP_PLAN step 5 b/c.
* One node induction for all outcomes: `EVO` bundles a fragment's success contract and its failure contracts (every
  kind: cap, room) as two fields, so `runVO`/`progRunO` derive each node's side conditions once. The fragment rules
  are not merged (success in `EVS*`, failure in `CapRun`/`RoomRun`): their proofs differ after the common prefix.
  Rejected: one contract with a `match` on the semantics' result (all ~30 fragment proofs restated). See
  Testing/notes/OUTCOME_CONTRACT.md.
* Known limits: J is RISC-V-shaped (immediates ±2048, jal ±2^18 J words, fixed short branch skips in `SafeX`); code
  layout is uniform (`addr base pc = base + 4·blockLen·pc`), which blocks non-padded variable-length targets
  (see Testing/notes/CLEANUP_PLAN.md).

**Build/check.** `lake build Nano.Main.REVIEW`, `Testing/scripts/review_axioms.sh`; ARM: `Arm/apc` `Blocks.ArmDMTop`.


## Target interface and adapters (`Target.lean`, `GTarget.lean`, `GUniform.lean`, `RvTarget.lean`, `ArmTarget.lean`, `Host*.lean`)

What it does: states once what a machine must provide for Gen's J programs to run on it, and lifts the J-level run
theorems to any such machine. Two interfaces: the general `JT.GTarget` + `Laws` (per-program image: code bytes, byte
offset per J instruction, anchor pcs; segment law) and the uniform `JT.JTarget` + `Laws` (one fixed-size block per J
instruction; one obligation per J instruction kind). The host lift (`HostOn`, `HostGen`, `HostOk`, `HostOom`) and the
top theorems (`Main/TopOn.lean:C_correct_g`, `C_runs_g`) are proved once, over `GTarget`; a uniform target reaches
them through `GUniform.lean` (`toG`, `laws_toG`), giving `C_correct_on`, `C_runs_on` as one-line corollaries. Fed by
the J runs (`SStarX`, EVS*/Cap*).

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
* `GTarget.lean:Img`, `GTarget`, `GTarget.Rel`, `GTarget.Laws` — the general target: `seg` (from an anchor, along a
  safe J run ending at an anchor, the machine reaches a later anchor of that run), `addi_ok` / `ret_ok` at anchors,
  `entry` (pc 0 is an anchor at offset 0), `off_le` / `vis_link` (return points are anchors and anchors' offsets lie in the code: return addresses do not wrap),
  `vis_ret` / `live_ret` (every `jalr x0, 0(x1)` is an anchor with every J register the return to the host reads related (kept ones, s0, a0, a1); elsewhere `Img.dead pc j`
  exempts dead temporaries from `Rel.x`), `vis_err` (the pair `addi a0, x0, imm; addi a1, x0, 0` and its
  successor are anchors). `gsim` — a safe J run between anchors is a machine run.
* `GUniform.lean:tbytes`, `JTarget.uimg`, `JTarget.toG`, `laws_toG` — a uniform target's code bytes, its image
  (uniform layout, every pc an anchor), and its general laws.
* `HostOn.lean:jOfG`, `rel_entry`, `fin_on`; `HostGen.lean:enter` — J's view of a start state (link layout = the
  image's), a `StartCorrect` state whose code is a valid image's bytes enters `Rel`, the return to the host.
* `HostOk.lean:host_ok`, `HostOom.lean:host_room`, `host_tiny` — the three returns, for an image `I` valid for Gen's
  `Cj`. The stub's `ld ra; ld s0` goes through `gsim` (anchors before and after only), so a target may fuse it.

Design decisions:
* One host lift, over `GTarget`. Rejected: keeping the `JTarget` lift beside it (two proofs of `host_ok` / `host_tiny`
  / `host_room` and the top theorems to keep in step).
* The image is fixed before the J program in `host_*` and `GenOKG` (`∃ I, I.code = gen x ∧ ∀ Cj, … → T.valid Cj I`):
  J's start view needs the image's link layout before `gen_mainN` yields `Cj`. Rejected: `∀ Cj, ∃ I`.
* The anchors the lift needs come from `Laws` by instruction shape (`vis_ret`, `vis_err`), not by position. Rejected:
  "stub pcs 1..10 are anchors" (the start code's size check at `S+4..S+6` is not at a fixed pc).
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

Assumes: `SafeX` J steps (ranges, work cells) from the run layer. Guarantees: `JTarget.Laws.step_ok` (from `steps`;
one safe J step = a machine run keeping `Rel`), hence `GTarget.Laws.seg` for `T.toG`; `host_ok` / `host_tiny` /
`host_room` for any `GTarget` with `Laws` and a valid image.

Known limits: `enc : J → List (BitVec 32)` with `enc_len = blockLen` and `addr = base + 4·blockLen·pc` fix uniform
32-bit-word blocks; `SafeX` carries RV immediate/jump ranges; `Laws.ram ≤ 2^32`. These limits are `JTarget`'s only: `GTarget`
has no word size, block size or `addr` (`SafeX`'s ranges and `ram` remain).

Build / check: `lake build Nano.Run.RvTarget Nano.Run.ArmTarget
Nano.Run.HostOom`, then `Nano.Main.REVIEW` and `Testing/scripts/review_axioms.sh`.
