# Proof/Machine

## Target interface and adapters (`Target.lean`, `RvTarget.lean`, `ArmTarget.lean`, `Host*.lean`)

What it does: states once what a machine must provide for Gen's J programs to run on it (`JT.JTarget` + `Laws`),
and lifts the J-level run theorems to any such machine (`HostOn`, `HostGen`, `HostOk`, `HostOom`). Fed by the J runs
(`SStarX`, EVS*/Cap*); used by `Main/TopOn.lean` (`C_correct_on`, `C_runs_on`).

* `JLay.lean:LayW` — the generic layout: code base, work cells, input/output bytes, entry memory. No code words.
* `Target.lean:JTarget` — machine `M`, `blockLen`, `enc` (words of one J instruction), `reg`, `scratch`,
  `lay : LayW → List J → Prop`, `m0`, `inv : LayW → List J → M.State → Prop`, `valid`, `loader`.
* `Target.lean:JTarget.Rel` — J state ↔ machine state through `observe`; `Laws` — what a target proves
  (`step_ok`, `addi_ok`, `ret_ok`, `lay_init`, `inv_init`, `m0_obs`, `reg_map`, `kept_map`, `ram`).
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

Assumes: `SafeX` J steps (ranges, work cells) from the run layer. Guarantees: `Laws.step_ok` (one safe J step = a
machine run keeping `Rel`), hence `host_ok` / `host_tiny` / `host_room` for `tbytes T Cj`.

Known limits: `enc : J → List (BitVec 32)` with `enc_len = blockLen` and `addr = base + 4·blockLen·pc` fix uniform
32-bit-word blocks; `SafeX` carries RV immediate/jump ranges; `Laws.ram ≤ 2^32`. A variable-length target (x86-64)
needs these generalised (not done here).

Build / check: `lake build Nano.V2Self.Proof.Machine.RvTarget Nano.V2Self.Proof.Machine.ArmTarget
Nano.V2Self.Proof.Machine.HostOom`, then `Nano.V2Self.REVIEW` and `Testing/scripts/review_axioms.sh`.
