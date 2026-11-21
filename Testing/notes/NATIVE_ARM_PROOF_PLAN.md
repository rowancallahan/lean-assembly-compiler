# Native AArch64 back end: proof plan (no proofs started)

Subject: `C/GenArm.lean` (`a31`), prototype tested in `Testing/nano/v2self/native_arm/README.md`. Goal statement:
`CompileCorrectP armDM (ArmLoader XD WD) compileA` with `compileA x = a31 x (o41 (y16 (s10 x)))` (DeepMind ARM
first, owner), then `CompileCorrect armSail …` from the same generic proof over `A64Sem`. Lex/Parse/Own proofs and
the width pass `g53` are reused unchanged; only the code-generation half is new.

## Why the existing ARM proof does not apply directly
`armTarget` (Proof/Machine/ArmTarget.lean) is a `JTarget` with uniform blocks: every J instruction is 4 A64 words, so
`addr base pc = base + 16·pc` (Target.lean:49) and the J link value `b + w·(pc+1)` (Call.lean:37, `Rel.ww`) is the
real A64 return address. GenArm is emitted per **template**, not per J instruction (push = 4 J → 4 A64 with the
`bgeu; jal` pair fused into `subs; b.lo`; IF compare 5 J → 4 A64; LOOP head 3 → 2; constants 1–17 → 1–4), so:
1. the code map is non-uniform: a monotone `π : J index → A64 word index`, defined at template boundaries;
2. stored return addresses (frame slot `[s0+8]`, register x30/x14) are A64 addresses `base + 4·π(j)`, not `b + w·j`,
   so `Rel.w` (memory equal byte for byte) fails on exactly those cells;
3. one J step is not one A64 block: `Laws.step_ok` (one monolithic per-J-step obligation) cannot be met.

## Plan (recommended: template-level simulation, reuse the J-level node proofs)
| # | step | what | effort |
|---|---|---|---|
| A | A64Sem extensions | new fields: `movn`, `cbnz`, `ldur`, `stur`, `ldp`, `ldrbR` (register offset), `addLsl3` (add shifted reg); first CHECK the DeepMind model decodes/executes all seven (Sail ARM: all present in Arm/model Instrs64). Prove for DM (`Arm/apc/Blocks/A64DM.lean` style, existing F_* lemmas are 15–40 lines each) | 1–2 sessions DM; Sail later 1–2 |
| B | per-template A64 lemmas | one lemma per Gen template kind (push, pop-two, 8 binops, 9 prims, li via movz/movn/movk, slot load/store in 3 offset forms, IF compare, LOOP head/step, CONTINUE, call, def header, epilogue, exit jumps, stubs, start code): straight-line compositions of A64Sem fields, stated as "J template run (pc,st)→(pc',st') ⇒ A64 run s→s' with RelA" | 2–3 sessions |
| C | link-value abstraction in J | replace the literal `b + w·(pc+1)` by a layout function `ℓ : Nat → Nat` (RV: linear, rv2arm: linear, native: `base + 4·π`); the J proofs only need "jalr to ℓ(j) lands at j", no arithmetic on links (Gen does none) | 1–2 sessions, touches Call/SafeRun/EVSCall |
| D | non-uniform layout in the generic layer | `JTarget.addr` from a per-program `π`; `Rel.code` per template; a template-level law `tmpl_ok` (or per-J-kind `StepLaws` plus fused-pair laws for `bgeu;jal`, `beq;jal`) instead of `step_ok` | 2–3 sessions |
| E | lockstep Gen ↔ GenArm | `a29` and `g39` run the same work-item sequence on the same AST; the RV-coordinate positions in `k`/`t`/`f`/`r[3]` map by `π` to GenArm's; GenArm's output = concat of A64 templates. Needs the abstract-emitter factoring of GenRef (CLEANUP step 9) | 3–5 sessions |
| F | top theorem | `C_correct_on` instance for the native target + `GenOK` (CLEANUP step 7), DM statement as `C_correct_armDM` | 1 session |

Total ≈ 10–15 sessions, after CLEANUP steps 5–9. Order: A (independent, can start now on DM), B (needs only A64Sem),
then C → D → E → F (need the cleaned-up generic layer).

## Status
* A (DeepMind): DONE. `Proof/Machine/A64SemN.lean` (`A64SemN` = `A64Sem` + the 7 forms, a separate structure so the
  rv2arm instances `a64DM` / `a64Sail` are untouched); `Arm/apc/Blocks/A64DMN.lean` (`a64DMN : A64SemN armDM XD WD`,
  axioms propext / Classical.choice / Quot.sound, `Blocks/AxiomsDMN.lean`). The DeepMind model decodes all seven.
  Side conditions found: `ldp` needs `t ≠ u` (the model rejects equal load targets); `ldur`/`stur`/`ldp` are stated
  with 8-aligned addresses like `ldr`/`str`. Sail ARM instance of `A64SemN`: not started.

* C (link values): DONE on branch `link-layout` (38504ff): `CallProbe.St.wk` → `St.ly : LinkLay` (off / un / inv),
  jal links `b + lo (pc+1)`, the global bound became `LinkOK C s` (per return point). REVIEW pinned axioms unchanged.
* D (general layout layer): `Proof/Machine/GTarget.lean`: `Img` (code bytes, `ly`, anchors `vis`), `GTarget.Rel` at
  anchors only, segment law `Laws.seg`, `gsim`; every uniform `JTarget` embeds (`toG`, `rel_toG`, `laws_toG`).
  Host*/TopOn over GTarget: in progress (FABLE-M2, branch m2-host; agreed extra laws `off_le` (anchors), `vis_link`,
  `vis_ret`, `vis_err`, and `Img.dead` = J registers not related at an anchor).
* B (per-template lemmas, GenArm pinned at native-arm d6db803): the J ↔ A64 correspondence of all 15 template kinds
  is in `Testing/notes/NATIVE_ARM_TEMPLATES.md` (written from the sources, not machine-checked).
  `Proof/Machine/ArmNat.lean`: `NMid` (machine state at an absolute code word index vs a register/memory view) and
  the single-instruction steps from `A64SemN` (movz, movn, movk, add/sub imm, add lsl 3 → x16, alu, cbz, cbnz,
  subs+b.cond, b, bl, br, ldr, str, ldur, stur, ldp, 8-byte store). `Proof/Machine/ArmNatTm.lean`: templates done:
  push, pop-two, BIN (all ops, mul via movz x17 + madd), RD. TODO: strb + byte store, li (movz/movn/movk chunk
  walk `a7`), slot access `a9` (3 forms), LOCAL, pop-into-slots, prims (ISIZE/LEN, RD, BNEW, BSIZE, BGET, BSET,
  BPUSH/PUT), IF head, LOOP head/step/exit/CONTINUE, call, prologue, epilogue, stubs, start code; then the native
  `GTarget` instance (image + anchors from the template list) and its `seg` law from these lemmas and the J template
  runs.
* Findings: after BGET/BSET the J temporaries t0/t1 differ from x5/x6 (dead at the boundary; hence `Img.dead`);
  start code is 34 A64 words for 32 J instructions; li is 1..4 words, slot access 1 or 2 words (locals ≥ 33).

## What in the current interface blocks it (cross-ref Testing/notes/CLEANUP_PLAN.md)
* step 7 `EncOK`: code must be `enc` of Gen's RV bytes → native generator not expressible. Needed (F).
* step 9 GenRef's `CG` over raw RV words: needed for E (lockstep), the largest item.
* step 8 `StepLaws` per J constructor: needed for D, but not sufficient (non-uniform `addr`, fused pairs).
* not in CLEANUP: uniform `addr`, `Rel.ww`/link value `b + w·(pc+1)`, `Rel.w` on return-address cells (C, D).
* `Laws.ram : ramEnd ≤ 2^32` and the ±1 MiB jump range: unchanged (GenArm keeps Gen's `g14` and 2^18-word limit).

## Cheaper fallback (not recommended)
Uniform native blocks (CLEANUP's recommendation: one fixed-size A64 block per J instruction) reuse `armTarget`
unchanged and need only steps 7 + 9 + "bytes = tbytes T Cj" (≈ 4–6 sessions), but keep ~2–4× the code of RISC-V,
i.e. most of rv2arm's cost. A middle way: drop GenArm's 7 extra instruction forms (≈ +10% code: ldp → 2 ldr,
ldur → sub+ldr, cbnz → cbz+b, movn → movz+movk) to skip step A; B–F stay.

## Risks
* DeepMind model coverage of the 7 new forms (unchecked); ldp/ldur alignment and permission side conditions.
* E is GenRef-sized; GenArm must stay in lockstep with Gen (any Gen change → GenArm change).
* Accept set: GenArm applies the 2^18-word limit to A64 words, so in principle a program near the limit is accepted
  by one back end and rejected by the other (never seen; native code is smaller). The theorem is per back end, so this
  is not a proof obstacle, only a documented difference.
