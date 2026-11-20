# Low-level proof cleanup plan (Nano/V2Self/Proof/{Gen,Machine,Main})

Phase 1 survey (read-only, against origin/main f06eecb4). Paths are relative to `Nano/V2Self/Proof/` and may move
with reorg-nano (to re-check after the merge). Goal: cheap proofs for later optimizations and for a native
ARM `JTarget`. Rules kept throughout: no Spec/ change, no new axioms/sorry/native_decide/bv_decide, REVIEW statements
unchanged, generated code unchanged unless a step says otherwise.

## 0. Layering today

```
Gen (C code g10..g55, emits RV64 words)          Gen/GenRef, GenWidth, GenTop, GenAll   relational spec CG/CT/CGs on raw words
  └ words = templates.map encG                   Machine/NdCG*, ExprExact, MachExact, CallExact
J (RISC-V-shaped IR, CallProbe.J, Call.lean:11)  templates: Expr, Templates, Call/CallA, Heap, Loop
  ├ plain runs  (Star)                           EVX, EVXP, EVXC, EVXF, EVXL, EVXT, HeapEV, ExprEV, NdRun, NdProg, StartRun, GenRun
  ├ safe runs   (SStar/SStarX) — twin layer      SafeRun, EVSDefs, EVSLeaf, EVSComp, EVSFin, EVSTail, EVSLoop, EVSCall, EVSRun, EVSProg, StartSafe, StartAllS, GenRunS
  └ cap/room exits (SStarX) — third copy         RoomRun, CapRun, CapNode, CapProg, CapStart
JTarget (Target.lean) : J step = machine run     RvTarget (blockLen 1), ArmTarget (blockLen 4, rv2arm blocks)
Host lift over any JTarget                       HostOn, HostGen, HostOk, HostOom → Main/TopOn (C_correct_on / C_runs_on)
```
All 98 Gen/Machine/Main modules are reachable from REVIEW + ArmTop (nothing dead there).

## 1. Duplication (measured)

| pattern | where | size |
|---|---|---|
| plain vs Safe twins: 51 name pairs `x`/`xS` (EVH, EVHw, EVHt, DefX, Fin1-3, runV/T/L, defRun, progRun, ifT, letT, loopX, callX, …) | EVX*/NdRun/StartRun vs EVS*/StartSafe | plain ≈3.1k lines, Safe ≈5.1k lines; identical lines: EVXT/EVSTail 244, EVX/EVSComp 201, EVXL/EVSLoop 155, StartRun/StartSafe 149, NdRun/EVSRun 101, EVXC/EVSCall 97 (≈950 verbatim) |
| success vs cap-exit node induction | EVSRun vs CapNode (runV/T/L vs runVCap/TCap/LCap) | 125 identical lines; CapRun repeats each fragment rule (ifCap, letCap, loopCap, callCap, defCap, fin1-3Cap …, 30 thms) |
| three run predicates | `Star` (Call.lean:84, 100 uses), `Safe`/`SStar` (JLay.lean:34,54, 42 uses), `SafeX`/`SStarX` (JLay.lean:58,90, 111 uses) | Safe ⊂ SafeX (`safeX_of`); only SStarX reaches `JT.sim_star` |
| per-leaf OOM proofs | RoomRun: leafRoom, constRoom, lenRoom, localRoom, local1Room, bnewRoom, pro_oom_srun, defCapK | each re-derives `x30/x31` unchanged + `push_oom_srun` + offset arithmetic |
| absolute→relative jump arithmetic `((q:Int)+2 + ((tgt:Int) - ((q:Int)+2))).toNat = tgt` | RoomRun 14, SafeRun 9, Heap 8, Expr 6, CallA 6, Templates 4, NdCGw 4, … | ≈60 sites |
| code-size bound `C.length < 2 ^ 18` threaded by hand | RoomRun 19, CapRun 12, EVSTail 6, + 15 files | 68 sites |
| GenRef register-file boilerplate (`bset s.r 6 …` length/get, `rget … hr0`, `tg_u1`) | GenRef g37_t* item proofs | 15× hl6/h0, 11× h6, 9× hv1, 9× g15 rewrite chain (171 repeated long lines) |
| ARM per-block proofs | ArmTarget (46 repeated long lines, `mid_regs` steps) | moderate |

## 2. Room/OOM and branch offsets today

* OOM ("room") exit: every value push is the checked push `push r o = [addi sp,-8; bgeu sp,t5,+2; jal x0,o; sd r,0(sp)]`
  (Call.lean:158) with `o = tgt − (q+2)` via `pushA tgt q r` (Expr.lean:134), `tgt = 1` (OOM stub word). The cap exit
  (BPUSH on a full buffer) jumps to stub word 6 (`bpush_capS`). Each template proves its exit separately
  (`*Room` in RoomRun, `*Cap` in CapRun), each with its own copy of: register preservation across the prefix,
  offset arithmetic, `SafeX` side conditions (`tgt < C.length`, `C.length < 2^18`, `pc + k < C.length`).
* The outcome (ok / cap / room) is a separate contract per outcome (`EVHwS`, `CapW .room`, `CapW .cap`, `CapT`),
  hence the second node induction in CapNode and the second program induction in CapProg/CapStart.
* Branch offsets: J offsets are in J-instruction units. Conditional branches are fixed short forward skips, hard-coded
  in the generic `SafeX` (JLay.lean:66-68: bgeu ∈ {2,3,4}, beq ∈ {2,7}, bltu = 2, bne = 4); jal is ±2^18
  (RV jal range) and is normalised mod 2^19 (JNorm `jw`/`norm`, GenMainN). Gen computes jal words itself (`g13`, range
  check `g14` = `JOk`, placeholders patched by `g19`/`g20`/`patchR`, Fixup.lean, GenRef ~134 uses).
* Layout: `addr base pc = base + 4·blockLen·pc` (uniform blocks); the link value convention `K.base + s.w·j` (SafeX jalr)
  with `Rel.ww : wk = blockLen − 1`.

### Proposed factored form
1. `Exit` = `{room, cap}` with `Exit.stub : Exit → Nat` (1, 6). One fragment lemma `exit_run`: from a state where a
   template's jal at `q` targets `e.stub`, the SStarX run reaches `(e.stub, s')` with the standard preserved fields
   (m, b, x0, x8, x28, x29) — packaged as a structure `Keeps s s'` (today an anonymous 6-tuple repeated in every
   `hgo`).
2. `checkedPush_room`: `pre ++ pushA 1 q r` where `pre` is an SStarX run with `Keeps` and x30/x31 unchanged ⇒
   `CapW .room`. constRoom/lenRoom/localRoom/local1Room/bnewRoom become instances (one line each).
3. Offsets: `relTo (tgt q : Nat) : Int := tgt − q` with `@[simp] q + relTo tgt q = tgt` and `jalTo tgt q : J`;
   templates written with `jalTo` instead of raw `(tgt:Int) − (q+2)`. Bundle code-size facts once:
   `structure CodeOK (C) : Prop := (len18 : C.length < 2^18) (stubs : 6 < C.length)` passed as one hypothesis.
4. One outcome-indexed contract `EVHwO (o : Outcome)` (ok carries the value/heap post, cap/room carry the stub pc)
   so the node and program inductions are done once (merges EVSRun+CapNode, EVSProg+CapProg, StartAllS+CapStart).

## 3. Target interface: what is RISC-V-specific, what a native ARM JTarget supplies

A native ARM JTarget supplies the same fields as `armTarget` (M with `A64Sem`, `blockLen`, `enc`, `reg`, `scratch`,
`lay`, `m0`, `inv`, `loader`) and `Laws` (step_ok per J kind, addi_ok, ret_ok, inv_init, lay_init, m0_obs, kept_map,
reg_map, ram). If native Gen emits exactly one fixed-size ARM block per J instruction, `armTarget` and its 1138-line
law proof are reused unchanged; the only new proof is "native Gen's bytes = `tbytes T Cj`".

RISC-V-specific in the current generic layer:
* `EncOK T enc` (Main/TopOn.lean:17): code is `enc` applied to Gen's **RV bytes** (`g40 … (Cj.map encG)`); a native
  generator cannot be expressed except as a post-translator of RV output. → replace by `GenOK T gen` quantifying over
  the J program (`gen x = tbytes T Cj ∧ T.valid Cj` for the Cj with Gen's facts); RV: `gen = mC`; rv2arm:
  `gen = enc ∘ mC` (one lemma from today's `EncOK`).
* `JTarget.words` / `LayW.W` (Target.lean:38): RV's code words; ARM fills it with `C.map fun _ => 0`. → move into
  `rvTarget.lay`/`inv` (target-private).
* Generic `SafeX`: imm ±2048 (RV I-type), jal ±2^18 (RV J-type), fixed branch skips — these are J-language limits
  inherited from RV encodings. Keep them as J's limits but name them (`JImm`, `JFar`, `JSkip`) so a target can state
  its own weaker requirement; low priority.
* `Laws.addi_ok` (imm ±2048), `Laws.ret_ok` (`jalr x0, 0(x1)`), `reg_map` (x1/x2/x10–x13): J's ABI, acceptable.
* `Laws.ram : ramEnd ≤ 2^32` and `hwin : 2^31 ≤ ramStart` (TopOn run_ok): from RV address materialisation (li) and
  D's position lemmas; for ARM they come from A64Sem.ram. Acceptable, document.
* `Laws.step_ok` is one monolithic obligation; adding a J instruction (optimizations) breaks every target proof at
  once. → split into per-constructor laws (`StepLaws` structure with one field per J kind) — new J instruction = one
  new field per target.
* Gen itself is RV-specific (encoders g1–g5/g10–g13, jal range check g14, patching g19/g20). GenRef's CG is over raw
  RV words (`em (fun o => g21 (g23 o 5 …))`). For a native Gen with different encoders, CG must be factored as
  "C's emitter calls = template instructions" + "encoder = target `enc`" (§4 step 9).

## 4. Ranked steps (effort: S ≤ ½ session, M ≈ 1 session, L = 2–4 sessions)

| # | step | files | effort | risk | payoff |
|---|---|---|---|---|---|
| 1 | GenRef boilerplate lemmas (`r6set` length/get bundle, `hv1`/tg_u1, g15 rewrite chain) | Gen/GenRef | S | low | −150 lines, easier Gen edits |
| 2 | `relTo`/`jalTo` + `CodeOK` bundle; rewrite the ≈60 offset sites and 68 `2^18` sites | Expr, Templates, CallA, Heap, SafeRun, RoomRun, CapRun, EVS* | M | low (statement-internal only) | every new template's jumps |
| 3 | `Keeps` structure + `exit_run` + `checkedPush_room`; RoomRun leaves as instances; `bpush_capS` via `exit_run` | RoomRun, CapRun, EVSLeaf | M | low | room/cap handling in one place |
| 4 | retire `Safe`/`SStar` in favour of `SafeX`/`SStarX` (`safeX_of` already exists) | JLay, SafeRun, RoomRun, SimW | M | low-med | one safe-run predicate |
| 5 | collapse plain/Safe twins: state EVH/EVHw/EVHt/DefX with SStarX, delete the plain EVX*/NdRun/NdProg/StartRun/GenRun proofs (to verify first: whether any plain result is used other than through toEVH/ofEVH), rename S→plain | EVX*, EVS*, NdRun, NdProg, StartRun/Safe, GenRun/S, HeapEV, ExprEV | L | medium (large diff, long builds; theorems only internal) | ≈ −3k lines; templates proved once |
| 6 | outcome-indexed contract; merge EVSRun+CapNode, EVSProg+CapProg, StartAllS+CapStart | EVS*, Cap* | L | medium | one node induction; new node kinds cost once |
| 7 | `GenOK` replaces `EncOK` (keep `EncOK → GenOK` so ArmTop/apc/sail statements stay) | Main/TopOn, ArmTop, RvTop | S | low | native generator pluggable |
| 8 | `StepLaws` per J constructor; `words`/`LayW.W` made target-private | Target, RvTarget, ArmTarget, HostGen, SimW/SimX | M | medium (touches both targets) | adding J instructions / targets cheap |
| 9 | factor GenRef CG over an abstract emitter (words = `enc` of template instructions, jump offsets in J units, range check abstracted) | Gen/*, NdCG*, ExprExact, MachExact, CallExact, Bridge | L+ | high (core Gen proof) | prerequisite for a native Gen with its own encoders |

Order: 1 → 2 → 3 → 4 (cheap, independent, each its own PR) → 7 (small interface PR) → 5 → 6 → 8 → 9.
Milestones (full `lake build`, REVIEW + review_axioms.sh, Arm/apc ArmDMTop/AxiomsDM, Arm/sail ArmSail): after 4, 5, 6, 8.
No step changes generated code; step 9 should not either (Gen's C source unchanged; only its proof factored).

Native-ARM recommendation: first native backend = Gen emitting `ArmEnc.blk` per J instruction (blockLen 4, uniform
layout, offsets ×4 words) — reuses armTarget; needs steps 7 + 9. ARM-specific template optimizations (fused
compare-branch, wider immediates) are then added as new J instructions (step 8 makes that one law per target)
rather than as non-uniform blocks; non-uniform `addr` is not recommended now.
