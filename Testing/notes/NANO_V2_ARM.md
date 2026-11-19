# NANO_V2_ARM: an AArch64 back end for C (design, box E; READ-ONLY phase)

Goal: the owner's statements for an ARM version of C, in `Spec/Alloc.lean`'s form:
`CompileCorrect arm compileC_arm` and `CompileRuns arm compileC_arm` (plus the self-compile instances, as
`SelfC`/`RunsTopO` do for RISC-V). Status: design only. Nothing below is built in the main repo yet.
The measurements were taken on this box, 2026-11-19.

## 0. Decisions so far (lead/owner, 2026-11-19)
* **Design = LIFT the existing proof, not redo it** (§3–§4): a proven instruction-level translation J → AArch64.
  Everything above J is reused unchanged. Only the per-instruction simulation and the host lift to `armMapping`
  are new.
* **Toolchain: both stacks move to Lean 4.35.0** (D is measuring; branch `lean-4.35`). So the ARM model and this
  repo end up in ONE environment. The staging option (A) of §2 is no longer the plan. §2a stays as data on the
  migration's difficulty.
* For now: organization and survey only. No ARM code.

### 0a. Is J abstract enough for the lift?
J (`Machine/Call.lean`) is a small abstract machine: registers `x : Nat → UInt64`, memory as 8-byte cells
`m : Nat → UInt64` (bytes via `lbm`/`sbm`, little-endian), the code base `b`, a `pc : Nat` in instructions.
It is **not** the RV64 Sail semantics: the Sail relation lives in SimW/SimX (`RelW`, `wok`/`io`/`fr`). Everything
above J (EVS, templates, start/cap/oom, `gen_runS`'s J part) talks only about `SStarX`/`SafeX` on J. So a second
target needs exactly a second `RelW`-style relation and per-instruction simulation lemmas, as the lead's plan
says. Two places where J is RV-shaped:
1. **The link value**: `jal rd off` writes `b + 4·(pc+1)`, and `jalr rd rs` jumps to `(x[rs] − b)/4`. The "4" is
   RV's instruction size. Gen's code never does arithmetic on code addresses (the only producer is `jal`'s
   link, saved and reloaded through frames; `epi`'s `jalr 0 14` reloads it). So link values only travel through
   memory. Two ways for ARM, with a fixed block of k = 4 A64 words per J instruction:
   * **V1 (J unchanged): J-shaped return addresses.** ARM computes and stores J's value
     (`adr x30, #(4 − 12·pc)` for `jal 1`) and converts on `jalr 0 r`
     (`adr x17 (= b); sub; add …, lsl #2; br`). The three host returns (stub words 5/10, start 31) become `ret`.
     Memory is byte-identical between J and ARM. Cost: adr/br/add-shifted lemmas and three special-cased indices.
   * **V2 (J parameterized by the link width W):** `jal` links `b + W·(pc+1)`, `jalr` jumps to `(x − b)/W`.
     RV is W = 4 (unchanged results); ARM is W = 16 = 4 words · 4 bytes. Then `bl` as the LAST word of each block
     links exactly `b + 16·(pc+1)`, `jalr 0 r` = `br xr`, and host returns are `ret` with no special case. Cost: a
     mechanical refactor of the J-level files that mention 4·pc or /4: about 25 files, mostly Machine/
     (Templates 12, Call 11, EVXC 9, EVSCall 8, CapRun 8, CallA 6, SimW 5, StartRun 4, EVXT 4, …). The hits in
     Bridge/Own are unrelated divisions.
   **Recommendation: V2** if the 4.35 migration touches these files anyway. Otherwise V1 (no edits above J).
2. **Byte vs cell memory, alignment**: unchanged. AArch64 is little-endian with the MMU off and `SCTLR_EL3.A = 0`
   (no alignment faults), so the `bw`/`w` relation of SimW carries over byte for byte.
3. **x0 = 0 / register count**: RV x0 ↦ `xzr` (31 in ALU/compare encodings). Never as a base register or as
   add-imm source/destination (31 = sp there): the translator emits `movz`/`movn` or `nop` in those cases.

### 0b. Uniform blocks vs a PC map
With a fixed block size (k = 4, nop-padded) the PC map is `pc ↦ 16·pc + base` and branch relocation is ×4. The
simulation is "1 J step = ≤ 4 A64 steps" with no relocation lemma at all. A variable-length expansion
(1–4 words) would save about half the code size but needs a prefix-sum PC map and relocation proofs for every
branch and every link value (and V2 would no longer apply). Ranges with k = 4: Gen caps code at 2^18 J words, so
2^20 A64 words = 4 MB, under the 2^29 fetch bound. `b`/`bl` reach ±128 MB. `b.cond` reaches ±1 MB, i.e. J offsets
< 2^16: IF/loop branches are local; to be checked on C's own output by the translator (fail ⇒ `compileC_arm`
returns `none`).

### 0c. Cost: lift vs a native ARM generator
| | lift (this design) | native ARM Gen in C + per-template proofs |
|---|---|---|
| compiler source | translator (Lean def; later in nano) | a second Gen (`g41_arm`), in nano |
| new proofs | ~12 A64 full-step lemmas, `SimA` + 14 block lemmas, the host lift (~ HostMain/CapHost/HostTiny), top theorems | everything in Machine/Gen redone: word-level Gen proofs (GenRef, Templates, StartCode, g40 bytes), every template's run proof (EVS*, Call*, Loop, Heap), start/cap/oom, plus the same host lift |
| reuse | all of Lex/Parser/Own/Bridge/Cert/SrcLink and the whole J level | only Lex/Parser/Own/Bridge/Cert/SrcLink |
| size estimate | ≈ 60–80 prover-hours (§5) | ≈ the RISC-V Machine/ + Gen/ effort again (76 modules here; weeks) |
| code quality | 4× code size, extra moves | native, smaller |
The lift is far cheaper, as the lead expected. A native generator only pays off if code size or speed of the
ARM output matters.

## 1. Target statement and what the Spec lacks
* `Spec/Machines.lean` has `armMapping` (ra x30, a0..a3 = x0..x3, workTop = 31 (sp), status x0, length x1,
  kept x19..x29, sp). There is **no `arm : Machine`**. `Spec/RiscvMachine.lean` defines `riscv` on the Sail RV64
  model. The ARM analogue must be a new Spec file (**owner**: Spec/ is frozen), e.g. `Spec/ArmMachine.lean`:
  * `State` = the Sail ARMv9 model state.
  * `step s` = `some s'` iff `stepModel s = .ok () s'` (the `elfmain.sail` step, `Arm/proofs/Arm/Step.lean`).
  * `observe`: PC = `_PC`; register n < 31 = `X[n]`; register 31 = `SP_EL3`; memory = the byte map that
    `MemWord` reads.
  * `configured` = the `ArmFull` pins (`Arm/proofs/Arm/Full.lean`: EL3, MMU off, every optional feature off,
    timers/PMU/debug off) **plus** `PSTATE.SP = 1` (so that sp = SP_EL3).
  * `ramStart/ramEnd` must lie below 2^29: `fetch_ok` needs code < 2^29, and the GIC/UART device windows must
    stay outside. The RISC-V RAM is [2^31, 2^32), so **the ARM RAM window is a separate owner decision.**
    It interacts with Gen's address arithmetic: `2^31 ≤ base` is used in the RISC-V proofs (RunsDef's GoodU,
    gen_runS), and those bounds become parameters.
  * `ArmFull` is satisfiable (`Arm/Witness.lean`), but cold reset is NOT shown to establish it (PORT.md). That is
    the same status as RISC-V's `Cfg`.
  This file can only live in the 4.34.1 environment, because it imports the ARM model. `Spec/Top.lean`/`Alloc.lean`
  are model-free and compile in both.
* `compileC_arm`: recommended form `compileC_arm s := (compileC s).map fun c => {c with code := A c.code}`.
  Here `A : List UInt8 → List UInt8` is the **RV → A64 block translator** (§3): decode each 4-byte RV word of
  Gen's output to its J instruction and emit a fixed 4-word A64 block. `memoryNeeded` stays `spaceC` (same work
  layout, same semantics). For self-hosting, `A` is later also written in nano (a C module; compiler source, so
  **owner**), with a Lean equation like the Cert's. Alternative: an ARM Gen inside C (a second `g41`). That costs
  far more, because all Gen word proofs (GenRef/Templates/StartCode) would be redone. Not recommended.

## 2. Existing ARM assets, and the toolchain problem
* `Arm/proofs` (Lean 4.34.1, against the Sail ARMv9 model built in `/home/user/armv9-lean`):
  * full steps (`ArmFull` kept, PC update): `b`, `bl`, `cbz`, `cbnz`, `b.cond` (all 16 conditions, taken/not
    taken), `movz`, `movk`, `add`/`sub` imm, `mov` (orr xzr), `ldrb`, `strb`, `ldr`/`str`/`stur` (8-aligned), `ret`
    (x30).
  * Decode-function + execute only, symbolic registers (Exec.lean): add/sub/and/orr/eor/lslv/lsrv/asrv
    (shifted reg), subs reg/imm (cmp), csinc, csel, movz.
  * `full_gen` (BrFull): any decode+execute result that changes only X, NZCV, SEE and branch bookkeeping is one
    full step.
  * `Words.lean`: 216 *concrete-register* words, about 775 s.
* `Arm/apc` (4.34.1): DeepMind `Arm64` model (Apache-2.0, external clone), the `Iface` machine laws on it, and
  `apc_eq_sail`/`bridge_step`/`sim`/`simM` (runs proved on DeepMind's model, transferred to Sail ARM for the
  bridged words). Symbolic-register ALU on DeepMind (`WideDec`, about 5 min by enumeration).
* **Blocker 1 (environment): `/home/user/armv9-lean` does not exist in this container.** `AGENT_OVERVIEW.md` says
  "never rebuild the ARM model". `Arm/model` is 35 files, 80 MB of generated Lean (DecodeEnd.lean alone is
  37 MB). So nothing ARM can be checked here. Needed: a cloud environment whose setup restores a prebuilt
  `armv9-lean` (the build cache route, as for the RISC-V model), plus toolchain 4.34.1 (`elan` installs it:
  done here in under a minute). **Lead/owner: environment decision.**
* **Blocker 2 (toolchains):** the main repo (Nano, the RISC-V Sail model) is 4.29. The ARM model is 4.34.1. One
  kernel-checked theorem needs one environment. Options:
  * **(A, recommended) stage the machine-independent Nano chain into the 4.34 environment**, like `Arm/apc/stage.sh`
    stages `Riscv/` sources. It needs the chain to be Sail-free and to compile under 4.34.1. Measured:
    * Only **two modules bring the RISC-V Sail model into Nano**: `Proof/Main/Main.lean` (imports
      `Spec.Implements1` for the RISC-V `ImplementsCW`/`Outcome` contract) and `Proof/Machine/Bridge.lean`
      (imports `Nano.V2.Enc`). Through `Main.lean`, the whole Bridge (44/45), Cert (48/51) and Main (9/9) folders
      become Sail-dependent, although their content (`Sem`, `semAt`, `means`, certificates) is model-free.
      **Split `Main.lean` into `Main/Sem.lean` (model-free: Stop, means, Sem, κC, LinearK, the stage Props)
      and `Main/Rv.lean` (Outcome, ImplementsCW, GenStage…).** After that, Lex/Parser/Own/Bridge/Cert/SrcLink and
      the J level are Sail-free. Same for `Machine/SimW` (LayW/wok/sok/SafeX/SStarX are pure; the Sail lift
      lemmas are not): split it into `SimJ` (pure) and `SimW` (Sail).
    * 4.34.1 port of the currently Sail-free part (231 modules): see §2a.
  * (B) Upgrade the whole repo to 4.34.1, including `sail-riscv-lean` (the RISC-V model build at 4.34 is untested;
    owner-level risk; it would touch every proof).
  * (C) Two environments, with the theorem stated in each over shared definitions. This does not give ONE checked
    theorem. Not acceptable as the final form, but usable during development.

### 2a. Measurement: the Sail-free Nano modules under Lean 4.34.1 (data for the 4.35 migration)
Set-up: a scratch lake project with toolchain 4.34.1 and `Nano/` + `Spec/` copied unchanged, building the 231
modules whose import closure has no Sail model. One `lake build`, 232 jobs, 325 s wall on this box (4 cores).
**Result: 105 built, 8 failed, the remaining ~118 not attempted** (they depend on a failed one). The failures:
`Cert.OutSpec`, `Machine.EVXP`, `Parser.ParInv`, `ParLet`, `Parser.ParRunFlat`, `Own.OwnP3`,
`Parser.ParRunWFStep`, `Parser.ParRunCInv`. Every failure seen is an elaboration/`simp` behaviour change (e.g.
EVXP: "Type mismatch: After simplification"), none is a missing feature. The J level (Call, Templates, Expr, Heap,
EV*: 16 of 17) builds unchanged. So the port is many small proof repairs, concentrated in Parser; the true
failure count is only visible after the first 8 are fixed. This is a lower bound for the 4.35 migration (D).

## 3. Mapping: J instructions → A64 blocks
Gen's code is a list of J instructions (`Machine/Call.lean`: addi ld sd jal jalr bgeu alu slli lbu beq bltu srli
bne sb). The RISC-V encoding is 1 word per J. The translator emits a **fixed block of 4 A64 words per J
instruction** (nop-padded), so J index pc ↦ A64 word 4·pc, and J offsets scale by 4 (minus the slot index).
* **Return addresses stay J-shaped.** `jal 1 off` stores ra = b + 4·(pc+1) in J. If ARM stored its real return
  address b + 16·(pc+1), frame memory would differ between J and ARM, and no word-level relation could hold
  (stored ra's are not identifiable). So the A64 block for `jal 1 off` is `adr x30, #(4 − 12·pc); b 4·off−1`
  (x30 := b + 4(pc+1), J's value; `adr` reaches ±1 MB, and pc < 2^18 by Gen's own check). A J return
  `jalr 0 r` becomes `adr x17, #−16·pc` (= b); `sub x16, xr, x17`; `add x16, x17, x16, lsl #2`; `br x16`
  (b + 4·(x_r − b) = the A64 address). The THREE host returns (stub words 5 and 10, start word 31: `jalr 0 1`
  after `ld 1 12 0` reloads the HOST ra) become a plain `ret`. They are at fixed indices (stubs 0..10, start
  S..S+31, S read from word 0). Memory is then **byte-identical** between J and ARM.
* Registers π (RV → A64): x0 ↦ xzr; x1 (ra) ↦ x30; x10..x13 ↦ x0..x3 (armMapping). Gen's RV-kept set
  {3,4,9,18..27} (`NoW.keepR`) maps into x19..x29 (the 11 ARM kept). x2 (sp) is only READ by the start code
  (`srli 31 2 3`) and ↦ sp via `add x16, sp, #0` first. Gen's working registers (5..8, 14, 15, 28..31) ↦ free
  ARM registers. x16/x17 are reserved as scratch. Gen writes only `nk` registers, and rd = 0 ↦ nop.

| J | A64 block (≤ 4 words) | full-step lemma status |
|---|---|---|
| `addi rd rs imm` (|imm| < 2^11) | `add`/`sub xd, xs, #|imm|`; rs = x0: `movz` (imm ≥ 0) / `movn` (imm < 0: the stubs' −1/−2); rs = sp: via x16 | add/sub imm, movz **exist**; **movn missing** |
| `ld rd rs off` | off ∈ 8ℕ, < 32760: `ldr xd, [xs, #off]`; else `add/sub x16, xs, #|off|; ldr xd, [x16]` | ldr (8-aligned) exists; **unaligned/zero-offset `ldr` on x16 to check**; add/sub imm exist |
| `sd rs2 rs1 off` | `str` / `stur` / via x16 | str/stur exist (8-aligned); same check |
| `lbu rd rs off` | `ldrb xd, [xs, #off]` or via x16 | ldrb exists (imm offset form to check) |
| `sb rs2 rs1 off` | `strb` | exists |
| `alu op rd a b` (add sub mul and or sll srl xor) | `add/sub/madd/and/orr/lslv/lsrv/eor xd, xa, xb` (xzr for x0) | decode+exec exist (Exec.lean), **top-level symbolic decode + full step missing** for all 8; **madd missing entirely** |
| `slli/srli rd rs sh` | `ubfm` (lsl/lsr #sh) | **missing** |
| `beq/bne/bltu/bgeu a b o` | `subs xzr, xa, xb` (cmp); `b.eq/ne/lo/hs 4·o − 1` | b.cond full **exists**; **cmp (subs reg) full step missing** (exec exists) |
| `jal 0 off` | `b 4·off` | exists |
| `jal 1 off` | V1: `adr x30, #…; b …` · V2: `nop; nop; nop; bl 4·off−3` | V1: **adr missing** · V2: bl exists |
| `jalr 0 r` (J return/jump) | V1: `adr; sub; add (shifted reg, lsl #2); br` · V2: `br xr` | V1: **adr, add-shifted, br missing** · V2: **br missing** |
| host `jalr 0 1` | `ret` (V1: special-cased index; V2: just `br x30`) | exists (`full_ret`) |
| padding | `nop` (HINT) | **missing** (or pad with `add x16, x16, #0`, which exists) |

Missing A64 lemmas, as `full_*` steps under `ArmFull` with symbolic registers: movn, madd, ubfm (lsl/lsr imm),
reg add/sub/and/orr/eor/lslv/lsrv (SymDec + full_gen around the existing `*_exec`), subs-reg (cmp), adr, br,
add shifted-reg (lsl #2), nop (or use an existing padding instruction). About 12 lemmas, each in the style of
BrFull/Mem.

## 4. Proof plan, mirroring `Proof/Machine` + `Proof/Main`
**Reused unchanged** (once Sail-free and ported, §2): Lex, Parser, Own, Bridge (Sem/semAt/semAtF and the
converses, main_room/main_capR/main_all, shiftInv), Cert, SrcLink. Also Gen's J-level facts: `gen_C`, DefsC,
`defsJ`/`stubJ`/`startJ`, the J programs, and every J-level run theorem (`gen_runS`'s SStarX part, start_runX,
start_capX, the room/cap contracts; RunsDef's Msp/thr/ShiftInv usage), stated on SafeX/SStarX with LayW.
Prerequisite: split `gen_runS`'s conclusion into the J-run part and the Sail `lift` part (currently one clause).
Also the RV-side word facts: `g41 … = g40 … (C.map encG)`, `words_encJX`.

**New:**
1. `A`: the translator (Lean def), plus `decodeRV (encG j) = j` for `GoodX j` (an RV decoder only on Gen's
   encodings), so that `A (mC x) = (C.map blockA).flatten.bytes`.
2. `SimA` (analogue of SimW/SimX): `RelA K (pc, s) t`, where t is an ARM state with `ArmFull`, PC = base + 16·pc,
   `X[π r] = s.x r`, and bytes in work/io = J memory (the same `wok`/`bok`/`sok` predicates, the same `fr` frame).
   One lemma per J instruction kind: "the 4-word block runs in k ≤ 4 full steps from RelA to RelA of `J.step`"
   (the analogue of `sim_*W`), then `sim_starA` (the analogue of `sim_starX`).
3. The ARM host layer (analogue of HostLift/HostMain/CapHost/HostTiny): `StartCorrect arm` ⇒ `RelA` initial
   (registers via armMapping and π; code bytes = `A …` at the PC; `ArmFull` from `configured`). Stub runs with
   `movn` values −1/−2; the four outcomes (ok / cap / OOM / tiny), with OOM leaving the output untouched (the
   olen = 0 layout carries over).
4. Top: `C_correctA : CompileCorrect arm compileC_arm`, `C_runsA : CompileRuns arm compileC_arm` (RunsDef/
   ShiftInv/`spaceC` reused verbatim), `self_correctA_C`/`self_runsA_C` (SrcLink + Cert reused).

## 5. Work units (parallel; estimates are for a strong prover with this repo open)
| id | unit | depends | estimate |
|---|---|---|---|
| A0 | owner: `Spec/ArmMachine.lean` (`arm : Machine`), the RAM window, `compileC_arm` + translator approval | — | owner |
| A1 | env: cloud environment with prebuilt `armv9-lean` + 4.34.1, a stage script (`Arm/nano/stage.sh`) | A0 | 1–2 h (infra) |
| A2 | split `gen_runS`'s conclusion into the J run + a target-generic lift hook; split `Machine/SimW` → `SimJ` (LayW/wok/SafeX/SStarX) + `SimW` (Sail RV) | — | 3–4 h |
| A2b | (V2 only) parameterize J's link width W (`jal`/`jalr`), re-check the ~25 J-level files at W = 4 | — | 4–6 h, splits per folder |
| A3 | (owner decision 2026-11-19) the Lean 4.35.0 migration of both stacks (D) | — | D's measurement |
| A4–A9 | the missing A64 full steps: A4 movn+nop, A5 reg-ALU ×7 (shared SymDec pattern), A6 madd, A7 ubfm lsl/lsr, A8 cmp-reg, A9 adr+br+add-shifted | A1 | 1.5–3 h each, parallel |
| A10 | translator `A` + `decodeRV∘encG` + the block table (Lean) | — | 3 h |
| A11 | `SimA` relation + `sim_starA` skeleton | A1, A10 | 4 h |
| A12–A15 | per-J block lemmas: A12 addi/ld/sd/lbu/sb, A13 alu/slli/srli, A14 branches, A15 jal/jalr (adr/br, host ret) | A4–A11 | 3–5 h each, parallel |
| A16 | ARM host layer (HostLift/HostMain/CapHost/HostTiny analogues) | A11–A15, A3 | 6–8 h |
| A17 | top + self theorems, axioms audit | A16 | 2 h |
| A18 | empirical: run `A (mC X0)` on QEMU-aarch64 / the Sail runner against the RV output (as `Arm/apc/test`) | A10 | 2 h |
| A19 | (later, owner) the translator in nano + Lean equation (self-hosted ARM) | A10 | 6+ h |

Critical path: A0/A1 (owner + environment) → A11 → A12–A15 → A16 → A17. Many units run in parallel. A2, A3 and
A10 can start before the environment exists.
