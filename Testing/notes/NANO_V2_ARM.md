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

### 0-owner. Owner decisions on the ARM machine (2026-11-19, via the lead)
1. **An `arm : Machine` instance in Spec/ is approved**, alongside `riscv`. The lead makes the Spec edit when the
   time comes (as for Spec/Alloc). It can only be added after the Lean 4.35 migration, once the ARM Sail state
   type is importable from this repo.
2. **Code below 2^29 is fine for now** (the `fetch_ok`/`memreadG*`/`memsetG*` bound); expand later.
3. **ARM RAM window: approved; choice below.**

**RAM window (proposal): `[0x1000_0000, 0x2000_0000)` = [2^28, 2^29), 256 MiB.** Why:
* Every fetch/data lemma of `Arm/proofs` requires the address < 2^29 (`Fetch.fetch_ok`, `Mem.memreadG1/G8`,
  `memsetG1/G8`, `full_ldr`/`str`/`ldrb`/`strb`). Below that bound `Fetch.dev_ne` shows that the address misses the
  two device windows of the model (GIC at 0x2C00_0000, UART at 0x3C00_0000), so it is plain memory.
* Translation is the MMU-off path at EL3 (`SCTLR_EL3 = TCR_EL3 = 0`, `s1off_ok`, valid for VA < 2^48), so VA = PA,
  with no alignment faults (`SCTLR_EL3.A = 0`, 8-aligned accesses proved; byte accesses any address).
* Starting at 2^28 instead of 0 keeps address 0 (null) and the low exception-vector area out of the RAM, and
  leaves 256 MiB for code + input + output + work. That is enough for C's own run (the RISC-V run of C on its
  66 KB text uses `spaceC ex1 [5] ≈ 4 MiB` of work, per audit A2).
* **Consequence for the proofs**: the RISC-V proofs use the RAM bounds 2^31 ≤ base, base + len ≤ 2^32 in a few
  places (`RunsDef.GoodU` / `thr`, `ShiftInv`, `gen_runS` premises like `2048 ≤ x12`, `E0 < 2^62`). These become
  parameters `(lo hi : Nat)` of the window (or are stated for both windows). ShiftInv already makes the room
  outcome position-independent, so `Msp`/`spaceC` can stay ONE function of the input for both targets (stated
  per window, then shown equal). A small unit: "window-generic RunsDef".

**Lead decision (2026-11-19): the pins are INLINED into `Spec/Arm.lean` as `CfgArm` (exactly as `Cfg`); Spec stays self-contained, and `Arm/proofs` proves `ArmFull ↔ CfgArm`.**

**Proposed Spec text, mirroring `Spec/Riscv.lean` + `Spec/RiscvMachine.lean`** (owner requirement: same
structure, field names, order and doc-comment style; text only, the lead edits Spec after the migration).
Two files: `Spec/Arm.lean` (≙ `Spec/Riscv.lean`) and `Spec/ArmMachine.lean` (≙ `Spec/RiscvMachine.lean`).
`Spec/Machines.lean` (`armMapping`) already exists.

Line by line:

| # | `Spec/Riscv.lean` (as is) | `Spec/Arm.lean` (proposal) |
|---|---|---|
| 1 | `/- Specification: what it means for RV64 machine code to implement a function, on the Sail model. -/` | `/- Specification: what it means for AArch64 machine code to implement a function, on the Sail ARMv9 model. -/` |
| 2 | `import LeanRV64D` | `import Armv9` |
| 3 | `namespace Proven` | `namespace Proven` (names suffixed `Arm`, so both files can be imported together) |
| 4 | `abbrev St := SequentialState RegisterType trivialChoiceSource` | `abbrev StArm := Armv9.SequentialState Armv9.RegisterType trivialChoiceSource` (the model's state type) |
| 5 | `/-- The control state we fix (Sail reset values): M-mode, hart active, mstatus.MIE = 0 (no interrupts), PMP entries off, …, one PMA region = RAM [0x80000000, 0x100000000) (rwx), … Everything else is arbitrary but must be present. -/` | `/-- The control state we fix: EL3, AArch64, stack pointer SP_EL3, no optional feature (only FEAT_AA64EL0), MMU off (SCTLR_EL3 = TCR_EL3 = MAIR_EL3 = 0), SCR_EL3 = 0, no pending interrupt, debug off, PMU/SPE/BRBE/timers off, 48-bit physical addresses. Everything else is arbitrary but must be present. -/` |
| 6 | `structure Cfg (s : St) : Prop where` | `structure CfgArm (s : StArm) : Prop where` |
| 7 | `priv : … .cur_privilege = some .Machine` | `pstate : ∃ p, s.regs.get? .PSTATE = some p ∧ p.EL = 3#2 ∧ p.nRW = 0#1 ∧ p.SP = 1#1 ∧ p.IL = 0#1` |
| 8 | `misa : … .misa = some 0x8000…` | `feat : s.regs.get? .FeatureImpl = some featV` (only FEAT_AA64EL0) |
| 9 | `mstatus`, `mcountinhibit`, `minstretcfg`, `pmpcfg`, `htif`, `elp`, `mseccfg` (one field per pinned register) | `scr`, `sctlr`, `tcr`, `mair`, `edscr`, `mdccsr`, `oslsr`, `mdcr3`, `mdcr2`, `mdscr`, `dbgen`, `spiden`, `edesr`, `gic`, `mpam3`, `mpam2`, `pa`, `spe`, `emu`, `pmcr`, `cntcr`, `cntp`, `cnthp`, `cntps`, `cntv`, `brbfcr`, `pcount`, `cnthpcv` (one field per pin of `Arm/proofs` `Pins`, same values) |
| 10 | `pma : ∃ a b, … pma_regions = …` (RAM rwx) | — (MMU off: VA = PA; the RAM is the address range, below) |
| 11 | `present : ∀ r ∈ [.PC, .x1, …, .x31, …], s.regs.contains r` | `present : ∀ r ∈ [._PC, .R0, …, .R30, .SP_EL3, .Branchtypetaken, .BTypeNext, .__cycle_count, …], s.regs.contains r` plus the two bookkeeping values of `ArmFull` (`Branchtypetaken ≠ RESET`, `BTypeNext = 0`) |
| 12 | `def Retires (s s' : St)`: `run_hart_active` = `Retire_Success` (no trap) ∧ `try_step … = .ok false s'` | `def RetiresArm (s s' : StArm)`: `stepModel s = .ok () s'` ∧ no exception taken (the exact model predicate is open, see below) |
| 13 | `def Steps : Nat → St → St → Prop` | `def StepsArm : Nat → StArm → StArm → Prop` (same two clauses) |
| 14 | `def runsTo (s : St) (P : St → Prop)` | `def runsToArm (s : StArm) (P : StArm → Prop)` |
| 15 | `def bytesAt (s : St) (a n : Nat) := (List.range n).map (s.mem[a + ·]?)` | `def bytesAtArm (s : StArm) (a n : Nat) := (List.range n).map (s.mem.get? (a + ·))` |
| 16 | `structure Region`, `disjoint` | reused as is (machine-free) |
| 17 | `def Region.inRAM (r) : 0x80000000 ≤ r.base ∧ r.base + r.len ≤ 0x100000000` | `def Region.inRAMArm (r) : 0x10000000 ≤ r.base ∧ r.base + r.len ≤ 0x20000000` |
| 18 | `def unchangedOutside (s s' : St) …` | `def unchangedOutsideArm (s s' : StArm) …` (same body with `mem.get?`) |
| 19 | `def calleeSavedKept (s s')`: x2, x8, x9, x18..x27 | `def calleeSavedKeptArm (s s')`: R19..R29, SP_EL3 (= `armMapping.kept`) |
| 20 | `def codeBytes (code : List (BitVec 32))` (little-endian) | reused as is (AArch64 words are little-endian too) |

| # | `Spec/RiscvMachine.lean` (as is) | `Spec/ArmMachine.lean` (proposal) |
|---|---|---|
| 1 | `/- Sail RV64 model as a Machine. -/` | `/- Sail ARMv9 model as a Machine. -/` |
| 2 | `/-- Integer register by number. -/ def riscvRegister (state : St) (number : Nat)`: 1..31 ↦ .x1…, else none | `/-- Integer register by number: 0..30 = X0..X30, 31 = the stack pointer SP_EL3. -/ def armRegister (state : StArm) (number : Nat)`: 0..30 ↦ .R0…, 31 ↦ .SP_EL3, else none |
| 3 | `/-- Missing values read as zero. -/ def riscvObserve (state : St) : MachineState` (programCounter = .PC, register = riscvRegister, memory = mem) | `/-- Missing values read as zero. -/ def armObserve (state : StArm) : MachineState` (programCounter = ._PC, register = armRegister, memory = mem) |
| 4 | `/-- One retired instruction, else none. -/ noncomputable def riscvStep (state : St) : Option St` | `/-- One retired instruction, else none. -/ noncomputable def armStep (state : StArm) : Option StArm` (`some s'` iff `RetiresArm state s'`, by `match stepModel state`) |
| 5 | `noncomputable def riscv : Machine where` | `noncomputable def arm : Machine where` |
| 6 | `State := St` | `State := StArm` |
| 7 | `step := riscvStep` | `step := armStep` |
| 8 | `observe := riscvObserve` | `observe := armObserve` |
| 9 | `configured := Cfg` | `configured := CfgArm` |
| 10 | `mapping := riscvMapping` | `mapping := armMapping` |
| 11 | `ramStart := 0x80000000` | `ramStart := 0x10000000` |
| 12 | `ramEnd := 0x100000000` | `ramEnd := 0x20000000` |

Open points for the lead's edit: (a) `CfgArm` inlines the pins field by field (as `Cfg` does), so Spec does not
import `Arm/proofs`. `Arm/proofs` then proves `CfgArm s ↔ ArmFull s ∧ sp-select` once. The constants `featV`,
`edscrV` (in `Hooks.lean`) are written out as literals in the Spec. (a') RISC-V's `Retires` excludes traps
(`Retire_Success`). The ARM analogue needs a model-level "no exception taken" condition for `stepModel`, e.g.
PSTATE.EL and the exception syndrome unchanged, or the model's `__exception_taken`-style flag if it has one. To be
fixed against the model source. (b) `ArmFull` is satisfiable (`Arm/Witness.lean`), but cold reset
is not shown to establish it, the same status as RISC-V's `Cfg` (state it in the doc comment). (c) The exact
PSTATE.SP accessor name, from the model.

### 0-adapter. ONE shared machine adapter `JTarget` (owner: "a few small adapters, different only in machine words and register locations")
**Principle.** The Spec side is already generic: `CompileCorrect`/`CompileRuns` take any `M : Machine`
(Spec/Top + Spec/Alloc). The proof side gets one adapter structure `JTarget`, and everything from "J run" to
"CompileCorrect M" is proved ONCE over it. A target supplies only machine words, register locations, and one
step lemma per J instruction kind.

**Reuse of `Compiler/Iface.lean`? No, but copy its shape.** Iface's `Mach.Base` + laws is the middle-layer
interface of the `Exp`/`Stmt`/`Arr` compilers (Arm/apc instantiates it). Its abstraction does not fit J: 15
abstract registers (`Fin 15`), `AOp` without 64-bit `ld/sd`, calls/links (`jal`/`jalr` with link values), or
two-register compare-branches, and its laws are per *abstract operation*, not per *instruction of a fixed
program with a memory relation*. Extending it would change the interface both RISC-V and apc already prove,
for no gain. Kept from Iface: the style (a data record + one law per operation, pure core Lean so it compiles
in any toolchain) and the `instrAt`/`runsTo`/`keep` vocabulary.

**The adapter** (proposal; every field small and named):

```lean
structure JTarget where
  M : Proven.Top.Machine            -- Spec's machine (riscv / arm): states, step, observe, configured, mapping, RAM window
  -- (a) machine words
  blockLen : Nat                    -- words per J instruction (RV 1, ARM 4)
  enc : J → List (BitVec 32)        -- J instruction ↦ its block (length blockLen)
  encOK : J → Prop                  -- which J instructions it can encode (immediate/offset/register ranges)
  -- (b) register locations
  reg : Nat → Nat                   -- J register ↦ target register number in M.observe (RV: id; ARM: π, 0 ↦ xzr)
  scratch : List Nat                -- target registers the blocks may clobber (RV: []; ARM: [16, 17])
  regOK : reg 10 = M.mapping.inputAddress ∧ reg 11 = M.mapping.inputLength ∧ reg 12 = M.mapping.workAddress ∧
          reg 13 = M.mapping.outputAddress ∧ reg 1 = M.mapping.returnAddress ∧ reg 2 = M.mapping.workTop ∧
          reg 10 = M.mapping.status ∧ reg 11 = M.mapping.outputLength ∧ (kept/scratch disjointness, injectivity)
  -- (c) per-instruction steps: ONE law per J kind, against the GENERIC relation `Rel` below
  step_ok : ∀ C base K pc s t j, C[pc]? = some j → encOK j → SafeX K C (pc, s) → Rel this C base K (pc, s) t →
            ∃ t', Runs M t t' ∧ Rel this C base K (step C (pc, s)).get! t'
  -- the only J-level constant that is machine-specific
  W : Nat := 4 * blockLen           -- the link width: `jal` links base + W·(pc+1)  (§0a, V2)
```
`Rel` is defined once, through `M.observe` only (no Sail-specific accessors):
`Rel t (pc, s)` := `M.configured t` ∧ PC = base + W·pc ∧ ∀ r live, `register (reg r) = s.x r` ∧ registers outside
the image of `reg` and `scratch` = their entry values ∧ the code bytes = `(C.map enc)` little-endian ∧ the work/io
bytes = the J cells (`wok`/`io`, as in `RelW.w/bw`) ∧ every other byte = its entry value (`RelW.fr`). That is
SimW's `RelW`, restated through `MachineState`, so it is target-independent.

**Shared, proved once over `t : JTarget`:**
* `sim_star t`: SStarX run ⇒ `Runs t.M` + `Rel` (induction over `step_ok`; today SimX.sim_starX).
* The stubs/start/cap/oom/tiny exits: these are J runs plus `sim_star`. The return to the host is the `jalr 0 1`
  law at the host's ra (with V2 no special case).
* The host lift: `StartCorrect t.M` ⇒ `Rel` at entry (registers via `M.mapping` + `regOK`, code via
  `bytesAt`/observe), and `Rel` at the exits ⇒ the `CompileCorrect`/`CompileRuns` conclusions (PC = ra, status/length
  registers, output bytes, unchanged-outside, kept registers, configured). Today this is HostLift + HostMain +
  CapHost + HostTiny + GenImpl + MainTop's riscv glue + RunsTop (≈ 1,450 lines, all written against Sail-RV
  `St`/`getX`/`riscvObserve`). It becomes ONE generic copy.
* Final theorems: `C_correct_on (t : JTarget) : CompileCorrect t.M (compileC_on t)` and
  `C_runs_on t : CompileRuns t.M (compileC_on t)`, with `compileC_on t s := (compileC s).map (code := encode t ∘
  decodeJ)`. Corollaries: `riscv` (encode rvTarget ∘ decodeJ = id on Gen's output, so it is today's `compileC`)
  and `arm`. Also `self_*_on t` from SrcLink + Cert (machine-free).
* The window (`M.ramStart/ramEnd`) enters only through `Region.inRAM`-style premises. RunsDef/GoodU/gen_runS
  take it as a parameter (the "window-generic RunsDef" unit).

**What cannot be machine-independent, listed as adapter fields**: `blockLen`/`enc` (machine words), `W` (link
width, derived), `reg` + `scratch` (register locations, incl. the zero register), `encOK` (immediate ranges), and
from `M`: `configured` (the Cfg pins), the RAM window, the calling-convention mapping. Nothing else.

**Sizes (estimates).**
| part | lines | lemmas |
|---|---|---|
| shared: `Rel`, `sim_star`, host lift, exits, final `*_on` theorems | ≈ 1,500 (generalizing ≈ 1,450 RV lines) | ≈ 40 |
| J-level refactors: W-parameter (V2) and window parameters | ≈ 300 edited lines in ≈ 25 files | 0 new |
| **adapter `rvTarget`** | ≈ 250: `enc` = `[encG j]`, `reg` = id, and `step_ok` = the existing `sim_*W`/`sim_*X` lemmas restated through `riscvObserve` (one bridge lemma `RelW ↔ Rel`) | ≈ 16 (1 bridge + 14 wrappers + regOK) |
| **adapter `armTarget`** | ≈ 120 for `enc`/`reg`/`regOK`/`encOK`; ≈ 900 for the 14 `step_ok` cases (each a short composition of `Arm/proofs` full steps) | ≈ 20 |
| `Arm/proofs` additions (missing full steps: movn, madd, ubfm, reg ALU ×7, cmp-reg, br, nop) | ≈ 1,200 (BrFull/Mem style) | ≈ 12 |
So the per-machine part is the encoding table, the register map and one step lemma per J kind (≈ 1 kLOC for ARM,
≈ 0.25 kLOC for RV). Everything else (≈ 1.5 kLOC shared + the unchanged J level and semantics, ≈ 400 modules) is
written once. **Wrapping RV costs ≈ 250 lines.** The existing RV host files (HostLift/HostMain/CapHost/
HostTiny/RunsTop glue) are retired once the generic lift reproves `C_correctLO`/`C_runsO` as `rvTarget`
corollaries.

### 0-impl. The generic layer AS BUILT (box E, 2026-11-20; branch nano-v2-src @ 02d3a9c)
`C_correctLO : CompileCorrect riscv compileC` and `C_runsO : CompileRuns riscv compileC` are now corollaries of the
generic theorems. Their statements are unchanged (checked by `rfl` against the old proofs) and their axioms are
unchanged (the 77-axiom Sail extern set). The old RV host chain (HostLift/HostMain/CapHost/HostTiny/GenImpl/RunsThr/
GenStageE/RunsTop/MainTop/MainTopE) is deleted.

**Generic (any target; Sail-free imports; axioms propext/Classical.choice/Quot.sound), 997 lines:**
| file | lines | content |
|---|---|---|
| Machine/JLay | 105 | `LayW`, `wok`/`io`/`bok`/`sok`, `SafeX`, `SStarX` |
| Machine/Target | 133 | `JTarget`, `Rel` (through `observe`), `LayOK`, `Laws`, `sim_star` |
| Machine/HostOn | 117 | `jOfT` (J view of a machine state), `rel_entry`, `fin_on` (the return) |
| Machine/HostGen | 164 | `tbytes T C` (code bytes), `read_some`, `blocks_of`, `enter` (StartCorrect ⇒ layout + Rel), `jregs` |
| Machine/HostOk | 112 | `host_ok` (normal return) |
| Machine/HostOom | 224 | `stub_run`, `host_room`, `host_tiny` (status −1) |
| Main/TopOn | 142 | `compileOn enc`, `EncOK T enc`, **`C_correct_on`**, **`C_runs_on`** |
Plus the following machine-independent splits: Machine/SemCases (`SemCases`, `gen_HD`) and Main/Compile (`SrcC`,
`srcRun`, `spaceC`, `compileC`, `compiler_correctG`, `DBStage`, `spaceC_le`). GenRunS/GenMain no longer import Sail.

**RISC-V adapter, 305 lines:** Machine/RvTarget (187: `rvTarget`, the `RelW ↔ Rel` bridge, `rvLaws`), Machine/RvStep
(67: `sim_ret`, `sim_addiN`, `le4`, `g40_bytes`), Main/RvTop (51: `rv_enc`, `compileOn id = compileC`, the two
corollaries, `C_runs`). Its step lemmas are the existing Sail library SimW/SimX (887 lines).

**What a target supplies** (`JTarget` fields + `Laws`):
* `M`, `blockLen`, `enc : J → List (BitVec 32)`, `reg`, `scratch`, `lay`, `m0`, `inv`, `words`;
* `Laws`:
  * `enc_len` (every block is `blockLen` words);
  * `reg_map` (x1/x2/x10–x13 ↦ the mapping, status = x10, length = x11);
  * `kept_map`;
  * `ram` (2048 ≤ ramStart, ramEnd ≤ 2^32);
  * `lay_init`, `m0_obs`, `inv_init`;
  * **`step_ok`** (one SafeX J step = a machine run; this is the per-instruction-kind work);
  * **`addi_ok`** (addi with the wrapping sum: the stubs' a0 = −1);
  * **`ret_ok`** (`jalr x0, 0(x1)` to any 4-aligned x1);
* `EncOK T enc`: `enc` turns Gen's bytes for its J program `Cj` into `tbytes T Cj`. For ARM, `enc` = decode Gen's
  words, re-encode by `armTarget.enc`. That is the translator, and `EncOK` is its correctness lemma.

**Open for ARM (not adapter work):**
1. **Window:** `C_correct_on`/`C_runs_on` take `hwin : 2^31 ≤ T.M.ramStart`. The cause is that `GoodU`/`thr`/`Msp`,
   `ShiftInv`/`shiftInv`, `no_room`/`lt_room` and `gen_HD`'s use quantify over work positions `hb ≥ 2^31`. ARM's
   window [2^28, 2^29) needs those lowered (e.g. to 2048). This is proof-only work in D's `ShiftInv` area. RV's
   `spaceC` is unchanged if the threshold stays position-independent.
2. **Link width: DONE (7536764).** J's state has `wk` with link width `w = 4·(wk+1)`. `jal` links `b + w·(pc+1)`,
   `jalr` jumps to `(x − b)/w`, and SafeX's jalr condition is `x = base + w·j`. `Rel.ww : wk = blockLen − 1`, so
   `w = 4·blockLen`, the byte size of a block: with blockLen = 4, `bl` as the LAST word of the block links the next
   block (`base + 16·(pc+1)`) and `jalr 0 r` = `br r`, exactly the rv2arm layout (Testing/nano/v2self/arm). RISC-V:
   `wk = 0` (`RelW.ww`), unchanged. `Laws.blk_pos : 0 < blockLen`.
3. **Instruction kinds** for ARM `step_ok` (no Gen change): §3's mapping. slli/srli become `movz x16` + lslv/lsrv,
   negative addi from x0 becomes movz + sub, and padding is `add x16, x16, #0`. Missing Arm/proofs lemmas: reg-ALU ×8
   (incl. madd), cmp-reg, br.

### 0-min. Minimal-instruction plan and route (owner priority, 2026-11-20: "a proof that works on ARM and RISC-V", code quality later)
**Route: the DIRECT Sail route** (lead decision, 23:39). armTarget's `step_ok`/`addi_ok`/`ret_ok` are proved
against the Sail ARM model with one full-step lemma per A64 instruction kind, composed per J block. Each lemma does
its own decode (SymDec-style decode prune), never the whole decoder.
- Only scalar integer instructions are used (no SIMD/FP), so the lemmas can avoid the model's partial `Reduce__1`.
- **Future option:** the DeepMind `Arm64.Step` surrogate plus one final `sim`/`simM` lift to Sail. The probe found it
  saves no main cost: the missing pieces are Sail-side symbolic full steps either way. Revisit it at the 4.35 cleanup.

**Instruction choice = the translator's** (Testing/nano/v2self/arm/PROOF_NOTES.md block table, ArmBlock.lean; 5e49b62 /
aee895b). The block table there IS the proof plan for `armTarget.step_ok`: one row per J kind, giving the A64 block,
its scratch use, NZCV, and the lemmas (existing `full_*` or D's AL1–AL6). The new lemmas are AL1–AL3 (register
add/sub/and/orr/eor/lslv/lsrv), AL4 (subs register), AL5 (madd) and AL6 (br). Nothing uses register field 31:
- x0 operands and stores of x0 go through `movz x17, #0`;
- mul is `madd d, a, b, x17`;
- compares are `subs x16, a, b`;
- RV x2 ↦ x4, and Spec `armMapping.workTop = 4` (1437a980).

**State relation for every row** (generic `JTarget.Rel`, Machine/Target.lean):
- PC = base + 16·pc;
- the block bytes at base + 16·i;
- `X[π j] = s.x j` for 0 < j < 32;
- registers outside π's image and outside scratch [16, 17] keep their entry values;
- the work cells, io bytes and `m0` frame are as in J;
- `wk = 3` (link width 16).
Each row's lemma composition must give `Runs` from `Rel (pc, s)` to `Rel (step C (pc, s))`. Taken branches leave the
block early, and not-taken/fall-through paths run the PADs.

Proof-side constraints on the adapter definitions (O):
- `reg = π` exactly as in ArmBlock.lean, so that `EncOK` holds for the translator's bytes.
- J registers outside π's domain (3, 4, 9, 16..27) are never written by Gen (`keepR`, `dstOk`). They may all map to
  one never-written register, e.g. x18. `Rel.x` then holds because `jOfT` reads them from that register at entry and
  nothing writes it. `reg` need not be injective there.
- `kept_map`: every `armMapping.kept` register (x19..x29, x31) is outside π's image and outside scratch.
- `lay K C` includes the translator's validation (only π-domain registers, ranges, |B| ≤ 262140), so `step_ok` only
  sees encodable programs.

**Fixed up front** (review points):
- NZCV is dead across blocks: only the compare block sets it, and its own `b.cond` consumes it. Rel says nothing
  about NZCV, and `step_ok` for every other kind may clobber it.
- Register 31 never appears as a data register. J x0 ↦ xzr only in ALU/compare operand positions; never as a base
  or add-imm operand.
- `scratch = [16, 17]`.
- The instruction set is derived from the J emitter mechanically: the table above covers every J constructor
  `CallProbe.J` (addi ld sd jal jalr bgeu beq bltu bne alu slli srli lbu sb).
- **Blocking J-level item:** the uniform block plus `br` needs the link-width refactor (§0a V2). Without it,
  blockLen must be 1 (§0-impl item 2).

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
