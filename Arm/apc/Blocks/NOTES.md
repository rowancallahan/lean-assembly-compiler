# `Arm/apc/Blocks`: rv2arm's A64 forms on DeepMind's `Arm64.Step` (interim target; the final theorem stays on Sail)

Lean 4.34.1, `lake build Blocks.Axioms` (from `Arm/apc`; DeepMind `arm64` at b0f729a as in `../README.md`).
All lemmas: axioms `propext, Classical.choice, Quot.sound` (`lake env lean Blocks/Axioms.lean`). No `sorry`,
`native_decide`, `bv_decide` (`bv_omega` twice, in `add_res12`).

## Shape (chosen so a Sail lemma can replace each one)

Sail `full_X` (`Arm/proofs/Arm/{BrFull,Mem}.lean`):
`hK : w &&& K = C`, field premises `(Sail.BitVec.slice w i n).toNat < 31`, state premises `ArmFull s`, `Abs s a`,
PC, `MemWord`; conclusion `∃ s', stepModel s = .ok () s' ∧ Abs s' (effect a) ∧ ArmFull s' ∧ PC' ∧ s'.mem = …`.

DeepMind `dm_X` (here): the same `hK` and field premises with `w.extractLsb' i n` (`Sail.BitVec.slice w i n =
w.extractLsb' i n` is `rfl`, `BridgeBr.sl_ext`), state premise `At t w` (running, PC 4-aligned, executable, `read32 =
w`; = DeepMind half of `BridgeBr.WordAt`); conclusion `∃ t', Arm64.Step Pg t t' ∧ abs t' = effect (abs t) ∧
Post t t' pc' mem'` (`Post` = running, PC, memory, sp unchanged). `abs` = `Apc/Agree.lean` (x0..x30 + NZCV as the
small machine's `AState`, the same type Sail's `Abs` uses). `effect` is written with the SAME expression as the Sail
lemma (or as `armStep` where no Sail lemma exists yet), so a bridge is: run both, `sl_ext`, done.

## Lemmas

| form (mask) | DeepMind lemma | file | Sail lemma | bridged today |
|---|---|---|---|---|
| movz `0xFF800000/0xD2800000` | `dm_movz` | Imm | `full_movz` | `br_movz` (template words) |
| movk `0xFF800000/0xF2800000` | `dm_movk` | Imm | `full_movk` | `br_movk` |
| add imm `0xFFC00000/0x91000000` | `dm_addi` | Imm | `full_addi` | `br_addi` |
| sub imm `0xFFC00000/0xD1000000` | `dm_subi` | Imm | `full_subi` | `br_subi` |
| add reg `0xFFE0FC00/0x8B000000` | `dm_addR` | Reg | AL1 draft (not Lean); `full_word` for the 21 fixed `emitted` words | `br_emitted` (fixed regs only) |
| sub reg `…/0xCB000000` | `dm_subR` | Reg | AL1 draft | `br_emitted` (fixed) |
| subs reg `…/0xEB000000` (NZCV) | `dm_subsR` | Reg | AL4 draft | `br_emitted` (fixed, `cmp` only: Rd = 31) |
| and/orr/eor reg `…/0x8A/0xAA/0xCA000000` | `dm_andR`, `dm_orrR`, `dm_eorR` | Reg | AL2 draft; `full_mov` (orr from xzr — not emitted any more) | `br_emitted` (fixed) |
| lslv/lsrv `…/0x9AC02000/0x9AC02400` | `dm_lslv`, `dm_lsrv` | Reg | AL3 draft | `br_emitted` (fixed) |
| madd `0xFFE08000/0x9B000000` | `dm_madd` | Reg | AL5 draft | no |
| b `0xFC000000/0x14000000` | `dm_b` | Branch | `full_b` | `br_b` |
| bl `0xFC000000/0x94000000` | `dm_bl` | Branch | `full_bl` | `br_bl` |
| b.cond `0xFF000010/0x54000000` (all 16 codes) | `dm_bc` (+ `cond_abs`) | Branch | `full_bc` | `br_bc` (6 codes; `cond_agree` covers 16, only `dec_bcsym` was restricted) |
| cbz `0xFF000000/0xB4000000` | `dm_cbz` | Branch | `full_cbz` | `br_cbz` |
| br `0xFFFFFC1F/0xD61F0000` | `dm_br` | Branch | AL6 draft (`full_ret` is the x30 case) | `br_ret` (x30 only) |
| ldr `[xn,#8·imm]` `0xFFC00000/0xF9400000` (`[x16]` = imm 0) | `dm_ldr` | Mem | `full_ldr` | no |
| str `0xFFC00000/0xF9000000` | `dm_str` | Mem | `full_str` | no |
| ldrb `0xFFC00000/0x39400000` | `dm_ldrb` | Mem | `full_ldrb` | `br_ldrb` |
| strb `0xFFC00000/0x39000000` | `dm_strb` | Mem | `full_strb` | `br_strb` |

## Bridge lemmas needed to transfer (DeepMind step = Sail step, per form; `Rel`, `MemRel` of `BridgeBr`/`BridgeMem`)

Already exist (`BridgeBr.lean`, `BridgeMem.lean`, `Bridge.lean`), stated on template words (`movW …`, `aiW …`):
`br_b`, `br_bl`, `br_cbz`, `br_bc` (6 codes), `br_ret`, `br_movz`, `br_movk`, `br_addi`, `br_subi`, `br_mov`,
`br_ldrb`, `br_strb`, `br_emitted`/`apc_eq_sail` (216 fixed words), `bridge_step`, `sim`, `simM`.
Re-statable from `dm_*` + `full_*` in mask form in a few lines each (the effects are syntactically equal after
`sl_ext`; offsets by `sx2`, conditions by `cond_agree`/`cond_abs`).

Needed, Sail side missing (Lean `full_*` lemmas for the AL drafts): add/sub/and/orr/eor/lslv/lsrv/subs with
symbolic registers (AL1–AL4), madd (AL5), br (AL6). Once these exist each bridge is the same few lines.

Needed, Sail side exists, bridge missing: `ldr`/`str` 8-byte (`full_ldr`/`full_str` vs `dm_ldr`/`dm_str`): needs
DeepMind `read64`/`write64` against `MemRel` (8 bytes; `Apc/Mem8.lean` has the byte view) and Sail's 8-alignment
(`hA8`), which rv2arm guarantees (PROOF_NOTES: ea % 8 = 0). `br_bc` for all 16 codes: replace `dec_bcsym` by
`dec_bcW` (here).

Memory premises differ: Sail needs address `< 2^29` (and `% 8 = 0` for 8 bytes) and the bytes present; DeepMind needs
`canRead`/`canWrite`. `MemRel` (readable/writable DeepMind bytes lie below `2^29` and agree with Sail) turns the
DeepMind premise into the Sail one; alignment must come from the block invariant.

## Block correctness (`Frame.lean`, `Block.lean`, `K*.lean`)

`ArmBlockDefs.lean` = verbatim copy of ArmBlock's definitions (`check_copy.sh`). `RelD C D K (pc, s) t` = ArmBlock's
`RelA` on DeepMind's state (`abs` for registers, `Memory.canExec`/`read32` for code, `canRead`/`canWrite`/`read8` for
the cells of `D`; x16/x17/NZCV free; x18..x29 and sp kept). `blk_<kind>`: `C[pc]? = some j`, `validJ`, `RelD` at
`(pc, s)` ⟹ `Reach t (RelD … (J's next state))` in ≤ 4 DeepMind steps.

**Statement fixes (found here, applied upstream in `ArmBlock.lean` by the lead: df4e635, b400ca6).** The first draft
of `BlockOK` was false for `addi` when `x[rs] + imm ∉ [0, 2^64)` (J's `ea` clamps with `Int.toNat`; the block wraps:
`addi rd x0 -1` is 0 in J, 2^64 − 1 on A64); `AccOK` now carries `NoWrap` for addi/ld/sd/lbu/sb (the wrapping addi
is `JTarget.addi_ok`). `validJ` did not bound `jal`'s offset (b/bl reach ±2^23 J instructions); it now does.

| J kind | theorem | status |
|---|---|---|
| addi (rd = 0: 4 PAD; rs = 0: movz; add/sub imm) | `blk_addi` | proved |
| alu (8 ops; `movz x17, #0` first for an x0 operand or mul; `madd …, x17`) | `blk_alu` (+ `alu_word`) | proved |
| slli / srli (`[movz x17, #0]`, `movz x16, #sh`, `lslv`/`lsrv`) | `blk_slli`, `blk_srli` (`blk_shift`) | proved |
| beq (x0,x0: `b`; one x0: `cbz`; else `subs x16; b.eq`) | `blk_beq` (`b_blk`, `cbz_blk`, `blk_cmp`, `cmp_tail`) | proved |
| bne / bltu / bgeu (`subs x16; b.ne/lo/hs`, x17 prefix for x0) | `blk_bne`, `blk_bltu`, `blk_bgeu` | proved |
| jal x0 (`b`) / jal x1 (3 PAD, `bl`) | `blk_jal` | proved, extra premise `-2^23 < o < 2^23` |
| jalr x0, rs (`br`) | `blk_jalr` | proved, premise = ArmBlock's `AccOK` for jalr |
| ld (`ldr [xn, #off]` or `add/sub x16; ldr [x16]`) | `blk_ld` | proved; premises `AccOK` (cell in D), `0 ≤ x[rs] + off` |
| sd (same forms; x0 stored from x17 after `movz x17, #0`) | `blk_sd` | proved; same premises. Stores keep the code: `CodeOK.w8` (DeepMind's `canWrite` = w ∧ ¬x) |
| lbu (`ldrb [xn, #off]` or via x16) | `blk_lbu` (`lb_eq`: byte lane = J's `lbm`) | proved |
| sb (`strb`, x0 via x17) | `blk_sb` (`sb_byte`, `memOK_w8`: = J's `sbm`) | proved |

**`blockOKD : BlockOKD`** (`BlockOK.lean`): ArmBlock's `BlockOK` verbatim in its premises (`C[pc]? = some j`,
`validJ`, `s.wk = 3`, `AccOK`), with `RelD` for `RelA` and DeepMind steps (`Reach`, ≤ 4) for `Runs`, all 14 J kinds.
`lake build Blocks.Axioms`: 37 s from clean Blocks oleans (4 cores); 37 theorems, axioms `propext, Classical.choice,
Quot.sound`.

### Transfer to Sail

`blockOKD` uses each DeepMind form lemma only through its `dm_*` statement (word mask + fields → `abs` effect +
`Post`). To get BlockOK on Sail: (1) the Sail `full_*` for every form (missing: symbolic-register AL1–AL6:
add/sub/and/orr/eor/lslv/lsrv/subs reg, madd, br); (2) restate `RelD` on Sail (`Abs`/`ArmFull`, Sail memory map
for `CodeOK`/`MemOK`) and replay `Frame`/`Block`/`K*` with `full_*` for `dm_*` (the block arithmetic — encodings
`mask32`/`fldt`, offsets `ofs19`/`ofs26`, register map, byte lanes `lb_eq`/`sb_byte` — is model-independent and
carries over unchanged); or (3) keep DeepMind and compose with per-form bridges (`sim`/`simM` style) — needs the
same missing `full_*` plus `ldr`/`str` bridges.

## `armDM` and `A64Sem` (2026-11-20; `ArmDM.lean`, `A64DM.lean`, `A64Inst.lean`)

`armDM : Proven.Top.Machine` (outside `Spec/`): `step` = DeepMind fetch/decode/eval as a function while `Running`
(`stepDM_of`: a running `Arm64.Step Pg` is an `armDM` step; `Pg` has no extern hooks); `observe` = pc, x0..x30,
register 31 = sp, mapped bytes (`read8`); `configured` = `Running`; `mapping = armMapping`; RAM `[2^31, 3·2^30)`.
Permissions for `A64Sem`'s W^X split: `XD s a` = byte executable, `WD s a` = readable ∧ writable.

Per-form fields, in `A64Sem`'s exact statement (`GoesK`, `FetchX`, `PcOK`): `F_movz`, `F_movk`, `F_addi`,
`F_subi`, `F_alu` (8 ops, madd with general x17), `F_cmpbr` (subs + b.cond, two steps), `F_cbz`, `F_b`, `F_bl`,
`F_br`, `F_ldr`, `F_str`, `F_ldrb`, `F_strb` (stores: observed memory = `store8`/`store1`, permissions kept).
`a64DM : A64Sem armDM XD WD` (`A64Inst.lean`), against the real `Nano/Run/A64Sem.lean` (its closure
builds on 4.34.1 since 12ddcd53; the earlier verbatim copy is gone). The loader layout is the per-start-state
`JT.ArmLoader XD WD`, the premise of `CompileCorrectP` / `CompileRunsP` (it replaced f8e28ee's `JT.LoaderPerm`), not a field.

**Top theorems** (`ArmDMTop.lean`, E's 37939cd): `C_correct_armDM : CompileCorrectP armDM (JT.ArmLoader XD WD)
(compileOn ArmRA.rv2arm)` and `C_runs_armDM` (the same for `CompileRunsP`) = `C_correct_rv2arm a64DM` / `C_runs_rv2arm
a64DM`. They are Spec's `CompileCorrect` / `CompileRuns` plus one premise on the START state (`ArmLoader`: code bytes
executable, input/output/work blocks readable+writable). Axioms: the standard three. Joint build: this lake package
(`lake build Blocks.ArmDMTop`, Lean 4.34.1) compiles the Nano chain of `Main/ArmTop` (271 modules, ~6 min the first
time, one build at a time on 15 GB) next to DeepMind's `arm64`.
