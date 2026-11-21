# Native AArch64 back end: lifting A64SemN to the Sail ARM model

Plan for `a64SailN : JT.A64SemN armSail TT TT` (not proved here; nothing was built or run). Branch `nap-m2`,
read 2026-11-21. Paths are relative to the repo root. "GUESS" marks anything not read off a file.

Headline: of the seven new fields, **three already have their Sail full-step lemma** (`full_cbnz`, `full_stur`,
`full_ldur`), two are one-line variations of existing lemmas (`movn`, `addLsl3`), and two need a new execute lemma
(`ldrbR`: new execute function + `ExtendReg`; `ldp`: new execute function, two reads, two register writes).
No field needs a premise that `A64SemN` does not already supply.

## 1. How the existing Sail instance is organised

Layers (bottom up), all under the pinned configuration `ArmFullB s n` (EL3, MMU off, only `FEAT_AA64EL0`, debug/PMU/
timers off; `Arm/proofs/Arm/Full.lean:15`, pins listed in `Arm/proofs/README.md` "Assumptions of the full-step layer"):

| Layer | Where | What |
|---|---|---|
| decode prune | `Arm/proofs/Arm/SymDec.lean` (`dec_*sym`), also `FullAluAdd.lean:20`, `FullBrLdur.lean:31,40` | `__DecodeA64 pc w s = decode_X <slices of w> {s with SEE := k}` from `w &&& K = T` only. Tactics `sprune hK __DecodeA64; sprune hK __DecodeA64_<group>; sfin hK h hs see; all_goals rfl` (`SymDec.lean:62-76`). No full decoder unfold, no `Reduce__1`. |
| decode fn + execute | `Exec.lean` (`add_exec` :28, `mov_exec` :78), `BrFull.lean` (`movz_exec'` :99, `movk_exec'` :89, `addi_exec` :109), `Branch.lean` (`cbz_*`/`cbnz_*` :34-85), `Mem.lean` (`ldrb_exec` :210, `strb_exec` :235, `ldr_exec` :298, `str_exec` :323, `stur_exec` :348), `FullBrLdur.lean` (`ldur_exec` :73) | `decode_X (ofNat 5 d) … s = .ok () {s with regs := xset … }`. Tactics: `idx r` (facts about `r < 31`, `Exec.lean:13`), `exec_simp` (`Exec.lean:17`: one big `simp` with `X_read`, `X_set`, `ShiftReg`, `DecodeShift`, the execute functions, monad lemmas), for memory also `pins` (`Hooks.lean:302`, destructs `Pins`) and `esimp` (`Hooks.lean:313`, feature tests such as `HaveLSE2Ext` reduce to false, line 339). |
| memory access | `Mem.lean`: `memreadG1` :171, `memsetG1` :190, `memreadG8` :260, `memsetG8` :279, `gpr_ok` :100, `bigend_ok` :165 | `Mem_read va 1/8 (accG true) s = .ok v {s with InGuardedPage := false}` given `VaOK va.toNat`, for 8 bytes also `va.toNat % 8 = 0` and `MemD s.mem va v`. |
| generic full step | `BrFull.lean`: `full_gen` :20, `full_x` :242 (one X write), `full_tk` :261 / `full_nt` :279 (branch taken / not); `Mem.lean`: `full_ld` :384 (load: X write + `InGuardedPage`), `full_st` :406 (store) | a decode result that changes only X / NZCV / SEE / branch bookkeeping is one `stepModel` step (fetch `fetch_ok`, `step_ok`, `__CycleEnd`), keeps `ArmFullB`. Needs `noteret hK i …` (`BrFull.lean:189`): a mask bit ≥ 12 where the word differs from `eret`. |
| per-form full step | `full_b` :321, `full_cbz` :329, **`full_cbnz` :343**, `full_bc` :357, `full_movz` :372, `full_movk` :382, `full_addi` :393, `full_subi` :404, `full_bl` :425 (all `BrFull.lean`); `full_ldrb` :435, `full_strb` :447, `full_ldr` :459, `full_str` :472, **`full_stur` :485** (`Mem.lean`); `full_addr` :46, `full_subr` :58 (`FullAluAdd.lean`); `full_subsr` (`FullSubs.lean:72`); `full_lslv/lsrv/asrv` (`FullAluShift.lean:51-75`); `full_brB` :118, **`full_ldur` :157** (`FullBrLdur.lean`); logic/mul in `FullAluLogic`, `FullMul` | see shape below |
| A64Sem field | `Arm/sail/ArmSail/Fields.lean`: `F_movz` :54, `F_movk` :73, `F_addi` :88, `F_subi` :103, `F_alu` :128, `F_b` :199, `F_bl` :211, `F_cbz` :227, `F_br` :247, `F_cmpbr` :257, `F_ldr` :323, `F_ldrb` :358, `F_str` :403, `F_strb` :445 | `pre` → `full_X` → rewrite slices → `goes_set`/`goes_jump`/`goes1` |
| instance | `Arm/sail/ArmSail/A64.lean:10` `a64Sail` | 14 fields = the 14 `F_*`, `map := rfl`, `ram := by decide` |

**Shape of a `full_*` lemma** (section variables, e.g. `BrFull.lean:316-318`):
`hf : ArmFullB s nb`, `ha : Abs s a`, `hpc : s.regs.get? ._PC = some pc`, `hlt : VaOK pc.toNat`,
`hal : pc.toNat % 4 = 0`, `hm : MemWord s.mem pc.toNat w`; plus `hK : w &&& K = T` (opcode bits), register slices
`< 31`, and for memory forms `VaOK <address>`, `<address> % 8 = 0` (8-byte only), `MemD`/`get?` for the loaded value.
Conclusion: `∃ s', stepModel s = .ok () s' ∧ Abs s' a' ∧ ArmFullB s' nb ∧ s'.regs.get? ._PC = some p ∧ s'.mem = M`.
`VaOK n := n < 2^48 ∧ n/2^16 ≠ 0x2C00 ∧ n/2^16 ≠ 0x3C00` (`Fetch.lean:42`; replaced the old `n < 2^29`);
`vaRam` (`Fetch.lean:45`) gives it for the RAM window `[2^31, 3·2^30)`.

**Observation / configured** (`Arm/sail/ArmSail/Machine.lean`): `armSail` :44, `obsS` :38 (`_PC`, `x0..x30`, registers
≥ 31 read 0, bytes of Sail's map), `configured s = (∃ n, ArmFullB s n) ∧ _PC present`. `pre` :137 turns a field's
premises into `Pre s w n a pc` :125 (`hf ha hpc va al lo hi hm obs`), `abs_ex` :66, `obs_eq` :56, `goes1` :74 /
`goes2` :79, `set_obsA` :85, `byte_obs` :109, `memword` :117. Encoding side (`ArmSail/Enc.lean`): `mask32` :21,
`fldt` :37, `immt` :40, `mo_lt` :42, `sx2` :49, `off19` :107. `Fields.lean` helpers: `goes_set` :27, `goes_jump` :34,
`regS` :20, `pcS` :24, `ea_toNat` :316, `cbyte_bv` :311, `wrD_get` :386, `mget_insert` :308.

**Size and cost** (from `Arm/proofs/README.md` table and the files): a `dec_*sym` is ~8 lines; an `*_exec` is 6 lines
(ALU) to ~25 (memory); a `full_*` is ~10 lines; an `F_*` is 12 (movz) to ~40 lines (str). Check times: `SymDec`
~35 s, `BrFull` ~33 s, `Mem` ~10 s, `FullAlu*` ~3 s each, `FullBrLdur` ~5 s, whole `Arm/proofs` ~1000 s of which
`Words` ~550-775 s. `Arm/sail`: `lake build ArmSail ArmSail.Axioms` 431 jobs, non-model part ~25 min fresh
(`Arm/sail/NOTES.md`). Prerequisite: the partitioned model built in `/home/user/armv9-lean` (~2 h on 4 cores / 15 GB,
`Testing/notes/ARM_FAST.md` §9). Options used: `maxHeartbeats 4000000..20000000`, `maxRecDepth 1000000`,
`--tstack=400000`.

**Model sources.** The generated model IS in this checkout: `Arm/model/Armv9/*.lean` (77 MB; `Instrs64.lean`,
`DecodeEnd.lean`, `V8Base.lean`). The built tree `/home/user/armv9-lean` does NOT exist here, so no proof can be
checked in this checkout until it is regenerated (`Arm/gen/partition.py`, `build_part.sh`).

## 2. The seven instructions

Common to all: `d/t/u/n/m < 31` (no SP, no XZR, so no `CheckSPAlignment`), fetch premises via `pre`. MTE / tag checks:
`accG` has `tagchecked = true` (`Mem.lean:176`) but every feature is off in `ArmFullB`, and the existing `memreadG*`
lemmas already discharge this. All Sail function names below were read in `Arm/model/Armv9`.

### 2.1 `cbnz xt, f` (`0xB5000000`, compare-and-branch) — easy
* Sail: `__DecodeA64_BranchExcSys`, SEE 117 (`DecodeEnd.lean:24873`), `decode_cbnz_aarch64_instrs_branch_conditional_compare`
  (`Instrs64.lean:5462`); `cbnz_eq_cbz : decode_cbnz… = decode_cbz… := rfl` (`BrFull.lean:308`).
* **Already proved**: `dec_cbnzsym` (`SymDec.lean:111`), `cbnz_taken`/`cbnz_not` (`Branch.lean:34,51`),
  `full_cbnz` (`BrFull.lean:343`, `ArmFullB` form, target `if a.x t = 0 then pc + 4 else pc + sext(imm19:00)`).
* New: only `F_cbnz` = copy of `F_cbz` (`Fields.lean:227-245`) with base `0xB5000000` and the two `if` arms swapped
  (A64SemN's `cbnz` result is already written "zero → pc+4"). ~20 lines.
* Side conditions: none beyond the field's (`-2^18 ≤ f < 2^18`, `t < 31`).

### 2.2 `stur xt, [xn, #f]` (`0xF8000000`, unscaled signed imm9) — easy
* Sail: `__DecodeA64_LoadStore`, SEE 687 (`DecodeEnd.lean:28787`),
  `decode_stur_gen_aarch64_instrs_memory_single_general_immediate_signed_offset_normal` (`Instrs64.lean:31096`),
  `execute_aarch64_instrs_memory_single_general_immediate_signed_offset_normal`.
* **Already proved**: `dec_stursym` (`SymDec.lean:201`), `stur_exec` (`Mem.lean:348`), `full_stur` (`Mem.lean:485`,
  `ArmFullB`, mask `0xFFE00C00`): needs `VaOK (a.x n + (slice w 12 9).signExtend 64)`, that address `% 8 = 0`;
  result `s'.mem = wrD s.mem addr (a.x t)`.
* New: `F_stur` = `F_str` (`Fields.lean:403-443`) with a different address lemma: `slice (wd …) 12 9 =
  BitVec.ofNat 9 (mo f 9)` and `(x + (ofNat 9 (mo f 9)).signExtend 64).toNat = a` from `(a : Int) = x.toNat + f`,
  `-256 ≤ f < 256`, `a` in RAM. Model-free; `Arm/apc/Blocks/A64DMN.lean:174` (`mo9`) is the DeepMind-side analogue to
  copy into `Enc.lean` (`eau_of` :178 there is stated on `Arm64.State`, so only its arithmetic is reusable).
  The store tail (`wrD_get`, `cbyte_bv`) is verbatim from `F_str`. ~45 lines incl. the address lemma.
* Side conditions: 8-alignment and RAM window are A64SemN premises (`a % 8 = 0`, `ramStart ≤ a`, `a + 8 ≤ ramEnd`);
  RAM ⊂ `VaOK`. Sail does check alignment (`IsAligned__1 va 8` in `memsetG8`), so the aligned-only statement is needed
  and present.

### 2.3 `ldur xt, [xn, #f]` (`0xF8400000`) — easy
* Sail: SEE 680 (`DecodeEnd.lean:28696`), `decode_ldur_gen_…_signed_offset_normal` (`Instrs64.lean:30438`).
* **Already proved**: `dec_ldursym` (`FullBrLdur.lean:40`), `ldur_exec` (:73), `full_ldur` (:157).
* Catch: `full_ldur` sits in the section whose hypothesis is `hf : ArmFull s` (`FullBrLdur.lean:144-147`) and
  concludes `ArmFull s'`, i.e. `BTypeNext = 0` only. `armSail.configured` is `∃ n, ArmFullB s n` (after a `br`,
  `n = 1`), so the field needs the `ArmFullB s nb` version. The proof body only uses `full_ld` and `s0_pins'`, which
  are `ArmFullB`-generic (`Mem.lean:384`, `BrFull.lean:301`), so restating it in the `n0` section should be a
  3-line change (GUESS: not compiled). The file header still says "draft, NOT yet checked", but `FullBrLdur` is in
  `check.sh` and `Arm/sail/NOTES.md` lists it as made to compile; stale comment.
* New: `full_ldurB` (restatement) + `F_ldur` = `F_ldr` (`Fields.lean:323-356`) with the 2.2 address lemma. ~35 lines.
* Side conditions: as 2.2; value premise `∀ k < 8, memory (a + k) = some (cbyte v k)` → `MemD` as in `F_ldr`.

### 2.4 `movn xd, #i, lsl 16h` (`0x92800000`, move wide) — easy
* Sail: `__DecodeA64_DataProcImm`, test `extractLsb 30 23 == 0x25`, SEE 697 (`DecodeEnd.lean:24449-24459`),
  `decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide Rd imm16 hw opc sf` (`Instrs64.lean:31605`) →
  `execute_aarch64_instrs_integer_ins_ext_insert_movewide` (`Instrs64.lean:31569`; `MoveWideOp_N` complements the
  result after `updateSubrange` on zeros).
* Resembles `movz`: `dec_movzsym` (`SymDec.lean:129`), `movz_exec'` (`BrFull.lean:99`), `full_movz` (:372), `F_movz`.
  The three decode functions have the same body; `exec_simp` already contains the execute function and
  `undefined_MoveWideOp`.
* New: `dec_movnsym` (mask `0xFF800000 = 0x92800000`, args `… (slice w 21 2) 0#2 1#1`, SEE 697), `movn_exec'`
  (result `xset s.regs d (~~~(imm.setWidth 64 <<< (hw.toNat*16)))`; GUESS: same script as `movz_exec'` plus one
  `Complement`/`~~~` rewrite), `full_movn` (via `full_x`, `noteret hK 30`), `F_movn` with a value lemma
  `UInt64.ofBitVec (~~~(ofNat 64 i <<< (h*16))) = movnV i h` (like `movk_val`, `Fields.lean:67`). ~45 lines.
* Side conditions: none (`sf = 1`, so the `hw<1>` UNDEFINED test is false; `pos + 15 < 64` from `h < 4`).
* Risk: `Enc.lean` notes that a `simp` proof of `movk`'s immediate overflowed the kernel; use `immt` (`rw`).

### 2.5 `add xd, xn, xm, lsl #3` (`0x8B000C00`, add shifted register, imm6 = 3) — easy
* Sail: `__DecodeA64_DataProcReg`, SEE 14 (`DecodeEnd.lean:29558-29570`),
  `decode_add_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg` (`Instrs64.lean:399`) →
  `execute_…_add_sub_shiftedreg` (:369) → `ShiftReg m LSL 3 64` (`V8Base.lean:88419`, `result <<< amount`).
* Resembles `full_addr` (`FullAluAdd.lean:46`), which is the same decode clause with `imm6 = 0#6` hard-wired in
  `dec_addrsym` (:20) and `add_exec` (`Exec.lean:28`). Not directly reusable (different `hK`, different imm6), but
  the three proofs are parametric in everything except the literal.
* New: `dec_addl3sym` (`hK : w &&& 0xFFE0FC00 = 0x8B000C00`; `sfin` turns the fully-masked imm6 into `3#6`),
  `add3_exec` (`… 3#6 … = xset s.regs d (a + b <<< 3)`; `exec_simp` has `ShiftReg`, `shl_int_nat`), `full_addl3`
  (`full_x`, `noteret hK 30`), `F_addLsl3` (one arm of `F_alu`, value by `UInt64.toBitVec_shiftLeft`). ~45 lines.
  Cheaper alternative: generalise `dec_addrsym`/`add_exec`/`full_addr` to a symbolic imm6 < 64 — more reuse, but
  touches lemmas `a64Sail` depends on; not recommended.
* Side conditions: none.

### 2.6 `ldrb wt, [xn, xm]` (`0x38606800`, register offset, option = 011 (LSL/UXTX), S = 0) — medium
* Sail: `__DecodeA64_LoadStore`, test `extractLsb 31 21 == 0b00111000011 && extractLsb 11 10 == 0b10`, SEE 656
  (`DecodeEnd.lean:28355`), `decode_ldrb_reg_aarch64_instrs_memory_single_general_register Rt Rn S option Rm opc size`
  (`Instrs64.lean:28275`) → `DecodeRegExtend` (`V8Base.lean:88353`, `0b011 → ExtendType_UXTX`) →
  `execute_aarch64_instrs_memory_single_general_register` (`Instrs64.lean:28107`) → `ExtendReg m UXTX 0 64`
  (`V8Base.lean:88366`) → `Mem_read address 1` → `X_set t 32 (zeroExtend data 32)`.
* Resembles `ldrb_exec`/`full_ldrb` (`Mem.lean:210,435`): same 1-byte `memreadG1`, same 32-bit `X_set` giving
  `b.setWidth 64`, same `full_ld`, same `F_ldrb` tail (`byte_obs`).
* New work: (a) `dec_ldrbrsym` with mask `0xFFE0FC00 = 0x38606800` (S, option, opc, size become literals);
  (b) a lemma `ExtendReg m .ExtendType_UXTX 0 64 s = .ok b s` for `xget s.regs m = some b`: nothing in
  `Arm/proofs` mentions `ExtendReg`/`Extend`/`DecodeRegExtend` (grep), and its body has the dependent-width term
  `(extractLsb val (len-1) 0) +++ Zeros (n := shift)` with `len = min 64 (64 - 0)` plus two `sail_assert`s — expect
  cast friction; (c) `ldrbr_exec`: the decode function is long (opc/size case tree, three `ConstrainUnpredictable`
  blocks guarded by `wback`, all dead since `wback = false`), execute is a different function from the immediate
  forms (extra `AArch64_SetLSInstructionSyndrome` (pure unit), `Prefetch` arm); (d) `full_ldrbr`, `F_ldrbR`
  (address `(a.x n + a.x m).toNat = x_n + x_m` from the `< ramEnd` premise). ~90 lines.
* Side conditions: `VaOK` from RAM premises; no alignment (1 byte); no overflow since `x_n + x_m < 3·2^30`.
  All supplied by A64SemN.
* Risk: (b) and the size of the `simp` in (c). `tagchecked` here is `memop != PREFETCH = true`, same as `accG`.

### 2.7 `ldp xt, xu, [xn]` (`0xA9400000`, pair, signed-offset form, imm7 = 0, opc = 10) — medium/hard
* Sail: `__DecodeA64_LoadStore`, test `extractLsb 30 22 == 0b010100101`, SEE 611 (`DecodeEnd.lean:27768`),
  `decode_ldp_gen_aarch64_instrs_memory_pair_general_offset Rt Rn Rt2 imm7 L opc` (`Instrs64.lean:24837`) →
  `execute_aarch64_instrs_memory_pair_general_post_idx` (`Instrs64.lean:24580`).
* What Sail does for our word: `wback = false` kills both writeback-overlap blocks; `t == t2` enters
  `ConstrainUnpredictable Unpredictable_LDPOVERLAP` (UNKNOWN / UNDEF / NOP) — **excluded by the A64SemN premise
  `t ≠ u`**; `HaveLSE2Ext` is false in the pinned feature set (`esimp` rewrites it, `Hooks.lean:339`), so the load is
  **two separate `Mem_read`s of 8 bytes** at `address + 0` and `address + 8` (not the single 16-byte `Mem_read__1`
  with `ispair`); then `X_set t 64 data1; X_set t2 64 data2` (t2 written last — matches `setReg2`, where `u` wins);
  finally the `SPESampleInFlight` test.
* Reuse: `memreadG8` twice (the second on the state with `InGuardedPage := false` inserted: `pins_insert`,
  `insert_insert`), `gpr_ok`, `full_gen`, `F_ldr`'s `MemD` construction twice.
* New work: `dec_ldpsym` (mask `0xFFFF8000`, as `dec_ldpW` in `A64DMN.lean:312`); `ldp_exec` (two reads, two
  `xset`s, `BitVec.addInt address 0/8` normalisation, `sign_extend 0#7 64 <<< 3 = 0`); a new generic `full_ld2`
  (copy of `full_ld`, `Mem.lean:384`, with `xset (xset … t v1) u v2` and `Abs s' ((a.setX t v1).setX u v2)`);
  `F_ldp`: observation equation for two writes (`set_obsA` handles one; need the two-write analogue of
  `obs_setX2`, `A64DMN.lean:343`) against `setReg2`. ~130 lines.
* Side conditions and who supplies them: both addresses 8-aligned (`x_n % 8 = 0` ⇒ `(x_n + 8) % 8 = 0`: supplied);
  both in `VaOK` (`ramStart ≤ x_n`, `x_n + 16 ≤ ramEnd`: supplied); `t ≠ u`: supplied; `t = n` or `u = n` is fine
  (address read before the writes; no writeback); no SP. Nothing missing.
* Risk: largest `simp` goal of the seven (the decode function alone is ~75 lines of dead UNPREDICTABLE handling);
  heartbeats/kernel depth; if the model were ever pinned with LSE2 on, the proof changes shape completely.

## 3. Summary table

| instruction | resembles | reuse | new work | risk | estimate (sessions) |
|---|---|---|---|---|---|
| cbnz | cbz | `full_cbnz` exists (`BrFull.lean:343`) | `F_cbnz` only | very low | 0.25 |
| stur | str | `full_stur` exists (`Mem.lean:485`) | signed-imm9 address lemma, `F_stur` | low | 0.5 |
| ldur | ldr | `full_ldur` exists for `ArmFull` only (`FullBrLdur.lean:157`) | `ArmFullB` restatement, `F_ldur` (shares address lemma) | low | 0.5 |
| movn | movz/movk | `dec_movzsym`, `movz_exec'`, `full_x` patterns | `dec_movnsym`, `movn_exec'`, `full_movn`, `F_movn` + value lemma | low | 0.5 |
| addLsl3 | add (alu op 1) | `dec_addrsym`, `add_exec`, `full_x` patterns | same three with imm6 = 3, `F_addLsl3` | low | 0.5 |
| ldrbR | ldrb | `memreadG1`, `full_ld`, `F_ldrb` tail | `ExtendReg` lemma, new decode/execute pair, `F_ldrbR` | medium (dependent widths, big simp) | 1 |
| ldp | ldr ×2 | `memreadG8` ×2, `full_gen`, `F_ldr` pieces | `dec_ldpsym`, `ldp_exec`, `full_ld2`, two-write observation, `F_ldp` | medium/high (goal size) | 1.5-2 |

Plus ~0.5 session of setup (rebuild `/home/user/armv9-lean`, ~2 h wall, then ~25 min for the non-model part) and
~0.25 for `A64N.lean` (`a64SailN where toA64Sem := a64Sail; movn := F_movn; …`) and its `#print axioms`.

## 4. Avoiding a form in GenArm (fallbacks, cost per occurrence)

Occurrence counts are template sites in `Nano/Codegen/GenArm.lean` (grep), not dynamic counts.

| form | replacement (existing A64Sem forms only) | extra words | sites |
|---|---|---|---|
| ldp t,u,[n] | `ldr t,[n]; ldr u,[n,#8]` (needs `t ≠ n`; true at all sites: `a32 6 5 11`, `14 6 11`, `7 14 5`, `15 14 8`, `a11`) | +1 | 5 (`a32`) |
| ldur / stur | `sub x16,n,#-f; ldr/str t,[x16]` — `a9` (:93-98) already has this fallback branch (`a5 o 16 n f`) | +1 | 1 emitter (`a9`), 7 callers |
| cbnz t,L | `cbz t,.+8; b L` | +1 (offsets shift) | 2 (`a3 a_23`) |
| movn d,#i | general: `movz` + up to 3 `movk` (+3 worst case); `movn x0,#0` (= -1): `movz x0,#0; sub x0,x0,#1` (+1); in `a6`/`a7` (:74-86) drop the 0xFFFF path and use the movz path (up to 4 words instead of 1-3) | +1..+3 | 3 literal sites + `a6`/`a7` |
| ldrb t,[n,m] | `add x16,n,m; ldrb t,[x16,#0]` (x16 must be free) | +1 | 1 (:122) |
| add d,n,m lsl 3 | no shift-immediate form in A64Sem: `movz x17,#3; lslv x16,m,x17; add d,n,x16` (+2, clobbers x16/x17), or three doubling `add`s (+3); with a new `lsl #imm` (ubfm) field +1 but that is itself a new Sail lemma | +2 | 4 (`a34`) |

Given section 2, only `ldp` and `ldrbR` are plausible candidates, at +1 word each (6 sites in total).

## 5. Plan, order, total

1. Regenerate and build the partitioned model; confirm `lake build ArmSail` is green before touching anything.
2. New file `Arm/proofs/Arm/FullNat.lean` (import `Arm.FullBrLdur`, `Arm.FullAluAdd`): `full_ldurB`, then
   movn, addLsl3 (decode + exec + full). Add to `check.sh` and to the `Arm` lake roots.
3. `Arm/sail/ArmSail/FieldsN.lean` (import `ArmSail.Fields`, `Nano.Run.A64SemN`): `F_cbnz`, signed-imm9 address
   lemma (in `Enc.lean` or here), `F_stur`, `F_ldur`, `F_movn`, `F_addLsl3`. Five of seven fields done.
4. `ldrbR` (ExtendReg lemma first, in isolation), then `ldp` (`ldp_exec` first; if its `simp` does not close in
   a session, switch GenArm to the +1-word fallback for that form instead).
5. `ArmSail/A64N.lean`: `a64SailN`; extend `Axioms.lean`; then the native top theorem over `A64SemN` (out of scope).

Total: **about 5-6 sessions** (4.75-5.25 for the lemmas + setup/assembly), dominated by `ldp` and `ldrbR`.

### Not verified from this checkout
* Nothing was compiled: `/home/user/armv9-lean` is absent, so every "should work" above about tactic scripts
  (`sprune`/`sfin` on the new masks, `exec_simp` closing `movn`/`add lsl 3`, moving `full_ldur` to `ArmFullB`) is a GUESS
  from reading the existing proofs.
* Whether `Arm/gen/partition.py` puts the new `decode_*`/`execute_*` functions (movn, ldp, ldrb_reg, `ExtendReg`) in
  the "core" or the "rest" modules, and whether adding proof files changes its root set and forces a model rebuild.
  Proof files import `Armv9.DecodeEnd` (`Base.lean:2`), so the names are visible either way.
* The exact `simp` normal form of `ExtendReg … UXTX 0 64` and of the pair execute function; line estimates for
  2.6/2.7 are extrapolated from `ldrb_exec`/`ldr_exec`.
* Build time of `Fields.lean` alone (only whole-build figures are recorded).
* That `ConstrainUnpredictable` is never reached was read off the guards (`wback = false`, `t ≠ t2`), not executed.
* GenArm site counts are static greps of emitter calls; the per-program dynamic cost of the fallbacks was not measured.

## Addendum: an eighth form, `movz xd, #i, lsl 16h` (`movzH`)
Found while proving `li` (GenArm's `a7` starts a constant whose low 16-bit chunks are 0 with a shifted `movz`):
`A64SemN.movzH`, word `0xD2800000 + h·2^21 + i·2^5 + d`. On DeepMind it is the existing `dm_movz` (already stated for
any `hw`). On Sail it is the move-wide class again: the existing movz lemma generalised from `hw = 0` to any `hw`
(GUESS, not read: same decode clause, shift `16·hw`); expected easy, counted with `movn`.

