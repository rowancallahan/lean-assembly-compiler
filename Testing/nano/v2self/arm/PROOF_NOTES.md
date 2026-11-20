# rv2arm proof notes: the plan for `armTarget.step_ok` (code UNPROVEN; these notes are the proof plan)

The code is `rv2arm.lean` (nano). `rv2arm.py` is a test oracle and emits the same bytes.
J semantics: `CallProbe.step` in `Nano/V2Self/Proof/Machine/Call.lean`. The RV words are those of `SimW.encJX`.

## Global facts (every block)

* **Block shape.** K = 4 A64 words per J instruction. The real words come first, then `PAD = add x16, x16, #0`
  (0x91000210, lemma `full_addi`). J index pc ↦ A64 byte address `base + 16·pc`.
  Exception: `jal x1` puts PAD first and `bl` last.
* **Register map π** (RV → A64): 0 ↦ xzr (31 in register forms and as Rt of stores), 1 ↦ x30, 2 ↦ sp (= SP_EL3 with
  PSTATE.SP = 1, encoded 31 in add/sub-imm and load/store base fields), 10..13 ↦ x0..x3, 28 ↦ x12, 29 ↦ x13,
  30 ↦ x10, 31 ↦ x11, 5..8, 14, 15 ↦ same number. π is injective and avoids 16..29.
  Any other RV register, or sp in a position the table does not allow, makes the translator's validation pass
  return the EMPTY output. For `Rel`: `X[π r] = s.x r` for r ∈ dom π \ {0, 2}, and `SP = s.x 2`.
* **Scratch.** x16 and x17 only. They are not in π's image, so `Rel` says nothing about them. They are dead at
  every block boundary: no block reads x16/x17 before writing them in the same block, and PAD only adds 0 to x16.
* **Never written:** x18 (macOS platform register), x19..x29 (`armMapping.kept`), sp. Gen never writes RV x2.
* **NZCV.** Only `cmp` (`subs xzr`) writes NZCV, and only in branch blocks. The `b.cond` of the same block reads it.
  NZCV is dead at every block boundary: every flag reader is preceded by its own `cmp` in its own block, so `Rel` need
  not mention NZCV.
* **Alignment.** 8-byte accesses (`ldr`/`str`/`ldur`/`stur`) are emitted only for J `ld`/`sd`, and only on addresses
  J's cell memory reads as one cell: ea = x[rs] + off with ea % 8 = 0, which Gen guarantees (frames and the expression
  stack are 8-aligned, and offsets are multiples of 8). The `Arm/proofs` lemmas need exactly this premise (8-aligned,
  < 2^29). Byte accesses (`ldrb`/`strb`) have no alignment premise.
* **Branch relocation.** For RV byte offset B = 4·o (J offset o) in block pc with the branch word in slot k:
  the A64 word offset = 4·(pc + o) − (4·pc + k) = B − k. So `b` = B (k = 0), `b.cond` = B − 1 − (number of sp copies),
  `bl` = B − 3 (k = 3). Validation requires the target 0 ≤ pc + o < n and |B| ≤ 262140 (b.cond's ±1 MiB).
* **Links (V2, W = 16).** `jal x1` links x30 = base + 16·(pc + 1), the address of the next block. `jalr x0, 0(r)`
  is `br π r`. A link value lives in J registers and memory as an A64 address. Gen never does arithmetic on link
  values; it only stores, reloads and jumps to them. So J must be parameterized by W (NANO_V2_ARM.md §0a, V2).
* **Encoding ranges.** RV I/S immediates are |imm| ≤ 2048 < 4096, so they fit add/sub imm12 directly.
  movz takes imm16; slli/srli shift amounts are < 64.

## Per J instruction

Notation: d = π rd, s = π rs, a = π ra, b = π rb. Lemma names are the existing `Arm/proofs` full steps. "new"
marks lemmas still missing; the AL drafts below are meant to cover them:
* new-ALU = AL1 (add/sub), AL2 (and/orr/eor), AL3 (lslv/lsrv), AL5 (madd);
* new-CMP = AL4;
* new-BR, new-LDUR = AL6.

| J (semantics from `step`) | A64 block (then PAD) | scratch | NZCV | lemmas |
|---|---|---|---|---|
| `addi rd rs imm`, rd = 0: no-op | PAD ×4 | x16 | – | full_addi ×4 |
| `addi rd x0 imm`, imm ≥ 0: x[rd] := imm | `movz d, #imm` | – | – | full_movz |
| `addi rd x0 imm`, imm < 0: x[rd] := 2^64 − abs | `movz x16, #abs; sub d, xzr, x16` | x16 | – | full_movz, new-ALU(sub) |
| `addi rd rs imm`: x[rd] := x[rs] + imm (rs may be sp) | `add d, s|sp, #imm` / `sub …, #abs` | – | – | full_addi / full_subi |
| `ld rd rs off`: x[rd] := m(ea), ea 8-aligned (rd = 0: PAD ×4) | `ldr d, [s, #off]` (off ∈ 8ℕ, < 32768) · else `ldur d, [s, #off]` (−256 ≤ off < 256) · else `add/sub x16, s, #abs; ldr d, [x16]` | x16 (3rd form) | – | full_ldr / new-LDUR / full_addi\|subi + full_ldr |
| `sd r2 r1 off`: m(ea) := x[r2] | the same with `str`/`stur` (r2 = x0 stores xzr) | x16 (3rd form) | – | full_str / full_stur / full_addi\|subi + full_str |
| `lbu rd rs off`: x[rd] := byte(ea) (rd = 0: PAD ×4) | `ldrb d, [s, #off]` (0 ≤ off < 4096) · else `add/sub x16, s, #abs; ldrb d, [x16]` | x16 (2nd form) | – | full_ldrb (+ full_addi\|subi) |
| `sb r2 r1 off`: byte(ea) := x[r2] & 255 | `strb` (the same forms) | x16 (2nd form) | – | full_strb (+ full_addi\|subi) |
| `alu op rd a b`: x[rd] := aluf op | [`add x16, sp, #0`] [`add x17, sp, #0`] `add/sub/mul/and/orr/lslv/lsrv/eor d, a|x16, b|x17` (mul = `madd …, xzr`); rd = 0: PAD ×4 | x16, x17 if an operand is sp | – | new-ALU (+ full_addi). lslv/lsrv take the amount mod 64 = RV's `sll`/`srl` (`shl_mod`/`shr_mod`) |
| `slli/srli rd rs sh` | [`add x17, sp, #0`] `movz x16, #sh; lslv/lsrv d, s|x17, x16`; rd = 0: PAD ×4 | x16 (x17) | – | full_movz + new-ALU |
| `beq/bne/bltu/bgeu a b o` | [sp copies] `cmp a, b; b.eq/ne/lo/hs (B − 1 − copies)` | (x16/x17) | set by cmp, read by b.cond, dead after | new-CMP + full_bc (taken/not taken). bltu = lo (C = 0), bgeu = hs (C = 1): unsigned, as J |
| `jal x0 o` | `b B` | – | – | full_b |
| `jal x1 o`: x1 := link, pc := pc + o | `PAD; PAD; PAD; bl (B − 3)` | x16 (PAD) | – | full_addi ×3 + full_bl |
| `jalr x0 r` (imm 0): pc := (x[r] − base)/16 | `br π r` (host return: `br x30`) | – | – | new-BR (full_ret covers x30) |

The not-taken path of a branch block runs the trailing PADs (full_addi). The taken path leaves the block early.
Either way, the block takes ≤ 4 A64 steps per J step, and `sim_star` composes them.

## Lemma map (lead, 2026-11-20). AL drafts are fuzz-confirmed but not yet Lean-checked

| lemma | covers | used by blocks |
|---|---|---|
| AL1 | add/sub (shifted register, LSL 0) | alu add/sub; `sub d, xzr, x16` (addi x0, negative) |
| AL2 | and/orr/eor (register) | alu and/or/xor |
| AL3 (branch al3-shift) | lslv/lsrv/asrv | alu sll/srl, slli/srli |
| AL4 (branch al4-fullcmp) | subs/cmp (register) + cset + NZCV | branch blocks (`cmp`), with full_bc |
| AL5 | mul/madd | alu mul (`madd d, a, b, xzr`) |
| AL6 | br + ldur | jalr; ld with −256 ≤ off < 0 or unaligned-imm offsets |
| full_movz | movz (hw = 0) | addi x0 (imm ≥ 0), slli/srli amount, negative-imm helper |
| full_addi / full_subi | add/sub immediate | addi, PAD, x16 address forms |
| full_ldr / full_str / full_stur | 8-byte, unsigned-imm / unscaled | ld, sd |
| full_ldrb / full_strb | byte | lbu, sb |
| full_b / full_bl / full_bc | branches | jal x0 / jal x1 / branch blocks |
| full_ret | br x30 | host return (also covered by AL6) |

**Not covered as stated: register 31.** Every existing `full_*` lemma requires each register field < 31. The blocks
use field 31 in these places (counts are in B2's ARM code):

| use | where | count in B2 | needed |
|---|---|---|---|
| `str xzr, [x]` (Rt = 31 = xzr) | `sd x0, …` | 38 | full_str/full_stur with Rt = 31 (value 0) |
| `strb wzr` | `sb x0, …` | 0 (possible) | full_strb with Rt = 31 |
| `add x16/x17, sp, #0`, `add/sub d, sp, #imm`, `ldr/str [sp, …]` (Rn = 31 = SP_EL3) | sp operands (start code `srli x31, x2, 3`) | 1 | full_addi/full_subi/full_ldr… with Rn = 31 read as SP (PSTATE.SP = 1) |
| `cmp x, xzr` (Rm = 31) | branches against x0 | 49 | AL4 with Rn/Rm = 31 = xzr |
| `sub d, xzr, x16` (`neg`) | addi x0, negative | 3 | AL1 with Rn = 31 = xzr |
| `madd d, a, b, xzr` (Ra = 31) | every mul | 142 | AL5 with Ra = 31 (it is `mul`) |
| ALU with an x0 operand (Rn/Rm = 31) | alu with x0 | 0 (possible) | AL1–AL3, AL5 with Rn/Rm = 31 |

The B.cond/b/bl/br/movz instructions have no register-31 issue. Alternative, if register-31 variants are costly:
change the translator to load 0 into x17 (`movz x17, #0`) and use x17 instead of xzr. That leaves sp as the only
register-31 use: one `add x17, sp, #0` lemma. It costs ≤ 1 word per affected block, and every such block still fits
in 4 words. Not done yet: say if wanted, since it changes the bytes O mirrors.

## The statement (draft): `ArmBlock.lean`

`ArmBlock.BlockOK M`: for every program C, data region D, kept values K, J state (pc, s) and A64 state t, if
* `C[pc]? = some j`,
* `validJ C.length pc j` (rv2arm's validation at the J level),
* `AccOK C D (pc, s)` (memory accesses in D; a `jalr` target is a block address), and
* `RelA M C D K (pc, s) t`,

and `stepW 16 C (pc, s) = some ps'`, then `∃ t', Runs M t t' ∧ RelA M C D K ps' t'`.

`RelA` = configured, PC = b + 16·pc, `X[π r] = x r` for live r, SP = x 2, x 0 = 0, x18..x29 = K, the code bytes
`codeA C` at b, every D cell's 8 bytes = J's cell (little-endian), D 8-aligned, D disjoint from the code, and both
inside the RAM window. `stepW W` is J with link width W (V2). `stepW 4` = `CallProbe.step`.
`blockJ` mirrors rv2arm at the J level. `ArmBlockCheck.lean` (generated by `gen_check.py`) checks with `#guard` that
`blockJ j` = the oracle's block on all 13,361 distinct J instructions of B2, the translator and the examples, plus
synthetic sp/x0/far-offset forms. All pass (Lean 4.29, 70 s; run `check_lean.sh`).
Open for the proof:
* the step count (≤ 4, also on the branch-taken path);
* `M := arm` (Spec's machine, after the 4.35 migration);
* the bridge from `RelA` to Arm/proofs' `Abs`/`ArmFull`;
* x18 is in `keep` although `armMapping.kept` lists x19..x29 + sp: an extra, stronger guarantee, for macOS.

## Translator-level facts for the Lean equation

* The output is `(C.map block).flatten` as little-endian bytes, emitted in chunks of CHUNK_WORDS = `z0` = 32000 RV words, because a nano
  list holds < 2^19 elements. `rv2arm.sh` concatenates the chunks. A Lean statement can be made about `l0` over the
  whole range directly.
* Validation `c1` runs over the whole program before any byte is emitted. An invalid program gives the EMPTY output
  (so `compileC_arm` would return `none`).
* Decode facts needed: `o7 (encJX (branch a b o)) = 4·o` (sign-extended), `o8 (encJX (.jal rd o)) = 4·o`,
  `o5`/`o6` = the I/S immediates, field extractors o1..o4 = rd, funct3, rs1, rs2.
