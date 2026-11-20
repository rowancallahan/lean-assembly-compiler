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

Notation: d = π rd, s = π rs, a = π ra, b = π rb. Lemma names are the existing `Arm/proofs` full steps. "new" marks
the lemmas still missing, to be matched with AL1–AL6:
* new-ALU: register-form add/sub/and/orr/eor/lslv/lsrv and madd;
* new-CMP: subs-reg;
* new-BR: br;
* new-LDUR: ldur, if `full_ld*` does not cover it.

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

## Translator-level facts for the Lean equation

* The output is `(C.map block).flatten` as little-endian bytes, emitted in chunks of 32000 RV words, because a nano
  list holds < 2^19 elements. `rv2arm.sh` concatenates the chunks. A Lean statement can be made about `l0` over the
  whole range directly.
* Validation `c1` runs over the whole program before any byte is emitted. An invalid program gives the EMPTY output
  (so `compileC_arm` would return `none`).
* Decode facts needed: `o7 (encJX (branch a b o)) = 4·o` (sign-extended), `o8 (encJX (.jal rd o)) = 4·o`,
  `o5`/`o6` = the I/S immediates, field extractors o1..o4 = rd, funct3, rs1, rs2.
