# rv2arm proof notes: the plan for `armTarget.step_ok` (code UNPROVEN; these notes are the proof plan)

The code is `rv2arm.lean` (nano). `rv2arm.py` is a test oracle and emits the same bytes.
J semantics: `CallProbe.step` in `Nano/V2Self/Proof/Machine/Call.lean`. The RV words are those of `SimW.encJX`.
Instruction choice follows `Testing/notes/NANO_V2_ARM.md` §0-min (2026-11-20):
* no `ldur`/`stur`;
* no SP-relative form (sp is never used);
* no store of xzr;
* no `movn`/`ubfm`/`adr`;
* register 31 appears only as xzr in ALU/compare operand positions (and as `madd`'s Ra = xzr).

`test_arm.sh` checks this on the emitted code with objdump: the mnemonics, no sp, no stored xzr, and x18..x29 unused.

## Global facts (every block)

* **Block shape.** K = 4 A64 words per J instruction. The real words come first, then `PAD = add x16, x16, #0`
  (0x91000210, lemma `full_addi`). J index pc ↦ A64 byte address `base + 16·pc`.
  Exception: `jal x1` puts PAD first and `bl` last.
* **Register map π** (RV → A64):
  * 0 ↦ xzr (only as an ALU/compare operand);
  * 1 ↦ x30;
  * 2 (RV sp) ↦ x4, an ordinary register: the host passes the work top in x4;
  * 10..13 ↦ x0..x3;
  * 28 ↦ x12, 29 ↦ x13, 30 ↦ x10, 31 ↦ x11;
  * 5..8, 14, 15 ↦ the same number.

  π is injective on the non-zero registers and avoids 16..29 and 31. Any other RV register makes the validation pass
  return the EMPTY output. For `Rel`: `X[π r] = s.x r` for r ∈ dom π \ {0}.
* **Scratch.** x16 and x17 only. They are not in π's image, so `Rel` says nothing about them.
  * x16: address (`add/sub x16, s, #abs`) and shift amount (`movz x16, #sh`); PAD adds 0 to it.
  * x17: the zero of a store of x0 (`movz x17, #0`).

  Both are dead at every block boundary: no block reads them before writing them in the same block.
* **Never written:** x18 (macOS platform register), x19..x29 (`armMapping.kept`), sp (never even read).
* **NZCV.** Only `cmp` (`subs xzr`) writes NZCV, and only in compare-branch blocks. The `b.cond` of the same block
  reads it. NZCV is dead at every block boundary, so `Rel` need not mention it. `cbz` reads no flags.
* **Alignment.** 8-byte accesses (`ldr`/`str`, unsigned-offset form only) are emitted only for J `ld`/`sd`. They
  access ea = x[rs] + off with ea % 8 = 0, which Gen guarantees (frames and the expression stack are 8-aligned, and
  offsets are multiples of 8). A negative or unaligned-imm offset goes through `x16 = x[rs] ± abs` with
  `[x16, #0]`; the address is the same ea. The `Arm/proofs` lemmas need exactly this premise (8-aligned, < 2^29).
  Byte accesses (`ldrb`/`strb`) have no alignment premise.
* **Branch relocation.** For RV byte offset B = 4·o (J offset o) in block pc, with the branch word in slot k:
  the A64 word offset = 4·(pc + o) − (4·pc + k) = B − k. So:
  * `b`, `cbz`: B (slot 0);
  * `b.cond`: B − 1 (slot 1, after `cmp`);
  * `bl`: B − 3 (slot 3).

  Validation requires the target 0 ≤ pc + o < n and |B| ≤ 262140 (±1 MiB for b.cond/cbz).
* **Links (V2, W = 16).** `jal x1` links x30 = base + 16·(pc + 1), the address of the next block. `jalr x0, 0(r)`
  is `br π r`. A link value lives in J registers and memory as an A64 address. Gen never does arithmetic on link
  values; it only stores, reloads and jumps to them. So J must be parameterized by W (NANO_V2_ARM.md §0a, V2).
* **Encoding ranges.** RV I/S immediates are |imm| ≤ 2048 < 4096, so they fit add/sub imm12 directly.
  movz/movk take imm16; slli/srli shift amounts are < 64.

## Per J instruction

Notation: d = π rd, s = π rs, a = π ra, b = π rb. The lemmas are the existing `Arm/proofs` full steps and D's AL
drafts (table below).

| J (semantics from `step`) | A64 block (then PAD) | scratch | NZCV | lemmas |
|---|---|---|---|---|
| any rd = 0 write (addi/ld/lbu/alu/slli/srli): no-op | PAD ×4 | x16 | – | full_addi ×4 |
| `addi rd x0 imm`, imm ≥ 0: x[rd] := imm | `movz d, #imm` | – | – | full_movz |
| `addi rd x0 imm`, imm < 0: x[rd] := 2^64 + imm | `movz d, #(65536 + imm); movk d, #0xFFFF, lsl 16/32/48` | – | – | full_movz + full_movk ×3 |
| `addi rd rs imm` (rs ≠ x0): x[rd] := x[rs] + imm | `add d, s, #imm` / `sub d, s, #abs` | – | – | full_addi / full_subi |
| `ld rd rs off`: x[rd] := m(ea) | `ldr d, [s, #off]` (off ∈ 8ℕ, < 32768) · else `add/sub x16, s, #abs; ldr d, [x16]` | x16 (2nd form) | – | full_ldr (+ full_addi\|subi) |
| `sd r2 r1 off`: m(ea) := x[r2] | the same with `str`; r2 = x0: `movz x17, #0` first, then store x17 | x16, x17 | – | full_str (+ full_addi\|subi, full_movz) |
| `lbu rd rs off`: x[rd] := byte(ea) | `ldrb d, [s, #off]` (0 ≤ off < 4096) · else `add/sub x16, s, #abs; ldrb d, [x16]` | x16 (2nd form) | – | full_ldrb (+ full_addi\|subi) |
| `sb r2 r1 off`: byte(ea) := x[r2] & 255 | `strb` (the same forms); r2 = x0: via x17 = 0 | x16, x17 | – | full_strb (+ full_addi\|subi, full_movz) |
| `alu op rd a b`: x[rd] := aluf op | `add/sub/mul/and/orr/lslv/lsrv/eor d, a, b` (mul = `madd d, a, b, xzr`; x0 operand = xzr) | – | – | AL1/AL2/AL3/AL5. lslv/lsrv take the amount mod 64 = RV's `sll`/`srl` (`shl_mod`/`shr_mod`) |
| `slli/srli rd rs sh` | `movz x16, #sh; lslv/lsrv d, s, x16` | x16 | – | full_movz + AL3 |
| `beq a x0 o` / `beq x0 b o` | `cbz a|b, B` | – | – | full_cbz (taken/not taken) |
| `beq x0 x0 o` | `b B` | – | – | full_b |
| other `beq`, `bne`, `bltu`, `bgeu a b o` | `cmp a, b; b.eq/ne/lo/hs (B − 1)` (x0 operand = xzr) | – | set by cmp, read by b.cond, dead after | AL4 + full_bc. bltu = lo (C = 0), bgeu = hs (C = 1): unsigned, as in J |
| `jal x0 o` | `b B` | – | – | full_b |
| `jal x1 o`: x1 := link, pc := pc + o | `PAD; PAD; PAD; bl (B − 3)` | x16 (PAD) | – | full_addi ×3 + full_bl |
| `jalr x0 r` (imm 0): pc := (x[r] − base)/16 | `br π r` (host return: `br x30`) | – | – | AL6 (br; full_ret covers x30) |

The not-taken path of a branch block runs the trailing PADs (full_addi). The taken path leaves the block early.
Either way, the block takes ≤ 4 A64 steps per J step, and `sim_star` composes them.

## Lemma map (lead, 2026-11-20). AL drafts are fuzz-confirmed but not yet Lean-checked

| lemma | covers | used by blocks |
|---|---|---|
| AL1 | add/sub (register) | alu add/sub |
| AL2 | and/orr/eor (register) | alu and/or/xor |
| AL3 (branch al3-shift) | lslv/lsrv/asrv | alu sll/srl, slli/srli |
| AL4 (branch al4-fullcmp) | subs/cmp (register) + NZCV | compare-branch blocks, with full_bc |
| AL5 | mul/madd | alu mul (`madd d, a, b, xzr`) |
| AL6 | br (+ ldur, now unused) | jalr |
| full_movz / full_movk | movz, movk | addi x0, shift amounts, the zero for x0 stores |
| full_addi / full_subi | add/sub immediate | addi, PAD, x16 address forms |
| full_ldr / full_str | 8-byte, unsigned imm | ld, sd |
| full_ldrb / full_strb | byte | lbu, sb |
| full_b / full_bl / full_bc / full_cbz | branches | jal x0, beq x0 x0 / jal x1 / compare branches / beq against x0 |

**Register 31: what remains.** Every existing `full_*` lemma requires register fields < 31, and the blocks no longer
use 31 in any `full_*` instruction. Register 31 remains only in the AL instructions, as xzr:

| use | count in B2's ARM code | needed in |
|---|---|---|
| `madd d, a, b, xzr` (every mul; Ra = 31) | 142 | AL5 |
| `cmp a, xzr` (`bne` against x0; Rm = 31) | 1 | AL4 |
| ALU / compare with an x0 operand (Rn/Rm = 31) | 0 (possible) | AL1–AL4 |

Removed by this version:
* `str xzr`: now x17 = 0;
* sp as a base or a source: RV sp ↦ x4;
* `ldur`/`stur`: now the x16 address path;
* `sub d, xzr, x16`: now movz/movk;
* `cmp a, xzr` for `beq`: now cbz.

## The statement (draft): `ArmBlock.lean`

`ArmBlock.BlockOK M`: for every program C, data region D, kept values K, J state (pc, s) and A64 state t, if
* `C[pc]? = some j`,
* `validJ C.length pc j` (rv2arm's validation at the J level),
* `AccOK C D (pc, s)` (memory accesses in D; a `jalr` target is a block address), and
* `RelA M C D K (pc, s) t`,

and `stepW 16 C (pc, s) = some ps'`, then `∃ t', Runs M t t' ∧ RelA M C D K ps' t'`.

`RelA` = configured, PC = b + 16·pc, `X[π r] = x r` for live r (RV sp in x4), x 0 = 0, x18..x29 and sp = K, the code bytes
`codeA C` at b, every D cell's 8 bytes = J's cell (little-endian), D 8-aligned, D disjoint from the code, and both
inside the RAM window. `stepW W` is J with link width W (V2). `stepW 4` = `CallProbe.step`.
`blockJ` mirrors rv2arm at the J level. `ArmBlockCheck.lean` (generated by `gen_check.py`) checks with `#guard` that
`blockJ j` = the oracle's block on all 13,315 distinct J instructions of B2, the translator and the examples, plus
synthetic x2/x0/far-offset forms. All pass (Lean 4.29, 70 s; run `check_lean.sh`).
Open for the proof:
* the step count (≤ 4, also on the branch-taken path);
* `M := arm` (Spec's machine, after the 4.35 migration);
* the bridge from `RelA` to Arm/proofs' `Abs`/`ArmFull`;
* x18 is in `keep` although `armMapping.kept` lists x19..x29 + sp: an extra, stronger guarantee, for macOS;
* the calling convention: RV sp ↦ x4, so `armMapping.workTop` must become 4 (it is 31 = sp now). That is a Spec
  (owner) change. The shim passes the work top in x4 and still sets sp.

## Translator-level facts for the Lean equation

* The output is `(C.map block).flatten` as little-endian bytes, emitted in chunks of CHUNK_WORDS = `z0` = 32000 RV words, because a nano
  list holds < 2^19 elements. `rv2arm.sh` concatenates the chunks. A Lean statement can be made about `l0` over the
  whole range directly.
* Validation `c1` runs over the whole program before any byte is emitted. An invalid program gives the EMPTY output
  (so `compileC_arm` would return `none`).
* Decode facts needed: `o7 (encJX (branch a b o)) = 4·o` (sign-extended), `o8 (encJX (.jal rd o)) = 4·o`,
  `o5`/`o6` = the I/S immediates, field extractors o1..o4 = rd, funct3, rs1, rs2.
