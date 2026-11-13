# Faster generated code (branch `speed`)

Status: steps 1-3 done. **The fast backends are tested only (not proved).** `Proven/Code.lean`, `Words.lean`, `Compiler.lean`, `CompilerArm.lean` untouched.
Step 4 (Sail proof of the fast RV64 backend) was not attempted; the lemma list needed is at the end.

## Files
- `Proven/CodeFast.lean` (`Proven.Fast.compile`): RV64I fast backend. `Proven/CompilerArmFast.lean` (`Proven.Arm.Fast.compile`): AArch64 fast backend. Both import `Exp`/`Exp.denote` from `Proven.Code` unchanged and keep the `e.depth < 11` register budget (same temporaries at the same indices; folding never increases depth).
- `Proven/Stats.lean`: per-category word counts for the std and fast backends (categories const / move / op / select / return).
- `asm/fuzz.lean`, `asm/triple-data/triple.lean`: take `BACKEND=fast` (default: std backends, output of std unchanged and `triple.lean` output byte-identical to the committed `triple.txt`), `MODE=stats`, and (fuzz) `SMALL=1` (mostly small constants; default stream unchanged, seed 21 still reproduces the round-2 corpus byte for byte).
- `speed/liavg.lean`: average length of one uniform 64-bit constant.

## What changed in the generated code
1. Constants: RV64 `li` = `addi` (12-bit) | `lui`+`addi` (32-bit, avoiding the 2^31-2048.. corner) | `li(v >> sh); slli sh; addi lo` recursively (<= 8 words); AArch64 `movz`/`movn` + `movk` for the non-trivial halfwords (<= 4 words). Uniform random 64-bit constant: RV64 **7.9 words** (std 96.0), AArch64 **3.99** (std 96.0).
2. Variables (`a0..a3` / `x0..x3`) and the value 0 (`x0` / `xzr`) are used directly as operands: no copy, no `add t,x0,a_i`.
3. Result is computed straight into `a0`/`x0` (no final `add a0,x0,t0`, `mov x0,x9`).
4. Immediate forms (RV: `addi/andi/ori/xori/slti/sltiu`, `sub c` as `addi -c`, `slli/srli/srai` for any constant amount, `eq` with 0 as `sltiu 1`, `eq` with small c as `xori`+`sltiu`; ARM: `add/sub #imm12`, shifts by constant (`ubfm/sbfm`), `cmp #imm12` for ult/slt/eq).
5. `ite`: RV: no `snez` when the condition is a comparison (already 0/1) and operands used in place (4-5 words instead of 5 + moves); ARM: `cmp c,#0; csel` (2 words, no moves), and comparison conditions fused: `cmp x,y; csel d,a,b,cond` (1+1 words).
6. Source-level `Exp.fold`: constant folding, constant on the right of commutative operators, `ite` with constant condition. (Unproved, tested by the fuzzer; `Exp.denote` unchanged.)
Code is straight-line (only the final `ret`), so executed instructions per call = words (incl. `ret`).

## Measurements (words per expression = executed instructions per call; categories are sums over the corpus)
Corpus 1: `asm/triple-data` cases (18 expressions: demo, shifts, comparisons, ite, depth-10 chain, ...), `MODE=stats lake env lean asm/triple-data/triple.lean`:

| backend | avg words | const | move | op | select | ret |
|---|---|---|---|---|---|---|
| rv-std | 38.50 | 478 | 99 | 63 | 35 | 18 |
| rv-fast | **8.38** | 37 | 0 | 62 | 34 | 18 |
| arm-std | 37.88 | 478 | 99 | 73 | 14 | 18 |
| arm-fast | **6.77** | 20 | 0 | 70 | 14 | 18 |
(the demo expression: 47 -> 8 words on both backends.)

Corpus 2: fuzz, 300 expressions per seed, default constant mix (1/3 edge values, 2/3 uniform 64-bit), seeds 31-34 (avg words; per-seed category sums in `MODE=stats` output):

| seed | rv-std | rv-fast | arm-std | arm-fast |
|---|---|---|---|---|
| 31 | 484.7 | 36.9 | 477.5 | 27.6 |
| 32 | 544.3 | 39.8 | 536.8 | 30.3 |
| 33 | 510.8 | 36.1 | 503.4 | 27.0 |
| 34 | 538.9 | 39.8 | 530.7 | 29.7 |

Corpus 3: fuzz with `SMALL=1` (constants mostly 12-bit signed), seeds 41, 42: rv-std 376.7 / 380.1, rv-fast **26.9 / 27.9**, arm-std 369.2 / 373.7, arm-fast **23.3 / 24.1**.

Where the instructions go, seed 31, sums over 300 expressions `[const, move, op, select, ret]`:
rv-std `[130319, 4702, 5053, 5025, 300]` (90% constants); rv-fast `[4958, 32, 4087, 1679, 300]` (45% const, 37% op, 15% select); arm-std `[130319, 4702, 5929, 2010, 300]`; arm-fast `[2636, 32, 4550, 758, 300]` (32% const, 55% op, 9% select).
Wide constants remain the largest single cost on RV64 (7.9 words each); on ARM operators dominate. Remaining ideas, not done: constant pool (`ld` from `.data`, needs memory), shared constants (CSE), `ite` by branch (breaks straight-line code and the current proof shape), AArch64 logical immediates (`orr x,xzr,#bitmask`; and/orr/eor with bitmask immediates), RV `add`-of-two-halves for repeated 32-bit halves.

## Tests (four-way harness: Lean denote == RV64 QEMU == RV64 Sail C emulator == AArch64 QEMU, `BACKEND=fast`)
- `asm/triple-data` cases: all 18 cases, 17,000+ inputs, 0 mismatches (`BACKEND=fast lake env lean asm/triple-data/triple.lean > t.txt; python3 asm/fuzzpar.py t.txt 4`).
- Fuzz, `BACKEND=fast NCASES=300 K=100`, 4 checker processes:

| seed | constants | pairs | mismatches | gen | check |
|---|---|---|---|---|---|
| 31-34 | default | 4 x 30,000 | 0 | 17-18 s | 16-18 s |
| 41, 42 | small | 2 x 30,000 | 0 | 18-19 s | 16-17 s |
Total **180,000 (expression, input) pairs, 1,800 expressions, 0 mismatches**, plus the triple corpus. The checker is now ~1,800 pairs/s (std: ~390/s) because the Sail emulator runs ~13x fewer instructions.
Reproduce: `BACKEND=fast SEED=31 NCASES=300 K=100 lake env lean asm/fuzz.lean > x.txt && python3 asm/fuzzpar.py x.txt 4`.
Bugs found during development by reading, not by the harness: the ARM fused `cmp` must come after the code for the two arms (flags), now so.

## Step 4: what a Sail proof of the fast RV64 backend would need (not attempted, no `sorry` added)
Current `Proven/Words.lean` proves one lemma per *concrete* word (`step_word` needs `decide`-able encodings), ~230 words. The fast backend emits words with free fields, so the families must be parametric or generated for the (finite) used combinations:
- `lui rd, imm20` (opcode 0x37) for `rd` in {a0, t0..t6, a4..a7}, any 20-bit imm: new, no existing lemma (Step/Regs have no `LUI` case; model side: `ITYPE`/`UTYPE` execute clauses).
- `addi rd, rs1, imm12` with `rs1 ∈ {x0, a_i, T k, rd}`, arbitrary signed imm (existing: only imm 0, 1 and `add` R-type).
- `slli rd, rs1, sh` (6-bit shamt 0..63, not only 1), `srli`, `srai` (imm[10]=1) with `rd, rs1` general.
- `andi, ori, xori, slti, sltiu` (imm12), plus `sltiu rd, rs, 1` (exists as `iSeqz` only for rd = rs = T k).
- R-type `op rd, rs1, rs2` with `rd ∈ {T k, a0}` and `rs1, rs2 ∈ {T k, A i, x0}` (existing lemmas fix `rd = rs1 = T k`, `rs2 = T (k+1)`); the select sequence `sltu/sub/xor/and/xor` with general sources and `rd = a0`.
- Register-file frame lemmas for writes to `a0` (the current spec reads `a0..a3` as inputs; writing `a0` before the end must not be observed by later reads: argument holds since `a0` is written only by the last word of `genTo`, but `gen_ok` needs restating with an explicit destination and operand-register invariant).
- Pure arithmetic: `li` correctness (`lui`+`addi`+`slli` chain computes `BitVec.ofInt 64 v`, including the `2^31 - 2048` corner and sign extension of `lui`), 12-bit sign-extension lemmas for the immediates, `Exp.fold` preserves `denote` and does not increase `depth`.
The existing `gen_ok` structural induction (`Proven/Compiler.lean:242`) would be redone for `genTo`/`opnd` (destination + operand-register parameters instead of "result in `T k`").
