# Register-generic step lemmas (`Riscv/Steps/Gen*.lean`)

One lemma per RV64I instruction form, with register numbers (`Fin 32`) and immediates as variables. They
replace the per-register-combination generated files (`Words`, `BranchWords`, `MemWords`, `Arr2Words`).

| file | what | check time |
|---|---|---|
| `GenRegs.lean` | `xpresent`, `rX_bits_ok`, `wX_bits_ok` (the only 32-way splits) | ~17 s |
| `GenTac.lean` | symbolic-field words `c ||| f…`, bit-range lemmas, `gstep` tactic | ~20 s |
| `GenALU.lean` | R-type, I-type, shifts, `lui` (20 lemmas) + encoding lemmas | ~80 s |
| `GenBranch.lean` | 6 branches × taken/not-taken, `jal`, `jalr` | ~50 s |
| `GenMem.lean` | `lb lbu lh lhu lw lwu ld sb sh sw sd`, `gmem` tactic | ~135 s |
| `GenUse.lean` | `step_rop`, `step_mv`, re-derived generated lemmas, `law_mov_any` | ~5 s |

Total ≈ 5 min, versus ≈ 59 min for the generated files (6 + 9 + 29 + 15). Axioms: identical to `compile_ok`
(77, checked by `Testing/scripts/check.sh` for 8 of them).

## Statements

All in `namespace Proven.G`, under `{s} (h : Cfg s) {pc} (hpc : s.regs.get? .PC = some pc) (hok : pcOK pc)`,
conclusion `∃ s', Next s s' npc rd v mem` (`Next`: retired step, `Cfg s'`, PC, `x[j] := if j = rd ∧ j ≠ 0 then v`,
memory). `x0` reads as 0 (`getX s 0 = 0` by `rfl`), writes to `x0` are dropped.

R-type, word `encR f7 f3 rd rs1 rs2` (`Spec/Code.lean`), `npc = pc + 4`, `mem = s.mem`:
- `step_add (rd rs1 rs2) (hrd : rd ≠ 0)` — `getX s rs1 + getX s rs2` (`rd ≠ 0`: `add x0,x0,x2..x5` are `ntl.*` hints)
- `step_sub` `-`, `step_and` `&&&`, `step_or` `|||`, `step_xor` `^^^`,
  `step_sll` `<<< ((getX s rs2).toNat % 64)`, `step_srl` `>>> …`, `step_sra` `.sshiftRight …`,
  `step_slt` `if (getX s rs1).slt (getX s rs2) then 1 else 0`, `step_sltu` `if getX s rs1 < getX s rs2 then 1 else 0`
- `step_rop (op : Op) (hop : op ≠ .eq) (rd rs1 rs2) (hrd : rd ≠ 0) (hi : instrAt s pc (encR op.f7 op.f3 rd rs1 rs2))`
  — value `Op.eval op (getX s rs1) (getX s rs2)` (`GenUse.lean`)

I-type, word `encI f3 imm.toNat rd rs1`, `imm : BitVec 12`, operand `imm.signExtend 64`:
`step_addi` (f3 0), `step_andi` (7), `step_ori` (6, needs `rd ≠ 0`: Zicbop `prefetch.*`), `step_xori` (4),
`step_slti` (2), `step_sltiu` (3). Shifts, `sh : BitVec 6`, word `encI f3 (f6 <<< 6 ||| sh.toNat) rd rs1`:
`step_slli` (1, 0) `<<< sh.toNat`, `step_srli` (5, 0) `>>>`, `step_srai` (5, 0x10) `.sshiftRight`.
`step_lui (rd) (imm : BitVec 20) (hi : instrAt s pc (encU 0x37 rd imm))` — `(imm ++ 0#12).signExtend 64`.

Branches, word `wB f3 (.ofFin rs1) (.ofFin rs2) o` (`Branch.lean`), `o : BitVec 12`, `mem = s.mem`, `rd = 0`:
`beq_t (rs1 rs2 o hi) (hc : getX s rs1 = getX s rs2) : … (pc + boff o) 0 0 s.mem` and `beq_n (hc : ¬…) : … (pc + 4)`;
likewise `bne_t/n`, `blt_t/n` (`(getX s rs1).toInt < (getX s rs2).toInt`), `bge_t/n`, `bltu_t/n`
(`.toNat <`), `bgeu_t/n`.
`step_jal (rd) (o : BitVec 20) (hi : instrAt s pc (wJ (.ofFin rd) o)) : … (pc + joff o) rd (pc + 4) s.mem`.
`step_jalr (rd rs1) (imm) (hi : instrAt s pc (BitVec.ofNat 32 (imm.toNat <<< 20 ||| rs1.val <<< 15 ||| rd.val <<< 7 ||| 0x67)))
(he : (getX s rs1 + imm.signExtend 64).toNat % 2 = 0) : … (getX s rs1 + imm.signExtend 64) rd (pc + 4) s.mem`.

Loads/stores (`GenMem.lean`), words `encL f3 imm rd rs1` / `encS f3 imm rs2 rs1`, hypotheses
`{A} (hA : getX s rs1 + imm.signExtend 64 = A) (ha : 0x80000000 ≤ A.toNat ∧ A.toNat + n ≤ 0x100000000)`,
`(hal : A.toNat % n = 0)` for `n > 1`, bytes `hi : s.mem[A.toNat + i]? = some bi`:
`step_lb` `b0.signExtend 64`, `step_lbu` `b.setWidth 64`, `step_lh`/`step_lhu` `(b1 ++ b0).signExtend/setWidth 64`,
`step_lw`/`step_lwu` `(b3 ++ … ++ b0).signExtend/setWidth 64`, `step_ld` `b7 ++ … ++ b0`;
`step_sb` mem `s.mem.insert A.toNat ((getX s rs2).setWidth 8)`, `step_sh`/`step_sw` successive inserts of
`(getX s rs2).extractLsb' (8*i) 8` at `A.toNat + i`, `step_sd` `storeBytes s.mem A.toNat (le8 (getX s rs2))`.

## How it works

- `rX_bits (.Regidx i) s = .ok (xval s.regs i.toFin) s` given `xpresent s.regs` (from `Cfg`, kept by every
  `insert`), and `wX_bits (.Regidx i) v s = .ok () {s with regs := xset s.regs i.toFin v}`. `sail_eval` freezes
  `rX_bits`/`wX_bits` and rewrites with these.
- A word is `c ||| fX regs imm` (`fR fI fSh fU fS fB fJ`: symbolic fields, zero elsewhere). The decoder's tests on
  bit ranges are decided by `fX_known/_mismatch/_ne/_zero` (concrete mask `KR KI KS KU`), `F_imm` + `fX_rd/_rs1/…`
  give the fields back, `fX_rdne` refutes hint patterns that need `rd = 0` when `rd ≠ 0` is a hypothesis.
  Bit lemmas use the `bits` tactic of `Branch.lean` (no `bv_decide`).
- Encoders `encR/encI/encL` (Nat form) are related to the field form by `encR_eq`, `encI_eq`, `encSh_eq`,
  `encU_eq`, `encL_eq`, `encS_eq`, `jalr_eq` (per-bit `enc_bits`).
- New instruction forms: write the statement and `by genc; gstep` (ALU/branch) or `genm; gmem` (memory).

## Subsumption (G5)

`GenUse.lean` re-derives `Words.step_res`, `Words.step_ret`, `W.inc_*`, `BranchWords.beq_5_6_t`,
`step_jal_0`, `MemSteps.step_ld/step_sd/step_lbu` (without `memD`/`memB`), and the `mov` interface law for ANY
abstract registers (`law_mov_any`, no `MovOK`), all without unfolding the model. Every generated lemma is an
instance of a generic one (with `Next.rd0` for `rd = x0` jumps), so the generated `*Words.lean` files could be
deleted once `Riscv/Direct` and `Riscv/Back/Iface.lean` are switched over (not done: those files are proved and
used; the only extra care is `rd ≠ 0` for `add`/`ori`, which every compiler word satisfies).

## For the optimisation passes

- Widen the interface laws to arbitrary registers: `bin op d a b` with any `d a b` (`step_rop`; `d ≠ x0`),
  `mov` via `step_mv`, immediate forms `binI op d a imm` via `step_addi/andi/ori/xori/slti/sltiu/slli/srli/srai`.
- `li d c`: `lui d hi; addi d d lo` with `hi = (c + 0x800) >>> 12`, `lo = c[11:0]` (32-bit constants), or `addi d x0 c`
  for `|c| < 2048`; 64-bit constants by `slli`/`addi` chains. The value lemma to prove once is
  `(hi ++ 0#12).signExtend 64 + lo.signExtend 64 = c` for 32-bit `c`.
- Loads/stores take any base register and offset: address arithmetic can be folded into the offset
  (`hA` is an equation, so the caller states the address in its own terms).
- Register allocation: `Next.x` gives the full register-file effect; frame conditions come from `j ≠ rd`.
