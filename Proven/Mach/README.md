# `Proven/Mach`: one middle layer, one thin back end per target

Status: kernel-checked, no `sorry`, no `axiom`, no `native_decide`, no `bv_decide`.

```
FRONT (elsewhere)   Lean function ──► Exp / Stmt / AStmt
MIDDLE (this dir)   source ──► List AOp            + all Hoare / loop / memory-separation proofs,
                                                     stated against the interface `Machine` only
BACK (per target)   AOp ──► List (BitVec 32)       + one law per AOp, proved from the target model
```

## Files

| file | layer | what | lines | check |
|---|---|---|---|---|
| `Iface.lean` | middle | `Reg`, `AOp`, `Mem`, `Base`, `Core`, `Machine` (the interface and its laws) | 183 | 0.6 s |
| `Logic.lean` | middle | `runsTo_mono`, `runsTo_loop`, `runsTo_while` (port of `LoopRule.lean`), `next_add`, `codeAt_append`, `codeOK_append`, `At.split`, `Done.trans`, `Set1.*`, `seq_run` | 119 | 0.5 s |
| `Exp.lean` | middle | `mgen8` (AExp), `toA`/`mgenE`/`mcompile` (Exp), `gen_ok`, `genE_ok`, `compile_ok` | 221 | 1.6 s |
| `Stmt.lean` | middle | model-free copy of `Stmt`/`Exec`, `compS`, `compF`, `wf`, `execS_ok`, `compF_ok` | 142 | 0.9 s |
| `Mem.lean` | middle | `Region`, `disjoint`, `bytes`, `Out`, `Mem.upd` lemmas, list-of-blocks lemmas | 112 | 0.5 s |
| `Arr.lean` | middle | `compA`, `compAF`, `wfA`, `RegOK`, `Rel`, `execA_ok`, `compAF_ok` | 279 | 1.8 s |
| `Riscv.lean` | back | `phys`, `enc`, `base`, `core`, the 9 law proofs, `rv : Machine` | 364 | 1.7 s |
| `RiscvExp.lean` | back (corollary) | `code_compile` (same words), `compile_ok'` | 83 | 1.1 s |
| `RiscvStmt.lean` | back (corollary) | `toM`, `code_compS`, `compileS_ok'`, `compileF_ok'`, `gcd_ok'`, `sum_ok'` | 105 | 1.1 s |
| `RiscvArr.lean` | back (corollary) | `code_compA`, `compileAF_ok'`, `sortCode_ok_m`, `sortCode_implements_m` (the last two: the proofs of `SortMachine.lean` copied, ~75 lines, with `compileAF_ok` replaced by `compileAF_ok'`) | 201 | 1.6 s |

Times: `lake env lean` per file, including imports (Lean 4.29.0).  Middle: 1056 lines; RISC-V back end:
364 lines (instance + laws) + 389 lines of corollaries.

**Target independence.** The six middle files import only `Proven/Code.lean` and `Proven/ArrCode.lean`
(pure source languages; no Sail, no `Std`) and each other. All eight (`Code`, `ArrCode`, `Mach/Iface`,
`Logic`, `Exp`, `Stmt`, `Mem`, `Arr`) compile **unchanged** and without warnings under Lean 4.34.1
(`~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean` with `LEAN_PATH` = a scratch dir of their own
oleans, 7 s in all). No per-version diff is needed. Version-fragile pieces were avoided on purpose:
`if_pos`/`dif_pos` (deprecated in 4.34.1) are replaced by `Mach.ite_pos`/`dite_pos'`; `code` and `bytes`
are defined by plain recursion; `simp` is only used as `simp only` with explicit lemmas.

`Proven/Loop.lean` (which defines `Stmt`) and `Proven/MemModel.lean` import the Sail model (through
`BranchWords` / `Spec`), so they cannot be imported by the middle layer: `Stmt.lean` has a model-free copy
of `Stmt`/`Exec` (mapped back by `Riscv.toM`, `exec_toM`), `Mem.lean` a minimal function-based copy of
the memory facts (mapped back by `Riscv.toR`, `bytes_eq`, `rel_toR`, `rel_ofR`).

## The interface (`Iface.lean`)

Abstract registers `Reg := Fin 15`. Middle conventions: `r0..r10` expression temporaries (`Exp` uses all
11, the array compiler `r0..r6`), `r11..r14` = variables `v0..v3`, the array compiler's `v4..v7` = `r7..r10`
(`avar`). Result register of `Exp` functions: `r11`.

```lean
inductive AOp
  | mov (d a : Reg) | li (d : Reg) (c : BitVec 64) | bin (op : Op) (d a b : Reg)
  | sel (d c a b : Reg)        -- d := if c = 0 then b else a  (may clobber a)
  | lbu (d a : Reg) | sb (v a : Reg)
  | bz (c : Reg) (n : Nat)     -- if c = 0 jump n words forward from the op's start
  | jmp (n : Nat)              -- jump n words back
  | ret
```

`Base` (data a target supplies): `S`, `runsTo : S → (S → Prop) → Prop`, `ok` (fixed control state),
`keep` (frame: everything that is not an abstract register, PC or memory), `pcIs`, `get : S → Reg →
BitVec 64`, `mem : S → Nat → Option (BitVec 8)`, `ra`, `retOK`, `instrAt`, `ramLo`, `ramHi`, `bzOK`,
`jmpOK`, `enc : AOp → List (BitVec 32)`, `lenBz`, `lenJmp`.

Derived (middle-defined): `next pc n = pc + 4n`, `codeAt s pc ws` (word `i` at `pc + 4i`), `codeOK pc n`
(4-aligned, `[pc, pc+4n) ⊆ [ramLo, ramHi)`), `inRAM a n`,
`At s pc ws := ok s ∧ pcIs s pc ∧ codeAt s pc ws ∧ codeOK pc ws.length`,
`Done s s' pc' := ok s' ∧ keep s s' ∧ pcIs s' pc'`,
`Set1 s s' d v := ∀ r, get s' r = if r = d then v else get s r`, `Same s s' := ∀ r, get s' r = get s r`.

## What a new target must prove (the ARM to-do list)

`Core` (generic):

| field | statement |
|---|---|
| `runsTo_of` | `P s → runsTo s P` |
| `runsTo_trans` | `runsTo s P → (∀ s', P s' → runsTo s' Q) → runsTo s Q` |
| `keep_refl`, `keep_trans` | `keep s s`; `keep s₁ s₂ → keep s₂ s₃ → keep s₁ s₃` |
| `keep_ra` | `keep s s' → ra s' = ra s` |
| `instrAt_frame` | `(∀ j < 4, mem s' (pc.toNat + j) = mem s (pc.toNat + j)) → instrAt s pc w → instrAt s' pc w` |
| `ramHi_lt` | `ramHi < 2 ^ 64` |
| `len_bz`, `len_jmp` | `(enc (.bz c n)).length = lenBz`, `(enc (.jmp n)).length = lenJmp` |

`Machine` (one law per operation; every law has the hypothesis `At s pc (enc o)` and concludes
`runsTo s fun s' => Done s s' PC' ∧ EFFECT`; `L := (enc o).length`):

| law | operand side conditions | `PC'` | `EFFECT` |
|---|---|---|---|
| `law_mov` | `MovOK d a` = `(d<11 ∧ 11≤a) ∨ (d<7 ∧ 7≤a<11) ∨ (a=0 ∧ 7≤d)` | `next pc L` | `Set1 s s' d (get s a) ∧ mem s' = mem s` |
| `law_li` | `d < 11` | `next pc L` | `Set1 s s' d c ∧ mem s' = mem s` |
| `law_bin` | `d < 10`, `a = d`, `b = d+1` | `next pc L` | `Set1 s s' d (op.eval (get s a) (get s b)) ∧ mem s' = mem s` (all 11 `Op`s) |
| `law_sel` | `d < 9`, `c = d`, `a = d+1`, `b = d+2` | `next pc L` | `get s' d = (if get s c = 0 then get s b else get s a) ∧ (∀ r, r ≠ d → r ≠ a → get s' r = get s r) ∧ mem s' = mem s` |
| `law_lbu` | `d = 0`, `a = 0`, `inRAM (get s a).toNat 1`, `mem s (get s a).toNat = some v` | `next pc L` | `Set1 s s' d (v.setWidth 64) ∧ mem s' = mem s` |
| `law_sb` | `v = 1`, `a = 0`, `inRAM (get s a).toNat 1` | `next pc L` | `Same s s' ∧ mem s' = (mem s).upd (get s a).toNat ((get s v).setWidth 8)` |
| `law_bz` | `c = 0`, `bzOK n` | `if get s c = 0 then next pc n else next pc L` | `Same s s' ∧ mem s' = mem s` |
| `law_jmp` | `jmpOK n` | `pc - BitVec.ofNat 64 (4 * n)` | `Same s s' ∧ mem s' = mem s` |
| `law_ret` | `retOK (ra s)` | `ra s` | `Same s s' ∧ mem s' = mem s` |

(Register side conditions are on `.val`; exact Lean statements: `Iface.lean`, structure `Machine`.)
The operand shapes are exactly those the three middle compilers emit; they are this narrow because the
RISC-V back end proves each law from the existing per-word lemmas (which exist only for these register
patterns). A target with symbolic-register step lemmas can prove more, and the shapes can then be widened
in `Iface.lean` without touching the middle proofs (they only ever *use* these instances).

After that, the corollaries are mechanical (RISC-V: `RiscvExp/Stmt/Arr.lean`): show
`code (compile…) = <the target's existing compiler>` if there is one, and convert `get`/`mem`/`keep` to
the target's own statement (`frame_of`, `mem_of`, `rel_ofR`).

### How ARM (`arm-proofs/Arm/Small.lean`, `Proven/CompilerArm.lean`) would discharge them

- **Hidden state.** NZCV flags, and any scratch register, are *not* abstract registers: make them part of
  neither `get` nor `keep` (ARM `keep s s' := ∀ x ∉ phys image, x[s'] = x[s]`, flags unconstrained). Then
  `cmp` may change flags freely inside a law.
- **compare-and-set** (`ult`, `slt`, `eq` in `law_bin`): `enc (.bin .ult d a b) = [cmp a, b; cset d, lo]`
  (`slt`: `lt`, `eq`: `eq`). The law's statement is about the *op*, so a two-word expansion is fine: prove
  it by chaining the two step lemmas (as the RISC-V back end chains `xor; sltiu` for `eq`, the 1–3 words
  of `genConst`, and the 5 words of `selCode`). `lenBz`/`lenJmp` are the only lengths the middle needs
  to know; every other length is read off `enc` (`code = flatMap enc`, branch distances are computed in
  target words from it).
- **select**: `enc (.sel d c a b) = [cmp c, #0; csel d, b, a, eq]` (or `tst c, c`); ARM satisfies the
  stronger "only `d` changes", which implies the law (it allows `a` to be clobbered; RISC-V needs that for
  its branch-free mask sequence).
- **no zero register in general operand position**: the interface never mentions a zero register.
  `mov d a` is `orr d, xzr, a` (register 31 in `orr` is `xzr`); `li` is a `movz/movk` sequence (any
  length); `bz` is `cbz x, #4n` (`bzOK n := n < 2^18`), `jmp` is `b #-4n` (`jmpOK n := 0 < n ∧ n ≤ 2^25`),
  `ret` is `ret` (`retOK v := v.toNat % 4 = 0`), `lbu`/`sb` are `ldrb w, [x]`/`strb w, [x]`.
- **registers**: choose `phys : Fin 15 → ARM register`, injective, avoiding `x30` (`ra`), `sp`, and with
  `phys r11..r14 = x0..x3` so the result register `r11` is `x0`.

**Lines a second target writes.** RISC-V: `Riscv.lean` is 364 lines (register map + `enc` + `Base`/`Core`
instance ~70, `Next`→abstract-effect helpers ~45, the nine laws ~250), on top of per-word step lemmas that already existed. An ARM
instance with existing per-instruction lemmas of the same shape should be of the same order (~300–400
lines), plus ~100–200 lines per re-derived corollary if an existing ARM statement must be matched
literally (the RISC-V corollaries: 83 + 105 + 126 lines, plus the 75 copied sort lines). The middle 1056
lines are not rewritten.

## Kernel-checked results

Middle (from the laws only; `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`):
`Machine.gen_ok`, `genE_ok`, `compile_ok`, `execS_ok`, `compF_ok`, `execA_ok`, `compAF_ok`,
`Core.runsTo_loop`, `runsTo_while`.

RISC-V (`rv : Machine`; same axioms as `Proven.compile_ok`, checked by comparing the sorted axiom lists):
`compile_ok'`, `compileS_ok'`, `compileF_ok'`, `gcd_ok'`, `sum_ok'`, `compileAF_ok'`, `sortCode_ok_m`,
`sortCode_implements_m` — each has *exactly* the statement of the original (`example : type_of% @new =
type_of% @old := rfl` at the end of each file). The code is identical, not just equivalent:
`code_compile : rv.code (mcompile e) = compile e`, `code_compS`, `code_compF`, `code_compA`, `code_compAF`
(theorems, under the existing `wf` side conditions). Four-way test on the new route:
`asm/triple-data/triple_mach.lean` (asserts the words equal `compile e`) → `asm/triple.py`: 18/18 cases,
Lean == RV64 QEMU == RV64 Sail emulator == AArch64 QEMU.

## What does not fit yet

- **Spill slots / merge sort (`BStmt`, `Proven/Arr2*.lean`, `compileBF_ok`, `msortCode_implements`)**: not
  done. `Arr2Code.lean` imports `Proven/Loop.lean` (model), and, more importantly, the interface lacks:
  (1) 8-byte loads/stores at a frame offset (`ld t_k, 8(j+1)(gp)`, `sd t0, 8(j+1)(gp)`): new ops
  `ldS (d : Reg) (j : Nat)` / `stS (j : Nat) (v : Reg)` with laws over a target value `fp s` (frame base)
  and `bytes (mem s) (fp s + 8(j+1)) 8 = le8 v`; (2) the frame itself: ops `enter N` / `leave` whose laws
  read `sp`, compute `fp' = alignDown(sp, 8) - 8(N+1)`, save/restore the register holding `fp` (RISC-V
  `gp`, callee-saved) in memory at `fp'`, zero the slots, and a `keep` that is *temporarily* broken for
  that register between `enter` and `leave` (so `keep` would need a frame-aware variant, e.g.
  `keepF fp`); (3) an extra region (the frame) in the separation side conditions. With those four laws
  the `BStmt` middle proof would follow `Arr.lean` (variables `≥ 8` related to slot bytes instead of
  registers).
- `compileStore_ok` (`MemCompiler.lean`) needs an 8-byte store op (`sd t0, 0(s1)`) and `s1` as an abstract
  register; not attempted.

## Room for optimisation passes

Nothing here fixes the code shape beyond the laws: the middle produces a `List AOp`, and `code M ops` is
its encoding. A pass `opt : List AOp → List AOp` is proved once, against the interface, by showing that
for every `M : Machine` running `code M (opt ops)` yields the same `Done`/register/memory post-conditions
as `code M ops` (e.g. a lemma of the shape of `execS_ok` for `opt ∘ compS`). Planned directions and what
each needs: *direct operands* (`bin op d a b` with `a`, `b` any registers, no `mov` into temporaries) —
widen the side conditions of `law_bin`/`law_mov` (RISC-V: step lemmas for more register triples, or
symbolic-register step lemmas as `Branch.lean` does for offsets); *short constants* — `li` is already one
op with a target-chosen expansion (`addi`/`lui` on RISC-V, `movz` on ARM), only `enc` and `law_li`
change; *register allocation* — `Reg` is a finite type and the middle's register conventions are plain
functions (`rk`, `avar`), so an allocator is a renaming pass proved against `Set1`/`Same`.
