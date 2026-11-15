# The optimising back end (`Compiler/Wide.lean`, `Compiler/Opt/`, `Riscv/Back/{Wide,Opt}.lean`)

Branch `opt`. Status lines say exactly what is kernel-checked and what is measured; see "Status" at the end.

```
source (Exp / Stmt / AStmt)
  │  selection        Compiler/Opt/Sel.lean     gen_ok      AExp → IR over virtual registers (Nat)
  ▼
IR  Code Nat          Compiler/Opt/IR.lean      big-step Exec, no program counter
  │  assignment       Compiler/Opt/Alloc.lean   map_ok      renaming f : Nat → Reg, checked injective (injOn)
  ▼
IR  Code Reg
  │  lowering         Compiler/Opt/Lower.lean   low_ok      → List WOp, checked wf; from the Wide laws
  ▼
wide ops  List WOp    Compiler/Wide.lean        interface `Wide` (extends `Core`; `Iface.lean` untouched)
  │  encoding         Riscv/Back/Wide.lean      rvw : Wide  one law per WOp from the generic step lemmas
  ▼
words
```
`Compiler/Opt/Fn.lean` (`fn`, `fn_ok`) composes assignment + lowering + `ret`; `Compiler/Opt/{Exp,Stmt,Arr}.lean`
give `optE/optS/optA` with `optE_ok/optS_ok/optA_ok` (conclusions literally those of `Machine.compile_ok`,
`compF_ok`, `compAF_ok`); `Riscv/Back/Opt.lean` gives `compileOpt`, `compileOptS`, `compileOptA :
… → Except String (List (BitVec 32))` and `compileOpt_ok`, `compileOptS_ok`, `compileOptA_ok` with the conclusions
of `compile_ok`, `compileF_ok`, `compileAF_ok`. The side conditions of the old theorems (`depth < 11`, `wf`) are
replaced by the single hypothesis `compileOpt… = .ok ws`: everything the proofs need is a decidable check made by
the compiler (`injOn`, `Wide.wf`, `okA`), which returns `.error` otherwise.

## Wide operations (`Compiler/Wide.lean`)

```lean
inductive Cond | eq | ne | ltu | geu | lt | ge          -- Cond.eval, Cond.neg, eval_neg
inductive WOp
  | mov (d a : Reg) | li (d : Reg) (c : BitVec 64)
  | bin (op : Op) (d a b : Reg)                        -- ANY registers
  | bini (op : Op) (d a : Reg) (c : BitVec 64)         -- law under `immOK op c`
  | lbu (d a : Reg) (off : BitVec 64) | sb (v a : Reg) (off : BitVec 64)   -- law under `offOK off`
  | br (c : Cond) (a : Reg) (b : Option Reg) (back : Bool) (n : Nat)       -- `none` = compare with zero
  | jmp (back : Bool) (n : Nat) | ret
```
`structure Wide extends Core`: `wenc`, Bool-valued `immOK`, `offOK`, `brOK`, `jOK`, lengths `lenBr`, `lenJ`
(independent of operands), and laws `w_mov w_li w_bin w_bini w_lbu w_sb w_br w_jmp w_ret`, each
`At s pc (wenc o) → runsTo s (Done s s' PC' ∧ EFFECT)` as in `Machine`, with no register side conditions.
`w_br`: `PC' = if c.eval (get s a) (getO s b) then tgt pc back n else next pc lenBr`.
`w_sb` takes `writable s addr` (as `Base.law_sb` since main gained `Base.writable`); hence `low_ok`/`fn_ok`/`body_ok`
take `hwr : ∀ a, ram a → ∀ s, ok s → writable s a`, `Wide.RegOK` has the writable clause of `Machine.RegOK`,
`WideF.enterOK_frame` also gives writability of the frame, and `WideF.optB_ok` has `hRw` (as `compBF_ok`'s layout).

RISC-V instance (`Riscv/Back/Wide.lean`, `rvw`): `mov` = `add d,x0,a`; `bin` = R-type word (`eq`: `xor; sltiu 1`);
`bini`: `addi/andi/ori/xori/slti/sltiu` for 12-bit `c`, `sub c` = `addi -c`, shifts `slli/srli/srai` (any `c`, amount
`c mod 64`), `eq c` = `xori; sltiu 1`; `lbu/sb` 12-bit offset; `br` = `beq/bne/blt/bge/bltu/bgeu a, b|x0`, forward
`2n < 2048` / backward `0 < n, 2n ≤ 2048`; `jmp` = `jal x0`; `li` = a plan of `addi d,x0,i | lui | addi d,d,i | slli`
found by an untrusted search (`liPlan`: 1 word for 12-bit, ≤ 2 for 32-bit, `lui/addi` + `slli/addi` chain for 64-bit)
and CHECKED by evaluation (`liGood`); fallback `liSlow` (one bit at a time, proved `runLi_slow`).

## IR (`Compiler/Opt/IR.lean`)

```lean
inductive Arg ρ | r (x : ρ) | i (c : BitVec 64)
structure Tst ρ where c : Cond; a b : Arg ρ
inductive Ins ρ | set d a | bin op d a b | lbu d a off | sb v a off
inductive Code ρ | skip | ins i | seq a b | when t body | loop pre t body     -- while (pre; t) do body
```
State `St ρ = (ρ → BitVec 64) × Mem`; `Exec ram : Code ρ → St ρ → St ρ → Prop` (loads/stores only at `ram`
addresses; `Exec.mem_out`: memory changes only there).

## Passes and their theorems

| pass | file | theorem (proved once, target-independent) |
|---|---|---|
| selection: operands in place, results to destination, immediates, compare/branch fusion, conditional assignment | `Sel.lean` | `gen_ok e : (∀ d k σ, Agree env e σ → IntoSpec ram ((gen e).1 d k) d k σ (e.denote env)) ∧ (∀ k σ, Agree env e σ → TstSpec ram ((gen e).2 k) k σ (e.denote env))` |
| statements | `Stmt.lean`, `Arr.lean` | `irS_ok : Exec p σe σe' → (∀ i, σ.reg i = σe i) → ∃ σ', IR.Exec ram (irS p) σ σ' ∧ …`; `irA_ok` likewise with `RelA` (heap blocks ↔ memory regions) |
| register assignment | `Alloc.lean` | `map_ok : (inj on U) → Exec ram c σ σ' → regs c ⊆ U → Ren f U σ τ → ∃ τ', Exec ram (c.map f) τ τ' ∧ Ren f U σ' τ'` |
| lowering (immediate forms / `li` into the scratch register, `when` = forward branch, bottom-tested loops) | `Lower.lean` | `low_ok : Exec ram c σ σ' → wf sc c → ok s → pcIs s pc → Frag ram s pc (W sc c) → Rel sc s σ → RunTo ram s (next pc (W sc c).length) (Rel sc · σ')` |

What the task list called (a) operands in place, (b) immediates and constant operands, (d) comparison/branch fusion,
(e) cheaper select are done INSIDE selection (tree level), not as separate IR→IR passes: on tree-shaped sources with
variables pinned to registers by the calling convention this gives the same code with one proof.
`ite c a b` into `d`: `d := b; if c then d := a` (lazily evaluated `a`; a temporary when `d` occurs in the test or in
`a`; `if ¬c then d := b` when `a` is `d`; `if c then d := a` when `b` is `d`).
Not done: constant folding beyond `op c₁ c₂` (lowering folds that), dead-code elimination (all source variables are
outputs in the current specs, so nothing is dead), a liveness-based allocator / spill slots (`BStmt`), strength
reduction.

Register assignment used: variable `i ↦` its convention register, temporary `k ↦ r k`; `Exp`/`Stmt`: 10 temporaries,
scratch `r10`; `AStmt`: 6 temporaries, scratch `r6`. The assignment function is not trusted: `injOn` checks it on the
registers the code mentions and `wf` rejects code that touches the scratch register.

## What an ARM instance must prove

A `Wide` value for the AArch64 model: the `Core` part (already needed for `Machine`) plus the nine `w_*` laws with
arbitrary registers. Encodings that satisfy the laws: `bin` = the 3-register instruction (`ult/slt/eq` =
`cmp; cset`), `bini` = `add/sub #imm12`, logical immediates where encodable, `lsl/lsr/asr #imm` (`immOK` decides),
`li` = `movz/movk` (any checked plan), `lbu/sb` = `ldrb/strb [a, #off]` (`offOK off := off < 4096`), `br c a b` =
`cmp a, b; b.cond` (`lenBr = 2`) with `b = none` as `cmp a, #0` (or `cbz/cbnz` for `eq/ne`, but `lenBr` must not
depend on the operands), `jmp` = `b`, `ret`. Flags are not part of `get`/`keep`, as for `Machine`. Nothing in
`Compiler/Opt/` changes.

Short-circuit loop tests: a loop condition `ite c a (const 0)` (i.e. `c ≠ 0 ∧ a ≠ 0`) becomes IR `loop2 pre₁ t₁ pre₂ t₂
body`, lowered as `jmp test; body; test: pre₁; br ¬t₁ exit; pre₂; br t₂ body` (`Sel.loopCode`, `loopCode_exit`,
`loopCode_iter`; `low_ok'` third component).

## Status (commit of this file)

Kernel-checked (`lake build Riscv.Back.Opt Riscv.Back.OptArr`, no `sorry`/`axiom`/`native_decide`/`bv_decide`):
- middle layer, from the `Wide` laws only: `Wide.low_ok`, `Sel.gen_ok`, `IR.map_ok`, `Wide.fn_ok`, `Wide.optE_ok`,
  `Wide.optS_ok`, `Wide.optA_ok` (`#print axioms Wide.low_ok`: `propext`, `Classical.choice`, `Quot.sound`);
- RISC-V: `rvw : Wide` (all nine laws), `compileOpt_ok`, `compileOptS_ok`, `compileOptA_ok`; `#print axioms` of each
  is the same 77-axiom list as `Proven.compile_ok` (compared by hash).
Not proved / not done: word arrays (`load64`/`store64`) in the optimised pipeline, the pipe front end on the new pipeline, a liveness-based
allocator, DCE, strength reduction, ARM instance of `Wide`.

Tested: `Testing/asm/triple-data/triple_opt.lean` 18/18 cases four-way (Lean == RV64 QEMU == RV64 Sail emulator ==
AArch64 QEMU; the ARM words are the unoptimised ARM backend's); `Testing/asm/fuzz_opt.lean` seeds 31–34, 300 cases ×
100 inputs each = 120,000 pairs, 0 mismatches (the emitter falls back to `compile e` when `compileOpt e` is an
error; how often was not counted); `loop_test.py` on `opt-words/{gcd,loopsum}.words` 300/300 each (QEMU + Sail
emulator); array programs: outputs checked against the Python model by `bench/bench.py` on QEMU only.

Measured (`python3 bench/bench.py sum take inc gcd loopsum insertion demo demo2 --opt-only`; RV64 QEMU `-icount`,
instructions inside the function; words from `Testing/asm/emit_opt_{loops,arr}.lean` → `Testing/asm/opt-words/`):

| function | ours before | ours optimised | gcc -O2 (bench/NOTES.md) | opt / gcc |
|---|---|---|---|---|
| sumBytes, per element (n = 100000) | 20.0 | 5.0 | 4.0 | 1.25 |
| take, per element | 21.0 | 6.0 | 5.0 | 1.2 |
| map (+1), per element | 25.0 | 7.0 | 6.0 | 1.17 |
| loop sum (`sumDown`), per iteration | 13.0 | 3.0 | 3.0 | 1.0 |
| gcd (100000, 3), per step | 36.0 | 6.0 | 3.0 | 2.0 |
| gcd (832040, 514229), whole call | 1058 | 178 | 77 | 2.3 |
| insertion sort, per element, n = 1000 | 10520 | 3911 | 1715 | 2.3 |
| `demo` expression, whole call | 47 | 8 | 8 | 1.0 |
| `demo2` expression, whole call | 29 | 9–13 | 9 | 1.0–1.4 |

Code size (words): loopsum 6, gcd 10, demo 8, demo2 13, sum 9, take 12, inc 13, insertion sort 38.
Merge sort: see the spill-slot section below.

## Drop-in entry points (kernel-checked)

`compileO : Exp → List (BitVec 32)`, `compileFO : Stmt → List (BitVec 32)` (`Riscv/Back/Opt.lean`),
`compileAFO : List (Fin 8) → AStmt → List (BitVec 32)` (`Riscv/Back/OptArr.lean`): the optimised words when
`compileOpt…` succeeds, the old words otherwise. `compileO_ok`, `compileFO_ok`, `compileAFO_ok` have the statements
of `compile_ok`, `compileF_ok`, `compileAF_ok` with the function name replaced (same hypotheses `depth < 11` / `wf`,
used only in the fallback case). A front end switches by replacing the function and theorem names; if it relies on
`compileAF bv p` definitionally (e.g. on its length), those facts must be restated for `compileAFO`.
`compileBF` (spill slots) has no optimised counterpart yet: the frame/slot interface `MachineF`
(`Compiler/Frame.lean`) has no RISC-V instance on branch `stable` at the time of writing.

## Spill slots: `BStmt`, merge sort (kernel-checked)

Added for the spill-slot language (`Compiler/BLang.lean`, byte blocks; `load64`/`store64` are rejected, i.e. the
drop-in falls back to the old compiler):
- `Wide`: two more operations `ldS d j`, `stS j v` (ANY register; laws `w_ldS`, `w_stS` shaped as `MachineF.law_ldS`
  / `law_stS` without the register restrictions), a frame register `fr` with `keep_fr`, `maxSlots`. RISC-V:
  `ld d, 8(j+1)(gp)` / `sd v, 8(j+1)(gp)` from `G.step_ld` / `G.step_sd`. IR: `Ins.ldS`, `Ins.stS` (slot contents live
  in IR memory at `fp + 8 (j + 1)`; `Exec` takes the frame base `fp`).
- Selection now works on `Sel.SExp` (a variable is `var i`, register-resident, or `slot j`); `AExp` goes through
  `Sel.ofA`, `BExp` through `toS sp` (`Compiler/Opt/BSel.lean`) where `sp j` says that variable `8 + j` is spilled. A
  spilled variable costs one `ldS` per read and one `stS` per write; the others are virtual registers.
  `irB_ok : BExec p σ σ' → okB N bv p → RelBI sp N fp bv R σ τ → ∃ τ', IR.Exec (ramB N fp R) fp (irB sp bv p) τ τ' ∧
  RelBI sp N fp bv R σ' τ'`.
- `Compiler/Opt/BFn.lean`: `WideF extends Wide` (+ `enter`/`leave` laws, copied in shape from `MachineF`), code
  `enter N; locals-in-registers := 0; body; leave; ret`, `WideF.optB_ok` (the shape of `MachineF.compBF_ok`).
- `Riscv/Back/OptB.lean`: `rvwF : WideF` (frame laws taken from `rvF`), `compileOptB N bv p : Except String …`,
  `compileOptB_ok` (conclusion and hypotheses of `compileBF_ok`, minus `hbv`/`wf`, plus `compileOptB … = .ok ws`),
  drop-in `compileBFO` / `compileBFO_ok` (statement of `compileBF_ok` with the name replaced).
  `#print axioms`: the same 77 as `compileBF_ok`; `WideF.optB_ok`: the 3 standard ones.
- Register choice (untrusted, checked): `T` temporaries `r0..r(T-1)`, scratch `r6`, the `6 - T` most used locals
  (loop bodies weighted 8) in `rT..r5`, the rest in slots; `T = 1, 2, …` tried in order, the first that passes
  `injOn`/`wf` wins. Merge sort (`compileOptB 7 [0, 2, 3] msortProg`): `T = 4`, locals `11` and `8` in registers,
  5 locals in slots.

Merge sort measured (`bench/bench.py msort --opt-only`, instructions per element):

| n | ours before | ours optimised | hand (`sort.S`) | gcc -O2 | opt / gcc |
|---|---|---|---|---|---|
| 100 | 606.4 | 244.8 | 127.1 | 101.8 | 2.4 |
| 1000 | 920.3 | 364.9 | 166.1 | 132.2 | 2.8 |
| 100000 | 1394.0 | 548.5 | 281.4 | 221.2 | 2.5 |

Code size 245 words (before: 442). Tested: `WDIR=opt-words python3 Testing/asm/msort_test.py check 60`: 60/60
(QEMU == Sail emulator == sorted; guard bytes, gp, sp, frame writes checked by that script).
Open: only 2 of 7 locals fit in registers because the expressions need 4 temporaries; callee-saved registers
(saved in the frame) or a liveness-based assignment would remove the remaining slot traffic.

Update (operand order + assignment search): `Sel.ops2` computes the operand needing more temporaries first
(`need`, Sethi–Ullman style; `ops2_ok` proved); `Riscv/Back/OptB.lean` tries 120 candidate assignments (T temporaries ×
subsets of the 8 most used locals), cheapest first, first passing the proved checks wins. Merge sort: T = 3, locals
`11, 8, 10` in registers; 231 words; 60/60 `msort_test.py check`; instructions per element n = 100 / 1000 / 100000:
221.8 / 329.9 / 495.5 (gcc -O2 101.8 / 132.2 / 221.2: 2.2 / 2.5 / 2.2×). Emitting takes 15 s (interpreted).

Fuzz path count (coordinator item 2): `Testing/asm/fuzz_opt.lean` now tags each case `_opt` / `_fb`. Seeds 31–34
(300 cases × 100 inputs each), compiler at 7f96615: 1200/1200 cases on the optimised path, 0 fallbacks; four-way
check 120,000 pairs, 0 mismatches; triple_opt 18/18.

## Simplification in selection (kernel-checked: `Sel.simpS`, `simpS_denote`, `Agree.simp`; `into`/`tst` apply it)

Two pure rewrites, bottom-up: `x + x ↦ x << 1`; `op x (ite c a b) ↦ ite c (op x a) (op x b)` when `x`, `a`, `b` are
leaves. And a conditional-assignment arm (inside the `when`) now reuses the caller's temporaries (`iteCode … d k`):
the test's temporaries are dead there. Effect on merge sort: 2 temporaries suffice, so the 4 hottest locals
(`11, 8, 9, 10`) are in registers (search picks `(2, [3, 0, 1, 2])`), 215 words.

| merge sort, per element | n = 100 | 1000 | 100000 |
|---|---|---|---|
| ours optimised | 193.7 | 285.9 | 427.5 |
| gcc -O2 | 101.8 | 132.2 | 221.2 |
| ratio | 1.90 | 2.16 | 1.93 |

`msort_test.py check 60`: 60/60 (QEMU == Sail). Other rows unchanged (sum 5.0, take 6.0, map 7.0, loop sum 3.0,
gcd 6.0/step, insertion 3911/elt at 1000). Axioms of `compileOptB_ok`, `compileBFO_ok`, `compileOptA_ok`: the same 77 as
`compileBF_ok` (hash). Callee-saved registers not added: after this change the merge-sort inner loop has no slot
traffic left in it; remaining spills (`12, 13, 14`) are in the outer loops.
Fuzz of aff977e: seeds 41–44, 1200/1200 cases optimised, 0 fallbacks, 120,000 pairs four-way 0 mismatches;
triple_opt 18/18; loop_test gcd/sum 300/300 (QEMU + Sail).

## Word arrays (kernel-checked)

`Wide` + IR + renaming + lowering: `ld d a off` / `sd v a off` (8 bytes, 8-aligned, any registers; RISC-V laws
`w_ld`/`w_sd` from `G.step_ld`/`G.step_sd`). Selection: `irB_ok` covers `load64`/`store64` (`RelBI` carries the word
heap, writable addresses `R ++ W ++ slots`); `WideF.optB_ok` takes byte and word blocks. Drop-in for the middle
compiler: `Mach.Riscv.compBFO N bv wv p` with `compBFO_ok'`, the statement of `rvF.compBF_ok` with
`rvF.codeF (rvF.compBF N bv wv p)` replaced by `compBFO N bv wv p` (`Riscv/Back/OptB.lean`).

CRC-32 (`crcP` copied from main's `Riscv/Examples/Crc.lean`, `Testing/asm/emit_opt_crc.lean`; `bench/bench.py`
model `zlib.crc32`, C version `c_crc` added to `bench/bench.c`), RV64 QEMU, outputs checked at n = 0, 1, 100, 1000,
100000 (not run on the Sail emulator):

| | words | n = 0 (table build) | per byte (n = 100000) |
|---|---|---|---|
| old `rvF.compBF` | 823 | 142,053 | 58.0 |
| optimised `compBFO` | 141 | 18,477 | 11.0 |
| gcc -O2 | — | 15,891 | 10.0 |

## Integration on `main` (2026-11-14): `Implements1` on the optimised words, front end switched

Kernel-checked (`Riscv/Back/Implements1Opt.lean`, `Riscv/Examples/Implements1Opt.lean`; `#print axioms`: the 77 of
`crc32_implements1`, `Testing/scripts/axioms_k.lean`):
- `compileAFO_okK`, `compileBFO_okK`: `compileAFO_ok` / `compileBFO_ok` concluding `rv.keep` (as `compileAF_okK`,
  `compileBF_okK`); `implements1_of_execO`: `implements1_of_exec` with the same hypotheses for `compBFO N [0, 3] [2]`.
- optimised codes `takeCodeO k`, `incCodeO`, `sumCodeO`, `Crc.crcCodeO` (`compBFO`), `sortCodeO` (`compileAFO`),
  `msortCodeO` (`compileBFO`), with `take_implements1O`, `inc_implements1O`, `sum_implements1O`,
  `Crc.crc32_implements1O`, `sortCode_implements1O`, `msortCode_implements1O`: the statements of the unoptimised
  theorems with the code names suffixed `O` (same `space`, `retLen`). All six take the optimised path (words:
  take 66 → 33, inc 58 → 32, sum 177 → 51, CRC-32 823 → 141, insertion sort 104 → 38, merge sort 442 → 215).
- Tested: `Testing/asm/impl1_test.py NAME 100` (QEMU == Sail == model in the `Implements1` convention, exact-size
  output and work blocks with guards, gp/sp restored, a1 for `take5`), unoptimised and `WDIR=impl1-opt-words`:
  see `Testing/asm/impl1-opt-words/RESULTS.txt`.
- The list front end: `compileP`, `compileXA` emit `compileAFO`, `compileXB` emits `compileBFO`; `compileP_ok`,
  `compileXA_ok`, `compileX_ok`, `compileP_implements1` re-proved with unchanged statements. 36/36 examples
  `pipe_test.py NAME 300` pass (`Testing/asm/pipe-words/RESULTS.txt`; e.g. `sort` 446 → 168 words, `twosort` 1144 → 476).

Measured (`python3 bench/bench.py sum take inc gcd loopsum insertion msort crc --quick`, RV64 QEMU `-icount`,
instructions inside the function; "unoptimised" = the words in `Testing/asm/{arr,loop}-words/`, "optimised" =
`Testing/asm/opt-words/` (the same programs through the optimising back end; merge sort and CRC-32 are exactly
`msortCodeO`, `crcCodeO`); gcc -O2 = `riscv64-linux-gnu-gcc -O2` of `bench/bench.c`, measured in the same run and
equal to `bench/NOTES.md`):

| function | unoptimised | optimised | gcc -O2 | opt / gcc |
|---|---|---|---|---|
| sum of bytes, per element (n = 100000) | 20.0 | 5.0 | 4.0 | 1.25 |
| take, per element (n = 100000) | 21.0 | 6.0 | 5.0 | 1.20 |
| map (+1), per element (n = 100000) | 25.0 | 7.0 | 6.0 | 1.17 |
| loop sum (`sumDown`), per iteration (n = 100000) | 13.0 | 3.0 | 3.0 | 1.00 |
| gcd (100000, 3), per step | 12.0 | 2.0 | 1.0 | 2.0 |
| gcd (832040, 514229), whole call | 1058 | 178 | 77 | 2.3 |
| insertion sort, n = 1000, per element | 10520 | 3911 | 1715 | 2.28 |
| insertion sort, n = 10000, per element | 107833 | 40120 | 17557 | 2.29 |
| merge sort, n = 100, per element | 606.4 | 187.5 (was 193.7) | 101.8 | 1.84 |
| merge sort, n = 1000, per element | 920.3 | 279.9 (was 285.9) | 132.2 | 2.12 |
| merge sort, n = 100000, per element | 1394.0 | 421.5 (was 427.5) | 221.2 | 1.91 |
| merge sort, branchy merge (`msortCodeO2`), n = 100 / 1000 / 100000, per element | — | 107.8 / 155.2 / 241.9 | 101.8 / 132.2 / 221.2 | 1.06 / 1.17 / 1.09 |
| CRC-32, n = 100000, per byte (incl. building the table) | 59.4 | 11.2 | 10.2 | 1.10 |
| CRC-32, n = 100, whole call | 147853 | 19577 | 16898 | 1.16 |

(gcd (100000, 3): whole call 1200110 / 200020 / 100010 instructions, divided by 100000 loop iterations here; the
earlier table above divides differently; the whole-call numbers agree with it.)

## Profile against gcc -O2, and liveness-checked register assignment (2026-11-15)

Profile (exact per-instruction counts from a small RV64I interpreter over the emitted words; same random bytes as
`bench.py`; agrees with the QEMU `-icount` numbers to the instruction). Merge sort before this change
(`msortCodeO`, 215 words), instructions per element:

| n | total | inner merge loop | of which: ALU / address add / branch / compare / lbu / mov / sb | outer loops | of which slot ld/sd |
|---|---|---|---|---|---|
| 100 (7 passes) | 193.7 | 164.4 | 49.0 / 33.6 / 29.0 / 21.0 / 14.0 / 10.8 / 7.0 | 29.2 | 14.5 |
| 1000 (11 passes) | 285.9 | 257.8 | 77.0 / 52.7 / 45.0 / 33.0 / 22.0 / 17.1 / 11.0 | 28.1 | 14.1 |
| 100000 (17 passes) | 427.5 | 399.5 | 119.0 / 83.6 / 69.0 / 51.0 / 34.0 / 25.8 / 17.0 | 28.0 | 14.0 |

So one merge step (one output byte of one pass) is 23.4 instructions, gcc -O2's `ms_buf` common path is ~11
(14.5 per element-pass incl. its outer loops). Where the extra ~12 go: the SOURCE program `msortProg` is a
branch-free merge (two loads per step, `src[p < mid ? p : k]` and `src[q < e ? q : k]`, the take flag
`(p<mid) & ((q<e & y<x) ^ 1)` computed arithmetically, both indices updated with `t` / `t ^ 1`, a
select for the stored value), while gcc compiles a branchy three-loop merge (one load per input byte, no flag).
Counted against what this source needs, our step is within ~1.5 instructions of the best schedule (the remaining
waste: `p<mid` and `q<e` are compared twice, once as the select branch and once as a value, and the stored-value
select costs a `mov`); CSE of the two compares needs two more registers that are not free. Outer loops: 28
per element, half of it slot traffic of `i`, `w`, `ww` (and `min(i + w, n)` evaluates `i + w` twice).
Insertion sort (`sortCodeO`): 16 instructions per inner step (`0x4c..0x88`), 3911 per element at n = 1000;
gcc ~7 per step: again the source (`innerBody`: index `j ? j-1 : 0`, flag `cE` computed with `and`,
store of a select, `j -= t`) plus one `li 0` into the scratch register for `0 <u j` (no zero register in `Wide`).
gcd: 6 per step vs gcc 3 (`a2 := a0 <u a1` is a source variable; two conditional assignments, loop test
`a0 ≠ 0 ∧ a1 ≠ 0` re-tested in full each step; gcc tests only the operand that changed).
Conclusion: the remaining factor ~2 is mostly in how the source programs are written (chosen for simple
source-level proofs), not in the code generator. The large lever left is a branchy merge-sort source program
(`BStmt`, proved equal to `List.mergeSort`), compiled by the same back end; on the compiler side, more
registers (callee-saved `s1..s11`, see below).

Callee-saved registers: not done. `Reg := Fin 15` (`Compiler/Iface.lean`) is the whole abstract register file
(`rk 0..6` = t0–t2/t3–t6, `avar` = a0–a7) and every `Wide` law has `keep s s'` (callee-saved registers unchanged)
inside `Done`, so `s1..s11` cannot be named by a `WOp` without changing `Iface.lean`/`Done` or giving `Wide` a
second register type and per-function save/restore laws, i.e. reworking every law and the RISC-V instance. An
`ldS`/`stS` slot moved into an `s` register would cost the same instruction count (`mv` instead of `ld`).

Implemented (kernel-checked; `#print axioms`: `propext`, `Quot.sound`):
- `Compiler/Opt/Live.lean`: `chk f c L` (registers live before `c` when `L` is live after; fails unless every
  definition `d` leaves the live registers other than `d` (and the source of a move `d := a`) in registers
  `≠ f d`; loop invariants from an untrusted bounded fixpoint `lv`, checked as a post-fixpoint), and
  `chk_ok : Exec ram fp c σ σ' → chk f c L = some Lin → Ren f (· ∈ Lin) σ τ → ∃ τ', Exec ram fp (c.map f) τ τ' ∧
  Ren f (· ∈ L) σ' τ'`; `dropMov` (removes `d := d`) with `dropMov_ok`.
- `Compiler/Opt/Fn.lean`: `allocOK f vars c := injOn f (vars ++ c.regs) || (chk f c vars).isSome`, `allocOK_run`;
  `Wide.body` and `Wide.fn` now check `allocOK` and lower `dropMov (c.map f)`. `body_ok`, `fn_ok` and everything
  above them (`optE/S/A/B_ok`, `compileO/FO/AFO/BFO_ok`, `compBFO_ok'`, the `…_implements1O` theorems,
  `compileP_ok`, `frontx_implements`) keep their statements unchanged (statement hashes equal; closures differ,
  fingerprints re-frozen).
- `Compiler/Opt/Color.lean` (untrusted): interference from the same liveness, greedy colouring (most constrained
  first, move partners preferred, the variables' convention registers offered first). `Riscv/Back/OptB.lean`:
  `pickB` tries liveness colourings first (no local spilled, then one, then two, cheapest by weighted uses), then
  the old injective candidates; `pickB_ok`. Merge sort: `i` (dead during the merge loop) now shares a register;
  `w`, `ww` stay in slots; 215 → 195 words.

| merge sort, per element | n = 100 | 1000 | 100000 |
|---|---|---|---|
| before (this section's profile) | 193.7 | 285.9 | 427.5 |
| liveness-checked assignment | 187.5 | 279.9 | 421.5 |
| gcc -O2 | 101.8 | 132.2 | 221.2 |
| ratio | 1.84 | 2.12 | 1.91 |

Other rows unchanged (Exp/Stmt/AStmt pin every variable to its convention register, so there is nothing to
share; only `d := d` moves disappear). Why not more: a selection temporary is ONE virtual register for the whole
program (`tk k`), so it interferes with everything and cannot use a variable's register where that variable is
dead; splitting temporaries per statement (or validating a per-occurrence assignment, i.e. `chk` over a pair
relation) would put `w` in a register too (est. a further ~6 per element). Tested: `msort_test.py check 60` on
`opt-words` 60/60; `impl1_test.py` take5/inc/sum/crc/sort/msort 100/100 each (QEMU == Sail == model);
`pipe_test.py` on the 7 changed `pipe-words` 100/100 each and the 29 changed `pipe-words1` (`I1=1`) 50/50 each.
Fuzz (`fuzz_opt.lean`, seeds 61, 62, 300 cases × 100 inputs): 600/600 cases on the optimised path, 0 fallbacks;
60,000 pairs four-way (Lean == RV64 QEMU == Sail emulator == AArch64 QEMU), 0 mismatches.

## Branchy merge sort source program (2026-11-15)

`Riscv/Examples/MsortB.lean`: `msortProgB`, the same bottom-up ping-pong program as `msortProg` with the merge of
two runs replaced by three loops: `while p < mid ∧ q < e` (short-circuit, compiled as `loop2`) loads `x := src[p]`,
`y := src[q]` and does `q := y < x ? q + 1 : q; p := y < x ? p : p + 1; x := y < x ? y : x; dst[k] := x; k++`
(each conditional assignment with the destination as one arm is a compare-and-branch over one instruction, so this
is branchy code without a statement-level `if`, which `BStmt` does not have), then the left and the right tail
copies. Ties take the left run (`¬ y < x`), so the result is `List.mergeSort` (stable). Proof: one merge invariant
`MI` (prefix `W` of `merge L R` written, `W ++ merge (L from p) (R from q) = merge L R`) with a per-loop extra fact
(`True`, `p = mid ∨ q = e`, `p = mid`); outer loops and the `runs` lemmas (`SortMergeList.lean`) reused unchanged.
Kernel-checked: `msortProgB_mergeSort` (`propext`, `Classical.choice`, `Quot.sound`) and, in
`Riscv/Examples/MsortBOpt.lean`, `msortCodeO2 = compileBFO 7 [0, 2, 3] msortProgB` (196 words, optimised path,
no local spilled) with `msortCodeO2_implements1`: the statement of `msortCode_implements1O` for `msortCodeO2`
(`space n = n + 71`; the 77 axioms of the other `Implements1` theorems; `axioms_k.lean`).

Merge step: 15 instructions (2 address adds, 2 `lbu`, 3 compare-and-branch + 3 single instructions for the
conditional updates, address add + `sb`, `k++`, the two loop-test branches; the loop is rotated), tails 7 per
byte; was 23.4 per step for `msortProg`. Words: `Testing/asm/opt-words/msortb.words`,
`Testing/asm/impl1-opt-words/msortb.words` (`lake env lean Testing/asm/emit_opt_msortb.lean`).

| merge sort, per element (RV64 QEMU `-icount`, `bench.py msortb msort --quick`) | n = 100 | 1000 | 100000 |
|---|---|---|---|
| `msortCodeO` (branch-free merge) | 187.5 | 279.9 | 421.5 |
| `msortCodeO2` (branchy merge) | 107.8 | 155.2 | 241.9 |
| gcc -O2 | 101.8 | 132.2 | 221.2 |
| ratio `msortCodeO2` / gcc | 1.06 | 1.17 | 1.09 |

Tested: `WDIR=opt-words MSORT=msortb msort_test.py check 60` 60/60 (QEMU == Sail == sorted, guards, gp/sp);
`WDIR=impl1-opt-words impl1_test.py msortb 100` 100/100 (QEMU == Sail == model).

Per-statement selection temporaries: NOT implemented. Measured with an unproved copy of `irB` that bases each
statement's temporaries at `tk (16 · index)` (colouring and the `allocOK`/`chk` check of `Wide.body` unchanged,
so the words were still validated by the checker): `msortProgB` 196 → 192 words, 107.6 / 155.1 / 241.9 per
element (no change: nothing is spilled already); `msortProg` 195 → 172 words (local 6 = `ww` still spilled),
174.5 / 262.9 / 398.5 (−7 %). Insertion sort and gcd go through the `AStmt`/`Stmt` selections, whose variables are
pinned to their convention registers, so `irB` temporaries do not affect them. To do it for real: give `irB` a
statement offset (proof: `irB_ok` with `0` generalised to the offset, the frame facts are already "temporaries
`≥ k`"), and make `gB`'s temporaries `(x - 32) % 16` so the injective fallback still type-checks through `chk`.

## Loop inversion, insertion sort and gcd source programs (2026-11-15)

**Loop inversion** (`Compiler/Opt/Lower.lean`, kernel-checked): a `loop pre t body` is now lowered as gcc lays out a
`while` loop, `pre; br ¬t exit; body: …; pre; br t body; exit:` (an entry test, then the bottom-tested body), instead of
`jmp test; body: …; test: pre; br t body`. Each loop entry saves the jump (one instruction); `pre` and the test are
emitted twice. `loop_guard` (new) runs the entry test, `loop_test` the bottom test; `low_ok`, `body_ok`, `fn_ok` and
everything above them keep their statements (`loop2`, the short-circuit loop, keeps its entry jump). All optimised words
change (re-emitted: `opt-words`, `impl1-opt-words`, `pipe-words`, `pipe-words1`, `frontx-words`); statement hashes
unchanged, closures differ (fingerprints re-frozen).

**Insertion sort** `insProgB` (`Riscv/Examples/InsB.lean`, a `Mach.BStmt` through `compBFO 0 [0, 3] [2]`, so the
locals are coloured freely): copy `out := in` (`mapK`), then for `i = 1 ..< n`: `v := out[i]; t := out[0];
out[0] := min v t; v := max v t` (now `out[0] ≤ key` is a sentinel), `j := i; t := out[j - 1];
while v < t { out[j] := t; j := j - 1; t := out[j - 1] }; out[j] := v` — gcc's inner loop without the `j > 0` test
(swapping the key with a smaller `out[0]` keeps the prefix a sorted permutation). Inner step: 7 instructions
(`add; sb; addi; addi; add; lbu; bltu`), the same count as gcc -O2's. Kernel-checked: `insProgB_exec` (result
`xs.mergeSort leB` via sorted + perm + `sorted_perm_eq`; `propext`, `Classical.choice`, `Quot.sound`) and
`insCodeO_implements1 : Implements1Raw insCodeO (fun x => x.mergeSort leU) (fun _ => 15)` (60 words; the 77 axioms of
the other `Implements1` theorems; `axioms_n.lean`). The old `sortProg` (`AStmt`) words are now
`opt-words/insertion-a.words` (`arr_test.py sort` with `WDIR=opt-words`).

**gcd** `gcdProg2` (`Riscv/Examples/GcdOpt.lean`, a `Stmt` through `compileFO`: two variables, so pinning costs nothing
and there is no frame prologue): `a2 := a1 ? a0 : 0; a1 := a1 ? a1 : a0` (b = 0 → swap, so `a1 ≠ 0` inside the
loop), `while a2 ≠ 0 { while a2 < a1 { a1 := a1 - a2 }; a2 := a2 - a1 }; a0 := a1` — gcc's structure (only the
changed operand is tested). 13 words; the loop is `bgeu; [sub; bltu]; sub; bnez`, gcc's code exactly. Kernel-checked:
`gcdProg2_exec` (= the reference `gcdSub`), `gcdSub_toNat : (gcdSub a b).toNat = Nat.gcd a.toNat b.toNat`
(`propext`, `Quot.sound`), `gcdO_ok` (the statement of `gcd_ok` for `gcdCodeO`) and `gcdO_ok_nat` (the same with
`Nat.gcd`) (`axioms_o.lean`; the axioms of `gcd_ok`). The old `compileOptS gcdProg` words: `opt-words/gcd-a.words`.

Measured (`python3 bench/bench.py sum take inc gcd loopsum insertion msort msortb crc --quick`, RV64 QEMU `-icount`):

| function | before (this file, above) | now | gcc -O2 | now / gcc |
|---|---|---|---|---|
| gcd (832040, 514229), whole call | 178 | 80 | 77 | 1.04 |
| gcd (100000, 3), whole call | 200020 | 100013 | 100010 | 1.00 |
| gcd (1000, 999), whole call | 6004 | 2009 | 2006 | 1.00 |
| insertion sort, n = 100 / 1000 / 10000, per element | — / 3911 / 40120 | 189.3 / 1722.2 / 17563.9 | 182.3 / 1715.2 / 17556.9 | 1.04 / 1.004 / 1.0004 |
| merge sort, branchy (`msortCodeO2`), n = 100 / 1000 / 100000, per element | 107.8 / 155.2 / 241.9 | 105.7 / 153.1 / 239.9 | 101.8 / 132.2 / 221.2 | 1.04 / 1.16 / 1.08 |
| merge sort, branch-free (`msortCodeO`), n = 100 / 1000 / 100000 | 187.5 / 279.9 / 421.5 | 186.4 / 278.9 / 420.5 | | 1.83 / 2.11 / 1.90 |
| loop sum, n = 100000, whole call | 300003 | 300003 | 300004 | 1.00 |
| sum / take / inc, n = 100000, per element | 5.0 / 6.0 / 7.0 | 5.0 / 6.0 / 7.0 | 4.0 / 5.0 / 6.0 | 1.25 / 1.20 / 1.17 |
| CRC-32, n = 100, whole call | 19577 | 19575 | 16898 | 1.16 |

Tested (QEMU == Sail == model): `impl1_test.py` on `impl1-opt-words` take5/inc/sum/crc/sort/msort/msortb/insb
100/100 each; `loop_test.py` `opt-words/{gcd,loopsum}.words` 300/300; `WDIR=opt-words arr_test.py` sum/take/inc/sort
100/100; `msort_test.py check 60` on `opt-words` (msort, msortb) 60/60; `frontx_test.py check 40` on the 8 changed
`frontx-words`; `pipe_test.py` on
the 36 `pipe-words` (50 each) and the 36 `pipe-words1` (`I1=1`, 30 each).

Callee-saved registers: not done. The condition for trying (both above ≤ 1.3×) holds, but nothing measured would
gain: `insProgB`, `gcdProg2` and `msortProgB` have no local in a slot (no `ldS`/`stS` in any hot loop), so `s1..s11`
would change no instruction count. The remaining gaps are address arithmetic, not registers: sum/take/inc pay one
`add base, i` per access where gcc walks a pointer (5 vs 4 per byte for sum), and the branchy merge step (15) has three
address adds. The next lever is strength reduction of `base + i` into a pointer variable (a source-level or `Sel`
rewrite), not `Compiler/Iface.lean`.
