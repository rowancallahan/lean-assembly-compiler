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
Not proved / not done: `BStmt` (spill slots, merge sort), the pipe front end on the new pipeline, a liveness-based
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
Merge sort: not measured (needs `BStmt`).

## Drop-in entry points (kernel-checked)

`compileO : Exp → List (BitVec 32)`, `compileFO : Stmt → List (BitVec 32)` (`Riscv/Back/Opt.lean`),
`compileAFO : List (Fin 8) → AStmt → List (BitVec 32)` (`Riscv/Back/OptArr.lean`): the optimised words when
`compileOpt…` succeeds, the old words otherwise. `compileO_ok`, `compileFO_ok`, `compileAFO_ok` have the statements
of `compile_ok`, `compileF_ok`, `compileAF_ok` with the function name replaced (same hypotheses `depth < 11` / `wf`,
used only in the fallback case). A front end switches by replacing the function and theorem names; if it relies on
`compileAF bv p` definitionally (e.g. on its length), those facts must be restated for `compileAFO`.
`compileBF` (spill slots) has no optimised counterpart yet: the frame/slot interface `MachineF`
(`Compiler/Frame.lean`) has no RISC-V instance on branch `stable` at the time of writing.
