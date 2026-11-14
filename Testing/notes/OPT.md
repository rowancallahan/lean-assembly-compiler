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
