# Loops + memory: what a byte-array loop needs

Status: notes only. The memory agent's files (`Proven/Mem*.lean`) were not on `main` when this was written; the
names below are from its in-progress working copy (`step_lbu`, `step_sb`, `step_ld`, `step_sd`: offset-0
loads/stores, data registers `memD` = the expression temporaries `T`, base registers `memB` = `s1, a0..a3`;
`Layout`/`Block`, `readCells`, `writeCells`, `layout_write`, `Next.store_region`).

## Sum of bytes (`a0` = pointer, `a1` = length, result in `a2`)

Source, extending `Stmt` (`Proven/Loop.lean`) by one statement and one expression form:

- `Exp.load8 (p : Exp)`: value `zeroExtend (mem[p])`. Semantics now needs the memory:
  `Exp.denote : Env → Mem → Exp → BitVec 64`, so `Exec : Stmt → Env × Mem → Env × Mem → Prop`.
- `Stmt.store8 (p v : Exp)` (for sorting).

Missing pieces:

1. `gen` for `load8 p` into `t_k`: `gen p k ++ [lbu t_k, 0(t_k)]`. `step_lbu` takes its base from `memB`, which
   does not contain the temporaries. Needed: `lbu/sb` step lemmas with base `rs1 ∈ T` (generated like
   `Proven/Words.lean`), or a `mv` of the address into `s1`. Same for `sb` (`rs1, rs2 ∈ T`).
2. `gen_ok` for the extended `Exp`, with the memory side condition: every address the expression loads from is in
   RAM. Since `gen` evaluates every subexpression (also both arms of `ite`), this is a *static* safety predicate
   `Exp.safe σ m` (all `load8` addresses of all subterms in a readable block), not just the value.
3. `Frame` (Proven/Loop.lean) must drop `s'.mem = s.mem` and keep a layout invariant instead:
   `Layout.ok L`, code block disjoint from all data blocks (so `codeAt` survives stores — today `codeAt_mem` uses
   memory equality), and `unchangedOutside` the written blocks.
4. `compileS_ok` with stores: the invariant per loop iteration is
   `readCells s.mem codeBlock = codeBytes code` and `∀ i < len, mem[base + i] = xs[i]`; `layout_write` /
   `Next.store_region` give the frame for one `sb`.
5. Loop invariant for the sum: `a0 = base + i`, `a1 = len - i`, `a2 = (xs.take i).sum`, measure `len - i`
   (`Exec.loop_of` / `Exec.loop_inv` in `Proven/Loop*.lean` already take a measure). The 64-bit pointer increment
   needs `base + len < 2^64` (true for RAM addresses), so `(a0 + 1).toNat = a0.toNat + 1`.

## Insertion / merge sort

- Two nested loops (insertion sort) are already expressible: `Stmt.loop` nests, and `compileS_ok` is proved by
  induction on `Exec`, so nesting needs nothing new on the control-flow side. The `beq` range (±4 KiB) bounds each
  loop body to ~1000 words (`Stmt.wf`); a `bne`-over-`jal` pair would lift that, using the already generated
  `bne` lemmas.
- Data side: the invariant "prefix sorted ∧ multiset preserved" is pure Lean on `List (BitVec 8)`; the machine
  side only needs items 1–4 above (byte loads/stores at `base + i`, frame through a write).
- Merge sort (as in `asm/sort.S`) additionally needs a second buffer (`scratch` in `Implements`), i.e. two blocks
  in the layout, and either recursion (stack: `sd/ld` on `sp`, `jal ra` / `ret` step lemmas with a saved `ra`) or a
  bottom-up iterative version, which fits `Stmt` with three nested loops and no stack.
- `Implements` (Proven/Spec.lean) then follows from a `compileF`-style theorem plus `bytesAt`/`readCells`
  conversions (`bytesAt_eq` in the memory files).
