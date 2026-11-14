# Byte arrays: loops + memory

Status (all kernel-checked, no `sorry`, axioms = those of `compile_ok`: `propext`, `Classical.choice`,
`Quot.sound`, the 7 model constants and the 67 `riscv_*` softfloat externs):
`compileA_ok`, `compileAF_ok` (`Proven/Arr.lean`), `sumCode_ok`, `takeCode_ok`, `incCode_ok`, `mapCode_ok`
(`Proven/ArrExamples.lean`), `sortProg_mergeSort` (`Proven/SortIns.lean`, pure Lean, axioms `propext`,
`Classical.choice`, `Quot.sound` only), `sortCode_ok`, `sortCode_implements` (`Proven/SortMachine.lean`).
Not done: bottom-up merge sort (see the end).

## Files

| file | what | check time |
|---|---|---|
| `ArrCode.lean` | `AExp`, `gen8`, `AState`, `AStmt`, `AExec` (no Sail) | 0.5 s |
| `gen_arr.py` → `ArrWords.lean` | step lemmas for the 34 new words | 56 s |
| `ArrExp.lean` | `Ran7`, `gen8_ok` (= `gen_ok` for 8 variables, temporaries `t0..t6`) | 1.3 s |
| `Arr.lean` | `compileA`, `AStmt.wf`, `Rel`, `AF`, `execA_ok`, `compileA_ok`, `compileAF_ok`, `AExec.loop_inv` | 2.4 s |
| `ArrExamples.lean` | `sumProg`, `mapProg g`; `*_exec` (source) and `*Code_ok` (machine) | 1.4 s |
| `SortIns.lean` | `sortProg` (insertion sort), `AExec.env_keep`, `sortProg_mergeSort` (source) | 1.9 s |
| `SortMachine.lean` | `sortCode_ok`, `ImplementsMapped`, `sortCode_implements` | 1.3 s |

Times are `lake env lean` per file, including imports.

## The language (`Proven/ArrCode.lean`)

- `AExp`: `var (i : Fin 8) | const c | bin op a b | ite c a b`, the operators of `Exp` (`Proven/Code.lean`);
  `ite` evaluates both arms (branch-free select), so expressions never touch memory.
- `AState = { env : Fin 8 → BitVec 64, heap : List (List (BitVec 8)) }`: variables and block contents.
- `AStmt`:
  - `assign v e`;
  - `load v b i`: `v := (heap[b][i]).setWidth 64` (zero-extended byte);
  - `store b i e`: `heap[b][i] := (e).setWidth 8` (low byte);
  - `seq p q`; `loop c body` (`while c ≠ 0`).
- `AExec p σ σ'` (big step). `load`/`store` carry `b < heap.length` and `i.toNat < heap[b].length`: an
  out-of-bounds access has no derivation, so a terminating run is memory safe. Loops via `AExec.loop_inv`
  (invariant + `Nat` measure). `AExec.env_keep`: variables a program never assigns are unchanged.

## Compiler and register conventions (`Proven/Arr.lean`)

- Variable `v_i` is `a_i` (`x10 + i`), `i < 8`. Expression temporaries: `t0..t6` (`T 0..6`).
- `bv : List (Fin 8)`: block `b`'s base address is held in variable `bv[b]`. `AStmt.wf bv` forbids assigning a
  base variable (so the bases stay put).
- `assign v e` ↦ `gen8 e 0 ++ [add a_v, x0, t0]`.
- `load v b i` ↦ `gen8 (v_(bv[b]) + i) 0 ++ [lbu t0, 0(t0), add a_v, x0, t0]`.
- `store b i e` ↦ `gen8 (v_(bv[b]) + i) 0 ++ gen8 e 1 ++ [sb t1, 0(t0)]`.
- `loop c body` ↦ `gen8 c 0 ++ [beq t0, x0, +exit] ++ body ++ [jal x0, -back]` (as `compileS`).
- `compileAF bv p = compileA bv p ++ [ret]`.
- New per-word lemmas (`ArrWords.lean`): `add t_k, x0, a4..a7` (28), `add a4..a7, x0, t0` (4),
  `lbu t0, 0(t0)`, `sb t1, 0(t0)`; the rest is reused (`Words.lean`: operators, constants, `a0..a3` reads;
  `Loop.lean`: `add a0..a3, x0, t0`; `BranchWords.lean`: `beq t0, x0`, `jal x0`).

### Limits (`AStmt.wf bv`)

- `assign`: `e.depth < 7`; `load`: `i.depth < 6`; `store`: `i.depth < 6`, `e.depth < 6` (no spilling).
- `loop c body`: `c.depth < 7` and `(gen8 c 0).length + (compileA bv body).length + 2 < 1024` (the `beq`
  reaches ±4 KiB); a `bne`-over-`jal` pair would lift this.
- 8 variables in total, base variables and lengths included. No 8-byte accesses, no stack, no calls, no
  conditional statement (use `ite` + an unconditional store, as the sort does).
- Data blocks are contiguous regions in RAM (`[0x80000000, 2^32)`), so indices and lengths are `< 2^32`.

## Theorem statements

```lean
def RegOK (R : List Region) : Prop := (∀ r ∈ R, r.inRAM) ∧ R.Pairwise disjoint

structure Rel (bv : List (Fin 8)) (R : List Region) (σ : AState) (s : St) : Prop where
  env : ∀ i, getX s (A8 i) = σ.env i
  hlen : σ.heap.length = R.length
  bvlen : bv.length = R.length
  base : ∀ b (hb : b < R.length), σ.env (bv.getD b 0) = BitVec.ofNat 64 R[b].base
  blen : ∀ b (hb : b < R.length), (σ.heap[b]?.getD []).length = R[b].len
  bytes : ∀ b (hb : b < R.length), bytesAt s R[b].base R[b].len = (σ.heap[b]?.getD []).map some

theorem compileAF_ok (bv : List (Fin 8)) {p : AStmt} (hp : p.wf bv) {R : List Region} (hR : RegOK R)
    {σ σ' : AState} (hex : AExec p σ σ') {s : St} (h : Cfg s) {pc : BitVec 64} (hpc : s.regs.get? .PC = some pc)
    (hc : codeAt s pc (compileAF bv p)) (hok : codeOK pc (compileAF bv p).length)
    (hcd : ∀ r ∈ R, disjoint ⟨pc.toNat, 4 * (compileAF bv p).length⟩ r) (hrel : Rel bv R σ s)
    (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧
      Rel bv R σ' s' ∧ unchangedOutside s s' R ∧ Cfg s' ∧ calleeSavedKept s s'
```

`compileA_ok` is the same without `ret`, ending at `pc + 4 * (compileA bv p).length`. The induction
(`execA_ok`) carries `AF R s s'` (Cfg kept, memory outside `R` unchanged, registers other than `t0..t6`,
`a0..a7` kept) and re-establishes `codeAt` after stores from code/data disjointness (`codeAt_out`). The memory
model is the interval instance of `Proven/MemModel.lean` (`Next.store_region`, `bytesAt`).

Examples (`xs : List (BitVec 8)`; input region `⟨inb, |xs|⟩` with base in `a0`, length in `a1`):

- `sumCode_ok`: `a2 = sumBytes xs` (`xs.foldl (fun acc x => acc + x.setWidth 64) 0`), every memory byte unchanged.
- `mapCode_ok g f`: for an expression `g` computing `f` on the byte in `a6`, with `n` in `a2` and an output
  region `⟨outb, |out|⟩` at `a3` of at least `min n |xs|` bytes: output `= (xs.take n).map f ++ out.drop (min n |xs|)`,
  input unchanged, `unchangedOutside s s' [output]`.
- `takeCode_ok` (`f = id`) and `incCode_ok` (`f = (· + 1)`): output region of exactly `min n |xs|` bytes holds
  `xs.take n` resp. `(xs.take n).map (· + 1)`.
- `sortCode_ok`: output region `⟨outb, |xs|⟩` (any initial contents) holds `xs.mergeSort leB`
  (`leB a b = decide (a ≤ b)`), input unchanged, `unchangedOutside s s' [output]`.
- `sortCode_implements : ImplementsMapped sortCode (fun x => x.mergeSort leU)` on `List UInt8`.
  `ImplementsMapped` is `Implements` (`Proven/Spec.lean`) with one extra hypothesis, the hosting assumption
  for the output block: `∀ i < (f x).length, (s.mem[output.base + i]?).isSome`. (The Sail `lbu` lemma needs
  the byte to be present in the memory map; the relation `Rel` therefore asks every block byte to be present
  at the start, including the output block, which the program overwrites before reading.) Everything else is
  literally `Implements`: code anywhere (from `codeBytes`), `a0..a3`/`sp`/`ra` as specified, regions in RAM and
  pairwise disjoint with the code, conclusion `PC = ra`, output bytes, `unchangedOutside` the four regions,
  `calleeSavedKept`, `Cfg`. The code uses neither the scratch region nor the stack.

Source-level sort proof (`SortIns.lean`): `inner_exec` (inner loop inserts `key` into the sorted prefix, with
the "hole" invariant `pre.take j ++ y :: (pre.drop j ++ rest)`), `ins_exec` (outer invariant: prefix of length
`i` sorted, whole array a permutation), `sortProg_exec` (sorted permutation), `sortProg_mergeSort` (equality
with `List.mergeSort` via `List.Perm.eq_of_pairwise` from core).

## Tests

`asm/emit_arr.lean` writes the words to `asm/arr-words/`; `asm/arr_test.py {sum,take,inc,sort} N` runs N random
inputs (lengths 0..64, `n` up to `2^64 - 1`) per function on QEMU and on the Sail C emulator: whole 128-byte
output slot (result, then intact `0x55` guard bytes), input slot unchanged, `a2` for `sum`; every Sail data write
must be inside the expected output bytes. Run: sum/take/inc 200 each, sort 300: all pass.

## What an ARM port needs

Generic (no RISC-V): `ArrCode.lean` (language, semantics), the `*_exec` source lemmas in `ArrExamples.lean`
and all of `SortIns.lean` except that they live in files importing the RISC-V compiler (move them to a
source-only file when the ARM side starts), `MemModel.lean`, `LoopRule.lean`.
RISC-V specific: `gen8`/`compileA` (word encodings), `ArrWords.lean`, `ArrExp.lean` (`gen8_ok` over RISC-V
step lemmas), `Arr.lean` (`execA_ok` uses `Next`, `codeAt`, `step_beq_5_0`, `step_jal_0`), `SortMachine.lean`.
The ARM side needs step lemmas for: the `Exp` operator words (`CompilerArm.lean` has an untested backend),
`mov x_k, x_var` for 8 variable registers, `ldrb w_t, [x_t]`, `strb w_t1, [x_t0]`, `cbz x_t0, +off`, `b -off`
(symbolic offsets), `ret`; a `Cfg`/`Next`/`runsTo` analogue for the ARM model; then `execA_ok` can be copied
with the register map changed. ARM has 31 general registers, so the 8-variable / 7-temporary limits can be
raised there.

## Merge sort: not done, and why

Bottom-up merge sort over `input`, `scratch`, `output` needs three base variables plus the length, which leaves
4 of the 8 variables (`a4..a7`). A branch-free merge step needs at least the width `w`, the output index `k`,
the left pointer `p` (the right one is `k + mid - p`) and the two loaded bytes `x`, `y` (loads are statements),
i.e. 5 variables, and its selection condition `p < mid ∧ (q ≥ end ∨ x ≤ y)` with `mid = min (i + w) n`,
`i = k &&& -(2w)` exceeds expression depth 6. Needed first: more variables (e.g. spill slots in the stack
block with `ld/sd` lemmas on base `sp`, or a larger register set with fewer temporaries) or expression
spilling, then the source-level merge proof (per pass: runs of width `2w` sorted, permutation).
