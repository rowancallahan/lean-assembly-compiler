# Byte arrays: loops + memory

Status (all kernel-checked, no `sorry`, axioms = those of `compile_ok`: `propext`, `Classical.choice`,
`Quot.sound`, the 7 model constants and the 67 `riscv_*` softfloat externs):
`compileA_ok`, `compileAF_ok` (`Proven/Arr.lean`), `sumCode_ok`, `takeCode_ok`, `incCode_ok`, `mapCode_ok`
(`Proven/ArrExamples.lean`), `sortProg_mergeSort` (`Proven/SortIns.lean`, pure Lean, axioms `propext`,
`Classical.choice`, `Quot.sound` only), `sortCode_ok`, `sortCode_implements` (`Proven/SortMachine.lean`).
Bottom-up merge sort: done in the extended language with spill slots, see
"Spill slots and merge sort" at the end (the analysis just before it is the earlier, superseded, status).

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

## Merge sort: why it did not fit the 8-variable language (superseded, see below)

Bottom-up merge sort over `input`, `scratch`, `output` needs three base variables plus the length, which leaves
4 of the 8 variables (`a4..a7`). A branch-free merge step needs at least the width `w`, the output index `k`,
the left pointer `p` (the right one is `k + mid - p`) and the two loaded bytes `x`, `y` (loads are statements),
i.e. 5 variables, and its selection condition `p < mid ∧ (q ≥ end ∨ x ≤ y)` with `mid = min (i + w) n`,
`i = k &&& -(2w)` exceeds expression depth 6. Needed first: more variables (e.g. spill slots in the stack
block with `ld/sd` lemmas on base `sp`, or a larger register set with fewer temporaries) or expression
spilling, then the source-level merge proof (per pass: runs of width `2w` sorted, permutation).

## Spill slots and merge sort (`Arr2*.lean`, `SortMerge*.lean`)

Status: all kernel-checked, no `sorry`; `#print axioms` of `compileBF_ok` and `msortCode_implements` is exactly
that of `compile_ok` (77 entries: `propext`, `Classical.choice`, `Quot.sound`, the 7 model constants, the 67
`riscv_*` externs); `msortProg_mergeSort` uses only `propext`, `Classical.choice`, `Quot.sound`;
`AExec.toB` only `propext`, `Quot.sound`. The old files (`ArrCode` .. `SortMachine`) are unchanged.

| file | what | check time |
|---|---|---|
| `Arr2Code.lean` | `BExp`, `BStmt`, `BExec`, `genB`, `compileB`, `prologue`, `compileBF`, `BStmt.wf`; embedding `AStmt.toB`, `AExec.toB` | ~1 s |
| `Arr2Step.lean` | `mem_word2`: `mem_word` for loads/stores with an immediate offset | ~1 s |
| `gen_arr2.py` → `Arr2Words.lean` | 134 step lemmas: `ld t_k, 8(j+1)(gp)` (k < 7, j < 16), `sd t0, 8(j+1)(gp)`, `sd gp, 0(t0)`, `ld gp, 0(gp)`, `ld t0, 0(t0)`, `sd t1, 0(t0)`, `add t0, x0, sp`, `add gp, x0, t0`; families `step_ldS`, `step_sdS`, `step_ldGp` | 776 s |
| `Arr2Exp.lean` | `FrOK`, `EnvRel`, `slot_addr`, `genB_ok` | ~2 s |
| `Arr2.lean` | `slotRegs`, `HeapRel`, `Rel2`, `setV_ok`, `execB_ok` | ~3 s |
| `Arr2F.lean` | `zero_slots`, `prologue_ok`, `compileBF_ok` | ~5 s |
| `Arr2Src.lean` | `BExec.loop_inv`, `env_keep`, `load'`/`store'`/`asg`, `ofNat` value lemmas (no machine) | ~1 s |
| `SortMergeList.lean` | `MS.runs` (one pass), `MS.CS` (aligned chunks sorted), `runs_perm`, `runs_CS`, `CS_sorted` (generic in `le`, no machine) | 0.7 s |
| `SortMergeSrc.lean` | `msortProg`, `inner_step`, `merge_inner_exec`, `run_exec`, `pass_exec`, `msortProg_mergeSort` | ~10 s |
| `SortMergeMachine.lean` | `msortProg_wf`, `msortCode`, `msortCode_ok`, `ImplementsMapped2`, `msortCode_implements` | ~5 s |

Times: `lake env lean` per file including imports, on a loaded machine.

### Language (superset of `AStmt`)

- `BExp`: as `AExp` with `var (i : Nat)`; `BEnv = Nat → BitVec 64`. Variables `0..7` live in `a0..a7`,
  variables `8..8+N-1` in stack slots (`N ≤ NS = 16`, fixed per program by `compileBF N`).
- `BStmt`: `assign v e | load v b i | store b i e | seq | loop` with `v : Nat`; `BExec` exactly as `AExec`.
- Embedding: `AStmt.toB`, `AExec.toB : AExec p σ σ' → BExec p.toB (σ.toB ρ) (σ'.toB ρ)` (variables `≥ 8` taken
  from any `ρ` and untouched). Old programs and their theorems stay as they are.

### Compiler

- Slot `j` is the 8 bytes at `gp + 8(j+1)`. A slot variable in an expression is one `ld t_k, 8(j+1)(gp)`
  (expression depth unchanged: a slot read costs no extra temporary); `v := t0` for a slot is `sd t0, 8(j+1)(gp)`
  (`setV`). Everything else is `compileA` (`genB` = `gen8` + the slot case).
- `prologue N`: `t0 := sp; t0 := (t0 >> 3) << 3; t0 := t0 - 8(N+1); sd gp, 0(t0); gp := t0; t0 := 0;
  sd t0, 8(j+1)(gp)` for `j < N`. So the frame is `[fp, fp + 8(N+1))` with `fp = frameBase N sp =
  alignDown(sp, 8) - 8(N+1)` (cell 0: saved `gp`), and the slots start at `0`.
- `compileBF N bv p = prologue N ++ compileB bv p ++ [ld gp, 0(gp); ret]`: `gp` is restored.
- `gp` (`x3`) is used as frame pointer because every caller-saved register is a variable or a temporary;
  it is saved and restored, so the function keeps it (stated in the theorems).

### Limits (`BStmt.wf N bv`)

- Variables `< 8 + N`, `N ≤ 16` (the generated `ld/sd` lemmas cover 16 slots; more slots = rerun
  `gen_arr2.py` with a larger count, ~6 s per extra slot ✕ 8 lemmas).
- Expression depth: unchanged (`assign`: `< 7`; `load`/`store` index and value `< 6`). Not lifted: a deep
  expression must be split by the programmer into assignments to (slot) variables.
- Loops: body within the `beq` range (`(genB c 0).length + (compileB bv body).length + 2 < 1024`); no
  far-branch form was needed (the merge sort's largest loop body is 270 words).
- Base variables are never assigned; blocks are byte lists; no 8-byte block accesses (S2 not done, see below).

### Main theorems

```lean
structure FrOK (N fp : Nat) : Prop where
  al : fp % 8 = 0
  lo : 0x80000000 ≤ fp
  hi : fp + 8 * (N + 1) ≤ 0x100000000
  ns : N ≤ NS

structure HeapRel (bv : List Nat) (R : List Region) (σ : BState) (s : St) : Prop where
  hlen : σ.heap.length = R.length
  bvlen : bv.length = R.length
  base : ∀ b (hb : b < R.length), σ.env (bv.getD b 0) = BitVec.ofNat 64 R[b].base
  blen : ∀ b (hb : b < R.length), (σ.heap[b]?.getD []).length = R[b].len
  bytes : ∀ b (hb : b < R.length), bytesAt s R[b].base R[b].len = (σ.heap[b]?.getD []).map some

theorem compileBF_ok (N : Nat) (bv : List Nat) (hbv : ∀ x ∈ bv, x < 8 + N) {p : BStmt} (hp : p.wf N bv)
    {R : List Region} (hR : RegOK R) {σ σ' : BState} (hex : BExec p σ σ') {s : St} (h : Cfg s) {pc : BitVec 64}
    (hpc : s.regs.get? .PC = some pc) (hc : codeAt s pc (compileBF N bv p)) (hok : codeOK pc (compileBF N bv p).length)
    (hf : FrOK N (frameBase N (getX s 2))) (hfd : ∀ r ∈ R, disjoint ⟨frameBase N (getX s 2), 8 * (N + 1)⟩ r)
    (hcd : ∀ r ∈ (⟨frameBase N (getX s 2), 8 * (N + 1)⟩ : Region) :: R,
      disjoint ⟨pc.toNat, 4 * (compileBF N bv p).length⟩ r)
    (hreg : ∀ i : Fin 8, getX s (A8 i) = σ.env i.val) (hslot : ∀ j < N, σ.env (8 + j) = 0)
    (hheap : HeapRel bv R σ s) (hra : (getX s 1).toNat % 2 = 0) :
    runsTo s fun s' => s'.regs.get? .PC = some (getX s 1) ∧ (∀ i : Fin 8, getX s' (A8 i) = σ'.env i.val) ∧
      HeapRel bv R σ' s' ∧ unchangedOutside s s' ((⟨frameBase N (getX s 2), 8 * (N + 1)⟩ : Region) :: R) ∧
      Cfg s' ∧ calleeSavedKept s s' ∧ getX s' 3 = getX s 3
```

The body induction `execB_ok` carries `Rel2 N fp bv R σ s` (`EnvRel`: `a_i = σ.env i`, `gp = fp`, slot `j`
bytes `= le8 (σ.env (8+j))`; plus `HeapRel`) and `AF (R ++ slotRegs N fp)`: each slot is an 8-byte region of
the layout, so a slot store is `Next.store_region8` and a byte store `Next.store_region` on the same list.

### Merge sort

Program `msortProg` (`SortMergeSrc.lean`): blocks input (0, base `v0`), scratch (1, base `v2`), output (2,
base `v3`), `v1 = n`; registers `v4..v7 = k, p, q, t`, slots `v8..v14 = x, y, mid, e, i, w, ww` (`N = 7`).
`pass(src, dst)` merges runs `[i, i+w)`, `[i+w, i+2w)` for `i = 0, 2w, ...` with a branch-free inner loop
(`t := (p < mid) & ((q < e & y < x) ^ 1)`, `dst[k] := t ? x : y`, `p += t`, `q += t ^ 1`; loads use index
`p < mid ? p : k` so they are always in bounds). Main: `w := 1; pass(in, out); ww := 2; while ww < n
{ w := ww; pass(out, scr); w := 2ww; pass(scr, out); ww := 4ww }` (an odd number of passes, so the result is
in the output block; no final copy). O(n log n): `1 + 2m` passes of O(n) each, `m` = number of `ww ∈ {2, 8, 32, …}`
below `n`, i.e. `⌈log₂ n⌉` or `⌈log₂ n⌉ + 1` passes (11 for n = 1000).

Source proof: one pass computes `MS.runs leB w S 0` (`pass_exec`, via `run_exec`, `merge_inner_exec`,
`inner_step`: invariant `W ++ merge (L.drop (p-i)) (R.drop (q-mid)) = merge L R` with core's `List.merge`);
`runs_perm` (permutation), `runs_CS` (if every aligned `w`-chunk is sorted, every aligned `2w`-chunk of the
result is: core's `List.pairwise_merge`); at the end `ww ≥ n`, so the output is sorted (`CS_sorted`), and by
uniqueness of sorted permutations (`sorted_perm_eq`) it is `xs.mergeSort leB`:

```lean
theorem msortProg_mergeSort (xs scr out : List (BitVec 8)) (σ : BState) (hh : σ.heap = [xs, scr, out])
    (h1 : σ.env 1 = BitVec.ofNat 64 xs.length) (hn : xs.length < 2 ^ 32) (hscr : scr.length = xs.length)
    (hout : out.length = xs.length) :
    ∃ σ', BExec msortProg σ σ' ∧ ∃ scr', σ'.heap = [xs, scr', xs.mergeSort leB]
```

Machine (`SortMergeMachine.lean`): `msortCode = compileBF 7 [0, 2, 3] msortProg` (442 words).
`msortCode_ok` (region form: output `= xs.mergeSort leB`, input unchanged, memory outside frame/scratch/output
unchanged, callee-saved and `gp` kept) and

```lean
theorem msortCode_implements : ImplementsMapped2 msortCode (fun x => x.mergeSort leU) (stackLen := 71)
```

`ImplementsMapped2` is `Implements` (`Spec.lean`) with exactly two extra hypotheses, the hosting assumptions
`∀ i < (f x).length, (s.mem[output.base + i]?).isSome` and `∀ i < x.length, (s.mem[scratch.base + i]?).isSome`
(the Sail `lbu` lemma needs a present byte, and `HeapRel` asks every block byte to be present at the start,
also for the scratch and output blocks, which the program writes before reading). The stack needs no hosting
hypothesis (the prologue writes every frame cell before any read). `stackLen = 71`: 64 bytes of frame (saved
`gp` + 7 slots) plus up to 7 bytes lost to aligning `sp` down to 8 (`Implements` does not promise an aligned
`sp`). Everything else is literally `Implements`: code anywhere, `a0..a3`/`sp`/`ra` as specified, conclusion
`PC = ra`, output bytes, `unchangedOutside [input, scratch, output, stack]`, `calleeSavedKept`, `Cfg`.

### Tests (`asm/msort_test.py`, words from `asm/emit_arr2.lean` in `asm/arr-words/msort.words`)

`check N`: per case its own input / scratch / output slots (each followed by 16 guard bytes) and its own
256-byte stack with `sp` at a random misalignment (0..7), `gp` set to a magic value; QEMU and the Sail C
emulator: output `= sorted(input)`, input and every guard byte unchanged, every stack byte outside the 64-byte
frame unchanged, `gp` and `sp` restored, and every Sail data write inside the case's scratch / output / frame.
`bench`: instructions retired between the call and the return (`minstret` under QEMU `-icount shift=0`).

### Not done

- S2 (8-byte `load64`/`store64` on blocks): not started. It needs two `BStmt` constructors, an alignment
  side condition per word-accessed block, a lemma for an 8-byte store inside a larger region (only whole-region
  `store_region8` exists) and `ld/sd t, 0(t0)` lemmas (already generated: `W2.ldT`, `W2.sdT`, `step_ldT`).
- Expression spilling (depth limit unchanged).
