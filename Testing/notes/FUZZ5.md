# FUZZ5: differential tests of the inductive-type front end (`frontx_ind`)

**Result: 0 mismatches, no spec gap found.** QEMU: 3300 + 3300 random cases (seeds 1, 2) + 152 large cases; Sail: 275 cases.
Built from `origin/fuzz4` + `origin/main` (merged; `feat-inductive` is only in main). No compiler source was changed; the words are the committed `frontx-words/*.words`.

Entries (all 11 with `ind A B L`): `bt_count bt_mirror bt_graftleft` (BinTree Nat), `pos_tonat pos_plus`, `nontail_sum_ln tail_sum_ln tail_reverse_ln list_append_ln` (List Nat), `level_hasparam level_isneverzero`. Two-input: `bt_graftleft pos_plus list_append_ln`.

## Method (`Testing/asm/fuzz5/`)
- `ref.lean` (`lean --run`, Lean 4.29): the verbatim source functions plus my own byte decoder/encoder (asserts all input bytes are consumed); gives the expected bytes. `fuzz5.py` has an independent Python reference and an independent encoder; Lean and Python must agree before anything runs on the machine.
- Inputs: empty (leaf/nil/`one`/`zero`), sizes 1–3, small/medium/up to ~1000 nodes; shapes: random (skewed splits), left chain, right chain, zig-zag, comb, breadth-first wide; Pos chains; lists; Levels (chains, right-nested, random). Scalars: 0, 1, 2, 127, 128, 255, 256, 2^31, 2^32±1, 2^63±1, 2^64−2, 2^64−1, random 64-bit, so sums wrap mod 2^64 many times. Two-input cases split sizes (a, n−a) with empty on either side.
- Large (QEMU only, `BIG`): trees of 20000 nodes (left, right, zig-zag, wide, random) and a 40000-node left chain (400 KB input); Pos chains to 60000; lists of 20000/40000/60000 elements (540 KB); Levels to 20000 nodes. Lean ran them with `ulimit -s unlimited`.
- Per case: layout `[G in G][out G][G work G]`, G = 16 guard bytes; output buffer exactly Lean's result length, pre-filled random; work block random-filled and **exactly `A + B·n` bytes** (n = total input length), `sp` = block end.
- Checks: output bytes = Lean = Python; `a1` = result length for tree/list/Pos results (`L = 1`); `gp`, `sp` restored; guards on both sides of the input, output and work block; QEMU: the whole memory image outside output + work block + result slots equals the initial image; Sail: every write lands in the output or work block. Space: QEMU is run twice with different work-block fills; bytes equal in both runs were written; the longest never-written run (heap grows up, stack down) was > 0 in every case, so heap and stack never met (smallest gap 355 bytes). Largest fraction of the block written: 24% (`pos_tonat`), 8–14% for the others, so `A + B n` holds with a wide margin on these inputs.
- Harness sanity: a corrupted expected byte is rejected (`CORRUPT=1`).

## Runs
| run | cases per entry | entries | mismatches |
|---|---|---|---|
| QEMU seed 1 | 300 | 11 | 0 |
| QEMU seed 2 | 300 | 11 | 0 |
| QEMU large (`BIG`, seed 3) | 16 (trees), 13 (others) | 11 | 0 |
| Sail seed 4 | 25 | 11 | 0 |

Failures: none, so no reproducers. Reproduce: `bash Testing/asm/fuzz5/runall.sh seed2|big|sail` (needs Lean 4.29 in `/tmp/leandl/x/*/bin`, qemu-system-riscv64, riscv64-linux-gnu-gcc, Sail 0.9 at the path in `fuzz5.py`); one entry: `python3 Testing/asm/fuzz5/fuzz5.py FN SEED N qemu|sail [big]`.

## Limits
- Well-formed inputs only (the spec says nothing about malformed bytes; not tested). Scalars are bytes, so always < 2^64; sums/counts above that are checked mod 2^64 (Lean's `Nat` result reduced).
- `A + B n` is loose (≤ 24% used), so the bound was never close to failing; a tighter bound would be needed to stress it. Heap/stack separation is inferred from fill comparison, not from a memory trace (Sail was only run on small inputs).
- Sail sample is 25 cases per entry, inputs up to ~10 KB. Two QEMU seeds; `Level.param`'s `Name` is dropped by the format, so it is not exercised.
- Level inputs: shape generator caps random trees at 400 levels deep; chains go to 20000.
