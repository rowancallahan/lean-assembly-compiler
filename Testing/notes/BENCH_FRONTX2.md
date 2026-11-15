# Front-end benchmark, round 2 (speed2 + inductives) — instruction counts vs gcc -O2

Measured, not proved. Same method as `BENCH_FRONTX.md`: dynamic instructions (`minstret`, QEMU `-icount shift=0`, call overhead
subtracted) of the committed `frontx-words/*.words` against gcc -O2 RV64I (`-ffreestanding`), outputs asserted equal to a model.
Tree: HEAD `3dbaec9` (= `origin/main`: speed2 and `feat-inductive` merged). Code in `Testing/asm/bench_frontx/`:
`bench_frontx.py rv` (bytes, unchanged), `bench_ind.py` + `ind.c` (inductives), `trace_ind.py`, `classify_ind.py`; raw numbers
`results/{rv,ind}.json`. The old `bench_frontx.py rv` re-run reproduces the committed `results/rv.json` exactly. Lean/x86 columns of round 1 not redone (no Lean here).

## 1. Byte-array functions (per input byte, slope 64 KiB→1 MiB)

| function | ours (round 1) | ours now | gcc -O2 | now/gcc | (round 1 /gcc) |
|---|---|---|---|---|---|
| crcraw | 70.0 | 61.0 | 69.0 | 0.88 | 1.01 |
| b64all | 55.2 | 24.5 | 11.1 | 2.20 | 4.97 |
| findnl | 27.0 | 6.0 | 5.0 | 1.20 | 5.40 |
| tailsum | 12.0 | 4.0 | 4.0 | 1.00 | 3.00 |
| nontailsum | 13.0 | 5.0 | 4.0 | 1.25 | 3.25 |
| drop5 | 26.0 | 6.0 | 5.0 | 1.20 | 5.20 |
| filterall | 21.9 | 6.95 | 6.97 | 1.00 | 3.15 |
| inceach | 16.0 | 7.0 | 6.0 | 1.17 | 2.67 |
| twice (`xs ++ xs`) | 47.0 | 14.0 | 7.0 | 2.00 | 6.71 |
| findfirstgt3 | 19.0 | 5.0 | 4.0 | 1.25 | 4.75 |
| adlere (Adler-32) | – | 7.5 | 7.5 | 1.00 | – |
| taillength / booklength | 10.0 | 3.0 | O(1), 45 total | n/m | n/m |
| finalof | 17.0 | 4.0 | O(1), 10 total | n/m | n/m |
| take5 / headof / be32at0 (whole call) | 182 / 52 / 114 | 95 / 44 / 89 | 39 / 9 / 62 | 2.4 / 4.9 / 1.4 | 4.7 / 5.8 / 1.8 |

Loops are now 1.0–1.25× gcc (was 2.7–6.7×); left over: `b64all` 2.2× (digit classification as a chain of tests), `twice` 2.0× (two passes, gcc fuses them).

## 2. Inductive examples (`frontx_ind`) — per node, slope between two sizes (trees 511 → 4095 nodes, lists/levels 500 → 2000)

Hand-written C on linked structures (`ind.c`: malloc-free bump allocator, same results). Two gcc columns, because ours takes the
**byte encoding** (`Ind.lean`: tag byte, fields, 8-byte little-endian scalars) and decodes it into cells, runs, and encodes a tree result:
- **gcc core** = the function alone on an already built structure (what a C programmer calls the function);
- **gcc e2e** = decode the same bytes → function → encode the result, in C. This is the like-for-like cost of the `Implements1` interface.

| function (node = one cons/branch/constructor) | ours | gcc core | ours/core | gcc e2e | ours/e2e |
|---|---|---|---|---|---|
| `BinTree.count` | 684.0 | 8.7 | 79 | 107.7 | 6.4 |
| `BinTree.mirror` | 1189.0 | 16.1 | 74 | 202.2 | 5.9 |
| `NonTail.sum` (List Nat) | 440.0 | 4.0 | 110 | 80.0 | 5.5 |
| `Tail.reverse` | 737.0 | 8.0 | 92 | 131.0 | 5.6 |
| `List.append` (per output cons) | 676.5 | 5.9 | 115 | 128.9 | 5.2 |
| `levelHasParam` (no param: full walk) | 412.2 | 26.5 | 16 | 77.3 | 5.3 |

Notes: gcc inlines ~3 levels of the tree recursions, so `core` for trees depends on depth mod 3 (hence perfect trees of equal depth mod 3);
gcc turns `NonTail.sum` into a loop (4/node) — ours keeps real calls. `levelHasParam` core is 26.5/node (recursion over a `switch` with short-circuit `||`; not analysed further). Ours does not allocate on the heap beyond the work block; counts include decoding every input byte.

## 3. Top 3 causes of slowness (inductive code; `trace_ind.py` = per-pc counts of the steady state, `classify_ind.py` = shares)

1. **Constants built bit by bit: 44–51 % of all instructions.** Every literal/offset is `li r,0` then `slli r,r,1` / `addi r,r,1` per bit
   (`classify_ind.py`: ladder 45 % count, 49 % mirror, 46 % nontail, 51 % reverse, 50 % append, 44 % hasparam). Example, field `x` of a cell
   (`F`, pc `ed0`–`ee8`): `li t2,0; slli; addi; slli; addi; sll t1,t1,t2` = a shift by 3 in 6 instructions where gcc has `slli`/an immediate offset;
   the 8-byte payload read in `dec` is 8 × (`add; add; li+ladder(2–7); add; add; lbu; sd; ld; li+ladder(5); sll; ld; add; sd` ≈ 28). Constants are
   rebuilt at each use, never as immediates.
2. **Every variable lives in a frame slot, every call zero-fills 16 argument slots: 16–24 % slot traffic + 8–10 % `add rd,zero,rs` moves.**
   The plain back end (`compP`) has no register allocation for these programs: `ld/sd off(gp)` is 161 of 684 instrs/node for `count`,
   and each call stores 16 outgoing slots, almost all `li t0,0; sd t0,k(gp)` (`F` pcs `1034`–`1098`, ≈ 34 instrs per call, ≈ 70/node with 2 calls/node
   = 10 % of `count`). gcc keeps `count` in 8.7 instrs/node (a0, ra, 2 saved registers).
3. **The interface decodes and encodes the byte format: `dec` is 421 of 684 (62 %) for `count`**, 421/1189 mirror (+ `enc` 367), 306/440 nontail,
   306/737 reverse (+ `enc` 268), 205/412 hasparam; the function proper (`F`) is 251 / 389 / 128 / 163 / 196. A C program that gets the same bytes pays this too:
   gcc e2e is 12× its core for `count` (99 of 108 instrs/node are decode). So of the 79× `ours/core` for `count`, ≈ 12× is the interface
   (not a compiler defect) and ≈ 6.4× is ours-vs-gcc on identical work. Inside `dec` the same causes 1 and 2 apply (byte loop unrolled ×8).

Ranking by instructions removable (from the shares above, not tried): (1) immediates instead of ladders ≈ half; (2) registers/no zero-fill ≈ 25–30 %; (3) the interface cost is fixed by the byte format.

## Caveats
- Instruction counts, not cycles (QEMU `-icount`); gcc's `lbu`/`sd` weights are not modelled.
- Ours and gcc are checked on identical inputs, but the gcc e2e encoder/decoder are my C re-implementation of the byte format (`ind.c`), written with byte loops.
- `Pos.*`, `graftLeft`, `Level.isNeverZero` not benchmarked (not requested).
- The tree benchmarks use perfect trees; list `append` counts both lists' nodes.
