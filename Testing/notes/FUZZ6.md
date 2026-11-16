# FUZZ6: differential tests of the entries of NOTES sections 18-21

**Result: 0 mismatches, 0 bound violations, no reproducer.** QEMU: 15 419 cases (38 entries; seeds 11 and 12 × 200 cases each, plus 219 large
cases); Sail: 1 406 cases (all 38 entries). Each QEMU case of seeds 11/12 was run again in a block cut to the bytes it uses (see below).
No compiler source was changed; the words are the committed `Testing/asm/frontx-words/*.words`. Built on `origin/fuzz5` (harness) merged with
`origin/main` (`fuzz5` predates sections 18-21; the merge is the only non-test change on the branch).

## Entries (38)
| section | entries |
|---|---|
| 18, more than 16 locals | `tinycompile` (17 slots), `optfirstthirdfifthe`, `errfirstthirdfifthe` (19), `optfirstthirdfifthseventhe`, `optmfirstthirdfifthseventhe`, `errfirstthirdfifthseventhe`, `errinfixfirstthirdfifthseventhe` (27), `addpoints16e` (17) |
| 19, comparisons / `if` / enums | `tree_contains5`, `tree_insert5`, `list_elem5`, `list_erase5`, `ordering_swap/then/isle/iseq`, `weekday_isweekend_a/b`, `hashofdatae`, `bvarofdatae`, `fvarofdatae`, `lpofdatae`, `hash32e`, `satprede`, `satsucce`, `packdatae` |
| 20, word arrays | `wa_crc32`, `wa_crcupdate`, `wa_countlengths` (maxBits 15), `wa_countlengths7` |
| 21, several functions | `pos_mul`, `nontail_reverse_ln`, `eq_bintree`, `pos_comp`, `tree_containsk`, `tree_findk`, `level_combining`, `level_simplify` |

## Method (`Testing/asm/fuzz6/`)
- `ref6.lean` (`lean --run`, Lean 4.29.0): the verbatim source functions (fp-lean @0abeea5, `doc/examples/bintree.lean`, core, con-leche @6810492,
  lean-zip @7e10583, `tc` of `TinySelf.lean`) and my own byte decoders / encoders (assert that every input byte is consumed). It reproduces the
  results of all (about 1 900) committed `frontx-words/*.cases` (`xcheck.py`: 0 differences), so my encoders are the repo's formats.
  `fuzz6.py` has an independent Python reference (zlib for CRC); Lean and Python must agree on every case before anything runs on the machine.
- Inputs. Sizes: empty, 1, 2, 3, then 4-1000 (random, at most 60 / 120 / 150 for the quadratic `pos_mul` / `nontail_reverse_ln` / `level_simplify`),
  large (`big`, QEMU only): trees of 20 000 nodes (left, right, zig-zag, wide, random; 400 KB for the pair `eq_bintree`), lists of 30 000, `Pos` of 30 000,
  Level of 5 000, `pos_mul` 90 × 90 (417 MB work block), `tinycompile` 100 000 bytes, CRC / counts of 1 000 000 bytes, `firstThirdFifthSeventh` on 100 000 bytes.
  Scalars: 0, 1, 2, 4, 5, 6, 127, 128, 255, 256, 2^31, 2^32 ± 1, 2^63 ± 1, 2^64 - 2, 2^64 - 1 (also as tree keys and list elements, so near the
  `T.small` bound 2^64) and ± 1 of them; for the packed-data helpers the divisor edges 32766 / 32767 / 32768 / 65535 / 65536 / 2^32 / 32767·65536 and
  neighbours; inputs shorter than 8 bytes (zero-extended) and longer. Trees: random, left / right chain, zig-zag, comb, breadth-first wide, and binary search
  trees built by the library's `insert` (random, ascending, descending, alternating keys, repeated key 5); `eq_bintree` pairs equal, one payload off by one, one
  subtree dropped, unrelated; `findK` / `containsK` keys present, absent, neighbours of present keys, 0, 5, 2^63, 2^64 - 1. Pos pairs of equal / ± 1 lengths,
  `one`. Lists with many 5s. Levels: chains, right-nested, random, and imax with a left side that simplifies to `zero` / `succ zero` (the `ls = .zero || ls = .succ .zero`
  test). `firstThirdFifth(Seventh)`: lengths 0-9 (the index edges 4 and 6), 20, 200, 100 000. `tinycompile`: opcodes 0-9 and others, arguments around 127 / 128, odd lengths.
  CRC / counts: random, all 0, all 0xFF, values ≤ 15, values at `maxBits ± 1`.
- Per case: layout `[G in G][out G][G work G]`, G = 16 guard bytes; output buffer exactly Lean's result length, pre-filled random; work block random-filled and
  **exactly the bound of the entry's theorem**: `8 (N + 1) + 7` (plain), `8 (A + B n) + 8 (N + 1) + 7` (`wa`), `A + B n` (`ind`), `Ind.spaceA m nl cells n` (`indw`, cells =
  the cells this input allocates; `findK` / `containsK`: `Ind.spaceA 1 16 (M n)`, M = 1 / 0 as in the committed `.cases`); `sp` = block end.
- Cells of the `indw` entries. `pos_mul`: `Σ_{j<m} (q + j (q + 1) + 1)`; `nontail_reverse_ln`: `n(n+1)/2 + n` (both reproduce the 50 committed work sizes exactly
  and equal the machine's heap use on every case: a first QEMU pass with a generous block reads the heap high-water mark, `4 + 4·(decoded cells) + 4·cells` words;
  mismatch would be a failure). `level_simplify`: no closed form found (see below), the cells are read off the heap of the first pass, and the second pass uses
  `Ind.spaceA 2 20 cells n` with that count. `findK`: heap use ≤ `n` cells asserted.
- Checks: output bytes = Lean = Python; `a1` = result length for tree / list / Pos / `tinycompile` / `countLengths` results; `gp`, `sp` restored; guards below and above
  input, output and work block; QEMU: the whole memory image outside output + work block + result slots is unchanged; Sail: every write lands in output or work block.
- Space. QEMU is run twice with different random fills; a byte is *written* iff it differs from its fill in either run. The longest never-written run (heap grows up,
  stack down) is the slack: > 0 in every case; the largest fraction of the block written: 13.1 % (`tree_contains5`, `list_elem5`, weekday, ordering), 3-11 % for the other
  inductive entries, 89-99.7 % for the frame-only entries (scalars, `firstThirdFifth*`, `tinycompile`, `wa_*`). **Shrink**: every case of seeds 11 / 12 was run again with the work block
  cut to the bytes it wrote (the bound minus the longest never-written run, whole words): same outputs, guards intact; smallest block / bound 0.005 (`tree_insert5`,
  `tree_findk`) to 1.000. The bounds of the scalar / `wa` entries are exact: `wa_crc32` writes 99.7 % of its 2159 bytes, and a block of 8 bytes less fails (`SHORT=8`: `gp/sp` or work
  guard broken, for `wa_crc32`, `hash32e`, `optfirstthirdfifthseventhe`, `tinycompile`); the inductive bounds are loose by a factor 8-200 on all inputs tried.
- Harness sanity: a corrupted expected byte is rejected (`CORRUPT=1`); a block shorter than the bound is rejected (`SHORT=k`).
- Sail: only the `mem[W` lines of the trace are kept (`--trace-mem --trace-output /dev/stdout | grep`; no trace file exists), inputs ≤ 1500 bytes (`pos_mul` ≤ 70, `nontail_reverse_ln` ≤ 400,
  `level_simplify` ≤ 300), 19-40 cases per entry; the disk was never at risk (a 3 GB work directory at the peak was QEMU images, removed after each run).

## Runs
| entry | QEMU cases (seed 11 + 12) | largest input of those (B) | large cases (largest B) | Sail cases (largest B) | max fraction of block written | smallest used block / bound |
|---|---|---|---|---|---|---|
| pos_mul | 200+200 | 122 | 11 (≤182) | 21 (≤50) | 0.086 | 0.032 |
| nontail_reverse_ln | 200+200 | 1081 | 11 (≤2251) | 19 (≤289) | 0.069 | 0.020 |
| eq_bintree | 200+200 | 31982 | 13 (≤399982) | 23 (≤1032) | 0.109 | 0.009 |
| pos_comp | 200+200 | 1603 | 11 (≤30002) | 37 (≤1086) | 0.085 | 0.044 |
| tree_containsk | 200+200 | 15999 | 13 (≤200009) | 31 (≤1379) | 0.035 | 0.009 |
| tree_findk | 200+200 | 12119 | 13 (≤200009) | 33 (≤1239) | 0.023 | 0.005 |
| tree_contains5 | 200+200 | 15991 | 13 (≤200001) | 32 (≤1361) | 0.131 | 0.009 |
| tree_insert5 | 200+200 | 16001 | 13 (≤200001) | 37 (≤1491) | 0.114 | 0.005 |
| list_elem5 | 200+200 | 7201 | 11 (≤270001) | 32 (≤1369) | 0.131 | 0.013 |
| list_erase5 | 200+200 | 7201 | 11 (≤270001) | 29 (≤1405) | 0.102 | 0.008 |
| weekday_isweekend_a | 200+200 | 1 | – | 40 (≤1) | 0.131 | 0.131 |
| weekday_isweekend_b | 200+200 | 1 | – | 40 (≤1) | 0.131 | 0.131 |
| ordering_swap | 200+200 | 1 | – | 40 (≤1) | 0.114 | 0.102 |
| ordering_then | 200+200 | 2 | – | 40 (≤2) | 0.109 | 0.109 |
| ordering_isle | 200+200 | 1 | – | 40 (≤1) | 0.131 | 0.131 |
| ordering_iseq | 200+200 | 1 | – | 40 (≤1) | 0.131 | 0.131 |
| level_combining | 200+200 | 4901 | 11 (≤2350) | 34 (≤1146) | 0.085 | 0.026 |
| level_simplify | 200+200 | 501 | 11 (≤981) | 38 (≤201) | 0.078 | 0.023 |
| hashofdatae | 200+200 | 20 | – | 40 (≤20) | 0.932 | 1.000 |
| bvarofdatae | 200+200 | 20 | – | 40 (≤20) | 0.932 | 1.000 |
| fvarofdatae | 200+200 | 20 | – | 40 (≤20) | 0.932 | 1.000 |
| lpofdatae | 200+200 | 20 | – | 40 (≤20) | 0.932 | 1.000 |
| hash32e | 200+200 | 20 | – | 40 (≤20) | 0.932 | 1.000 |
| satprede | 200+200 | 20 | – | 40 (≤20) | 0.932 | 1.000 |
| satsucce | 200+200 | 20 | – | 40 (≤20) | 0.889 | 1.000 |
| packdatae | 200+200 | 20 | – | 40 (≤20) | 0.937 | 1.000 |
| addpoints16e | 200+200 | 9 | – | 40 (≤9) | 0.954 | 1.000 |
| optfirstthirdfifthe | 200+200 | 200 | 1 (≤100000) | 40 (≤200) | 0.958 | 1.000 |
| errfirstthirdfifthe | 200+200 | 200 | 1 (≤100000) | 40 (≤200) | 0.958 | 1.000 |
| optfirstthirdfifthseventhe | 200+200 | 200 | 1 (≤100000) | 40 (≤31) | 0.970 | 1.000 |
| optmfirstthirdfifthseventhe | 200+200 | 200 | 1 (≤100000) | 40 (≤200) | 0.970 | 1.000 |
| errfirstthirdfifthseventhe | 200+200 | 200 | 1 (≤100000) | 40 (≤200) | 0.970 | 1.000 |
| errinfixfirstthirdfifthseventhe | 200+200 | 200 | 1 (≤100000) | 40 (≤200) | 0.970 | 1.000 |
| tinycompile | 200+200 | 977 | 12 (≤100000) | 40 (≤920) | 0.954 | 1.000 |
| wa_crc32 | 200+200 | 996 | 12 (≤1000000) | 40 (≤901) | 0.997 | 1.000 |
| wa_crcupdate | 200+200 | 987 | 12 (≤1000000) | 40 (≤976) | 0.997 | 1.000 |
| wa_countlengths | 200+200 | 996 | 12 (≤1000000) | 40 (≤987) | 0.977 | 1.000 |
| wa_countlengths7 | 200+200 | 998 | 12 (≤1000000) | 40 (≤936) | 0.971 | 1.000 |

(`hashofdatae` … `weekday_*`, `ordering_*`: no large case, the input is one word / one tag.)

Failures: none, so no reproducers. The only things that failed while building the harness were errors of the harness itself (Python `IndexError` on a short `firstThirdFifth` input in my own generator,
an `assert` on a heap measure that was not rounded to cells, the Sail write-set built as a Python `set` of every work byte, which ran out of memory on 500 MB blocks); all fixed before the runs above.
Reproduce: `bash Testing/asm/fuzz6/runall6.sh seed1|seed2|big|sail` (Lean 4.29.0 in `/tmp/leandl/x/*/bin`, `qemu-system-riscv64`, `riscv64-linux-gnu-gcc`, Sail 0.9 at the path in `fuzz6.py`); one entry:
`SHRINK=1 python3 Testing/asm/fuzz6/fuzz6.py FN SEED N qemu` (`sail`, `big` as 4th / 5th argument; `SAILMAX`, `BUDGET`, `CORRUPT`, `SHORT` in the header of `fuzz6.py`); `python3 Testing/asm/fuzz6/xcheck.py FN…`.

## Observations (not failures)
- `level_simplify` allocates far more than one cell per node: committed case `imax (succ (max zero param)) param` (4 nodes) is accounted 5 cells, and nested imax grows the count fast (the machine's own count is
  used for the bound; my estimate `2·cells(l) + cells(r) + 3` per imax, which assumes the front end inlines the two `let`s, gated the generator but does not match the machine's count exactly; hypothesis only, not
  checked against the compiled terms, which I could not elaborate here: the Lean build needs `../deps/sail-riscv-lean`). Any test of `simplify` on deep imax nests has to bound the nesting: with 300 nested imax the
  QEMU run did not finish in minutes. Not a wrong result, a cost of the compiled program; the theorem's `cellsSup` accounts for it.
- NOTES.md section 21 (on `origin/main`) ends in the middle of the section ("Other options of the whole program …", no table of entries, no speed / not-done list), and `TinySelf.lean`'s header says every tiny
  instruction compiles to 3 words while `tc` emits 4 bytes per instruction. Documentation only.
- Not covered: malformed input bytes (the specs say nothing); `Level.param` names (dropped by the format); `tinyCompile` programs are checked as bytes (the compiled code of the 5 tiny programs was not run: `tiny/selfhost_test.py` does that);
  `crc` / `countLengths` for inputs ≥ 2^32 bytes; Sail only on inputs ≤ 1.5 KB; the generated words were not rebuilt (no Lean/Sail model build on this box), so the committed `.words` were tested as they are.
