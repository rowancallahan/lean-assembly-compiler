# FUZZ9: differential tests of the `Expr` entries (NOTES §25) and the higher-order entries (§27)

**Result: 0 mismatches, 0 bound violations, no reproducer.** QEMU: 10 780 cases (35 entries × seeds 21, 22 at 150 cases + seed 23 at 8 large cases);
Sail: 957 cases (30 per entry, inputs ≤ 1500 B). No compiler source was changed; words are the committed `Testing/asm/frontx-words/*.words`
(TinyRepro has none committed: `emit9.lean` writes `fuzz9/words/tinyr*.words` from `TinyR*.comp.code`).

## Entries (35)
- §25 (11): `hasFvar`, `closed0`, `inst1`, `sizeF`, `scopedD`, `isForallE`, `getAppFn`, `piResult`, `fvarTypeD`, `numArgs`, `isLit` (`expr_*`).
- TinyRepro (4): `tinyr1` (r1), `tinyr2` (r2), `tinyr3` (r3), `tinyr5` (r5). **r4 does not exist** in `Riscv/Frontx/TinyRepro.lean` (only r1, r2, r3, r5 are compiled).
- §27 (20): every `hof_*` entry (`mapInc`, `mapComp`, `mapXor`, `filterGt3`, `filterNZ`, `dupAll`, `stageMap`, `pipe2`, `xstageFilter`, `nonFindGt3`, `findGt3`,
  `foldrSum`, `sumFoldl`, `xorArr`, `anyNL`, `allAscii`, `findHigh`, `countSp`, `arrFindGt3`, `countAbove100`).

## Method (`Testing/asm/fuzz9/`)
- `gen9.lean` (`G9="ENTRY SEED N [big]" lake env lean --tstack=16000000 gen9.lean`, `ulimit -s unlimited`): random inputs built in Lean, the expected result
  is the repo's own executed function and encoder (`TExpr.enc`, `Res.enc`, `TinyRn.InsT.enc`), and the entry's own allocation model (`pg.al`, `pg.M`) gives
  the cells. There is no second (Python) reference for these entries.
- Exprs: all 10 constructors; `Name`s (str / num, multi-byte and long strings, `Nat`s to 2^64-1), `Level`s, `List Level`, literals (`natVal` at the
  edges 0, 1, 2^31, 2^32±1, 2^63±1, 2^64-2, 2^64-1; `strVal` empty, NUL, UTF-8, 70 chars); loose bvar indices at the binder depth, depth±1, 2^64-1;
  fvar indices random / 2^64-1. Shapes: random trees with skewed size splits (one deep child, long left / right spine), binder chains (lam / forallE / letE mixed,
  bodies referring to the binders), left- and right-nested app spines (≤ 1500), Pi chains ending in an application of a bound variable, let chains, lam chains around spines,
  proj chains. Contexts: unrestricted, closed (bvars below the binder depth), no fvar, scoped (fvar index < bound, types built at the lowered bound; `scopedD` queries
  the bound, ±1, 2^64-1, random). Large cases: 3 000 – 20 000 nodes (inputs up to 162 kB, `inst1` results up to 172 kB). The Bool entries are balanced
  (hasFvar true 77/150, closed0 54/150, scopedD 85/150, isForallE 12/150, isLit 8/150 in seed 21). `inst1`'s second argument: a `bvar`, a small Expr, an Expr built at binder depth 2.
- TinyRepro: random `Ex` trees (skewed splits, up to 700 fuel; `UInt64` literals random / edges), `comp` / `compile` results.
- Hof: byte arrays of length 0-3, then ≤ 3000 (mixes of random, ≤ 7, the thresholds 0 3 4 5 10 32 100 101 127 128 255, `255 - i%5`); large: 20 000 and 100 000 bytes.
- Machine per case (from fuzz6): layout `[G in G][out G][G work G]`, output pre-filled random, work block random-filled and **exactly the stated bound**
  (`Ind.spaceA m nl cells n` with `(m, nl)` read from the `implements1` theorems: 1/16, `inst1` 1/19, r1 2/20, r2 2/17, r3 2/16, r5 1/16 with `M·n`; `8 (slots+1) + 7` for `hof_*`).
  Checks: output = Lean; `a1` = result length (`retLen` entries); `gp`, `sp` restored; guards around input, output and work block; QEMU: the whole image outside
  output + work + result slots unchanged, run with two different fills, heap/stack gap > 0 (min gap / block: 0.89-0.97 for `indw` entries; the bounds are loose by about 10×);
  Sail: only `mem[W` lines of the trace are kept, every write lies in output or work block. `Testing/asm/ctest` was never created.
- Harness sanity: `CORRUPT=1` (a corrupted expected byte) is rejected. A block 64 B shorter than the bound is *not* rejected for the loose `indw` bounds (expected; the exact-bound check of fuzz6 applies to the scalar entries only).

## Incidents (not compiler failures)
- First run: 5 jobs (`expr_hasfvar`, `expr_inst1`, `expr_scopedd`, `hof_filtergt3`, `hof_foldrsum`, one seed each) died in the **Lean reference** with
  "deep recursion was detected at 'interpreter'" (the model `pg.al` / the book's non-tail functions on 10 000+ deep inputs). Fixed in the harness by `lean --tstack=16000000`; all 15 re-runs of those entries passed.
  So the stack-heavy inputs are run on the machine only because the reference gets a large interpreter stack.

## Limits of this fuzzing
- `Nat`s ≥ 2^64 are not representable in the input format (8 bytes), so they were not tested. Inputs are < 2^20 B (the `implements1` bound).
- The work bound used is this input's cells (`pg.al`), at most the theorem's `cellsSup`; the machine's heap use was not compared with the model (unlike fuzz6's `measure`).
- Sail covers ≤ 1500-byte inputs only; deep chains (> a few hundred nodes) ran on QEMU only.
