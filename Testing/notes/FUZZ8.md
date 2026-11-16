# FUZZ8: differential tests of the strings / Name entries of NOTES section 23

**Result: 0 mismatches, 0 bound violations, no reproducer, on QEMU (all) and Sail (sample).**
Entries: `name_beq`, `name_bbeq`, `level_beq`, `level_bbeq` (`Riscv/Frontx/NameExamples.lean`; words `Testing/asm/frontx-words/*.words`, tested as committed).
No compiler source changed. Harness = `origin/fuzz6`'s `fuzz6.py` (imported: layout, guards, QEMU image diff, slack, shrink pass) plus `fuzz8.py`, `ref8.lean`, `runall8.sh`.

## Method (`Testing/asm/fuzz6/`)
- `ref8.lean` (`lean --run`, Lean 4.29.0): the verbatim con-leche `Name`, `Level`, `Name.decEq`, `Level.decEq` copied from `IndExamples.lean` / `Ind2Examples.lean`, `Name.beq`, `Level.beq`, `==`;
  own byte decoders (formats of section 23: Name tags 0/1/2, string = cons(4)+byte … nil(3), num = 8 bytes LE; Level 0-4, names 5-7, bytes 8/9). They assert every byte is consumed and that string bytes are valid UTF-8.
  `fuzz8.py` has an independent Python structural equality; Lean and Python must agree on every case before anything runs on the machine.
- Per case (fuzz6 harness): `[G in G][out G][G work G]`, output buffer exactly 1 byte pre-filled random, work block random-filled and exactly the stated bound `Ind.spaceA m 16 0 n`
  (m = 2 names, 3 levels; n = input bytes), `sp` = block end. Checks: output = Lean = Python; `gp`, `sp` restored; guards around input, output, work; the whole image outside output + work unchanged.
  QEMU run twice with different fills to find written bytes; heap/stack gap > 0 asserted; second pass (`SHRINK=1`) reruns each case with the block cut to the bytes it wrote.
- Inputs. Strings: empty, `"\0"`, `"\0\0"`, `"a\0"`, `"\0a"`, 2-byte (`é`, `λ`, U+07FF, U+0080), 3-byte (`€`, U+0800, U+D7FF, U+E000, U+FFFD, U+FEFF, U+FFFF, U+FFFE, U+2028),
  4-byte (`😀`, U+10000, U+10FFFF), `e`+U+0301 vs `é`, control bytes, random scalar values over the whole range, concatenations, 100-800 random chars, and runs of 64/255/256/257/1000 copies of one char.
  Numbers: 0, 1, 2, 127, 128, 255, 256, 2^32±1, 2^63-1/2^63/2^63+1, 2^64-2, 2^64-1, random. Names: depth 0-300 mixed `str`/`num`; chains up to 20 000 deep (large cases).
  Levels: chain / right / left / random trees, up to ~300 nodes (large: 1 000, 2 000), leaves `zero` and `param` with names of depth 0-8; `max`/`imax` mixed.
  Pairs: equal (30 %), near-equal (45 %: last/any component changed, number ±1 / +2^63, string +NUL / truncated / last char ±1, component appended / dropped / duplicated, `str`↔`num` swap; levels: a param name mutated, `max`↔`imax`, arguments swapped, a `succ` wrapped, a node replaced by `zero`), unrelated (25 %); 15 % of pairs swapped.
- Runs (all pass): seeds 21 and 22 × 200 cases per entry (shrink pass included): 3 200 cases; large (`big`, seed 23, plus seeds 26, 27 for `level_beq`):
  `name_beq` 16, `name_bbeq` 16, `level_bbeq` 14, `level_beq` 12 + 12 + 14 cases; largest input 613 388 B (`name_beq`), 357 395 B (`level_beq`), work blocks up to 770 MB.
  Equal/different ratio per run roughly 30/70. Max fraction of the work block written 6.0 % (names), 5.2 % (levels); smallest shrunk block / bound 0.0084.
- Harness sanity: `CORRUPT=1` (an expected byte flipped) is rejected. `SHORT=8` (block 8 bytes short) is NOT rejected: these bounds are loose by ~15-100x (heap/stack gap ≥ 94 % of the block), so the shrink pass is the evidence that the stated work size suffices, not tightness.

## Failures
None, so no reproducers.

## Notes / limits
- The stated size suffices for every input tried; it is far from tight (smallest used block 0.8-1.2 % of the bound).
- QEMU `virt` puts the fdt at 0xbfe00000, so one image (input + work) must stay under about 1 GB; large level cases whose work block exceeded 850 MB were dropped by the generator (`fuzz8.py`, `big`). An earlier attempt with 20 000-node levels hung for that reason (harness limit, not a compiler result).
- Not covered: malformed input bytes (invalid UTF-8 / bad tags: the spec does not define them), numbers ≥ 2^64 (outside the range subtype), names deeper than 20 000, levels above ~2 000 nodes.

## Sail (sample)
Sail 0.9+ release `sail_riscv_sim` (`--trace-mem --trace-output /dev/stdout`, piped through `grep` for `mem[W`; no trace file is written), seed 24, 120 generated cases per entry, keeping inputs <= 2000 B,
`Testing/asm/ctest` deleted after each entry. Every write lands in output or work block; outputs equal Lean. `name_beq` 46 cases (largest 1957 B), `name_bbeq` 34 (1178 B), `level_beq` 60 (1896 B), `level_bbeq` 52 (1922 B); 192 in all, 66 equal / 126 different.
Sail was not used for the shrink pass or for large inputs.

Reproduce: `bash Testing/asm/fuzz6/runall8.sh seed1|seed2|big|sail`; one entry: `SHRINK=1 python3 Testing/asm/fuzz6/fuzz8.py name_beq 21 200 qemu`. Needs Lean 4.29.0 in `/tmp/leandl/x/*/bin`, `qemu-system-riscv64`, `riscv64-linux-gnu-gcc`.
