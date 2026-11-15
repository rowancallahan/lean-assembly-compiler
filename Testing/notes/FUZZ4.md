# FUZZ4: differential tests of the §13–15 front-end features

**Result: 0 mismatches on QEMU RISC-V. No spec gap found. Sail was not run** (no Sail C emulator in this box; the downloaded release binary was not run).

Entry points: `adlere adlerstatee` (foldl, tuple state, `%`/`/`), `replacexe fromoptione smalle swape addpointse zeroxe neste` (structures/tuples, byte results), `nontailsumrec nontaillengthrec fibLen` (real calls). The fast loops of §13 are inside the Adler and recursion entry points.
Built from `origin/main` + `origin/fuzz3` (merged); words regenerated from the current build are byte-identical to `Testing/asm/frontx-words/`.

## Method
- `Testing/asm/fuzz4/emit.lean` (`SEED=s OUT=dir lake env lean --tstack=4000000 Testing/asm/fuzz4/emit.lean`): ~900 inputs per function with the result of executed Lean (`#eval` of the original function).
  Adler/recursion: empty, all single bytes, constant 0x00/0xFF/1/254/128 at lengths 2..5554 (5552 = zlib NMAX), prefixes summing to 65519..65522, 65535, 65536, 131041..131043 with tails `[],[0],[1],[255],0*8,…` (front and back), 600 random (full, 2-letter, {0,255}, 254/255 alphabets), Adler also 65520–70000 long.
  Small entries: all lengths 0..10 × bytes 0,1,15,16,17,127,128,254,255, 700 random (to 3000 bytes). `fibLen`: lengths 0..29.
- `Testing/asm/fuzz4/frontx_fuzz4.py` (from fuzz3's harness): QEMU; per case in/out/work blocks with guards, output pre-filled with random bytes, work block exactly `space n` (`8(slots+1)+7`, or `frame(n+1)+32`).
  Checks: output = Lean = independent Python reference (zlib.adler32 for `adlere`; own Adler state for `adlerstatee`), gp/sp restored, guards intact, the whole QEMU memory image outside output+work equals the initial image. `ONLYHUGE=1`: 9 inputs per function up to 2^20 bytes (also 65520/65521/65522, 5552/5553), Python reference only (Lean's list recursion cannot take them).
  Stack use: the lowest touched byte of the work block is the block's first byte in all cases, so `space n` is tight for every entry and the guard below the block was never hit. (Single-run output only; no per-length check.)
- `a1` is only a result for list results (none here), so it is not checked.

## Runs
| run | functions | cases each | mismatches |
|---|---|---|---|
| seed 1, FILL 1, QEMU | 12 | 799–901 (fiblen 30) | 0 |
| seed 2, FILL 2, QEMU | 12 | 799–901 (fiblen 30) | 0 |
| ONLYHUGE (up to 2^20 bytes) | 11 (not fibLen) | 9 | 0 |

Harness sanity: a corrupted Lean result in a case file is rejected.
Limits: `fibLen` only to length 29 (fib is exponential; the proved range is 2^20); no Sail; two seeds; work block filled with one pattern (0x77) only.
