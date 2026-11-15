# FUZZ3: differential tests of the Frontx entry points

**Result: 0 mismatches.** No spec gap found.

Entry points: `take5 drop5 matchDrop3 filterAll incEach twice headOf finalOf findFirstGt3` and `tailSum nonTailSum tailLength bookLength`.
No AArch64 version of any Frontx entry point exists, so ARM was not compared.

## Method
- `Testing/asm/fuzz3/emit.lean`: `SEED=1 OUT=/tmp/fuzz3 lake env lean Testing/asm/fuzz3/emit.lean` writes 638 inputs per function with the result from executed Lean (`#eval`).
  Inputs: empty; length 1 (bytes 0..10, 127, 128, 254, 255); lengths 1-9, 16, 63-65, 255, 256, 1000, 4096 filled with 0x00, 0xFF, 3, 4, 5, 127, 128; 500 random inputs (up to 3000 bytes, a third over bytes 0..7 to hit the `> 3` threshold); one 6000-byte case each of zeros, 0xFF, small-alphabet random.
- `Testing/asm/fuzz3/frontx_fuzz.py` (from `frontx_test.py`): `CASESDIR=/tmp/fuzz3 CTEST=dir [NOSAIL=1] [HUGE=1] python3 frontx_fuzz.py check N fn`.
  Per case: output block exactly the result length, work block exactly `8*(slots+1)+7` (= `space n`), 16 guard bytes around each block.
  Checks: output = Lean result = independent Python reference, `a1` = result length (list results), gp and sp restored, guards intact, and (new) the whole QEMU memory image outside output and work equals the initial image.
  Sail (optional): every data write lands in output or work.
- `HUGE=1` adds inputs of the maximum allowed length 2^20 (zeros, 0xFF, small-alphabet random) and 65537 random bytes; expected results from the Python references only, because Lean's interpreter hits deep recursion on 2^15-element non-tail lists (`filterAll`, `incEach`, `nonTailSum`).

## Runs
| run | cases per function | functions | mismatches |
|---|---|---|---|
| QEMU RISC-V, all checks, incl. 4 huge inputs (up to 2^20) | 642 | 13 | 0 |
| QEMU + Sail C emulator (first 300 cases, inputs up to 4096) | 300 | 13 | 0 |

Sanity check of the harness: corrupting a Lean result in a case file makes it fail.
Limits: the Sail run has no inputs above 4096 bytes; the tests use one seed; `nonTailSum` was only run to 2^20 on QEMU.
