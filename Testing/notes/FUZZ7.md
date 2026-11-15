# FUZZ7: differential tests of multiply / divide / remainder / variable shifts (NOTES section 22)

**Result: 0 mismatches, no failure, so no reproducers.** No compiler source changed; the words are the committed `frontx-words/*.words`.
QEMU: 2 seeds x 10 entries (about 1450 to 1740 cases each, 14 000+ per seed) + 1 large run; Sail: 10 entries (all cases of the
scalar entries, about 1200 to 1740; 119 for kraft/nextcodes).

Entries: `wa_kraft` (`kraftE`), `wa_nextcodes` (`nextCodesE`), `wa_gcd`, `fx_gcd` (`Nat.gcd`, wa and list paths), `wa_ops64/32/n`
(`ops64E/ops32E/opsNE`, wa), `fx_ops64/32/n` (same, list path).

## Method (`Testing/asm/fuzz7/`)
- Expected bytes: `ref.lean` (`lean --run`, Lean 4.29.0) = the source functions copied verbatim (lean-zip @7e10583
  `countLengthsFast`/`kraftSumFast`/`nextCodesFast`, core `Nat.gcd`, the `ops` expressions and the entries' byte readers), executed.
  `fuzz7.py` also has an independent Python reference (own histogram, Kraft sum, next codes, gcd, `ops`); Lean and Python must agree
  before anything runs on the machine (they did on every case).
- Inputs. Scalars: operands `a` in {0, 1, 2, 3, 5, 255, 256, 2^31-1, 2^31, 2^31+1, 2^32-2, 2^32-1, 2^32, 2^32+1, 2^32+5, 2^48, 2^62,
  2^63-1, 2^63, 2^63+1, 2^64-2, 2^64-1, ...} x divisors/shift amounts `b` in {0, 1, 2, 3, 7, 2^31, 2^32-1, 2^32, 2^32+1, 2^63,
  2^63+1, 2^64-2, 2^64-1, 0..130}; every `b` in 0..130 for seven fixed `a`; Fibonacci pairs both ways (gcd); random (uniform, small,
  edge); 32-bit entries get the operands mod 2^32 (so also near 2^32 wrap in the product); `fx_ops32` gets random garbage in the high
  halves (masking); 3% short inputs (missing bytes read 0, so `b = 0`), 3% trailing bytes. kraft/nextcodes: lengths 0..15, 0..255,
  constant arrays, mostly zeros, gaussian around 8, {0,1,2,15,16,255}, fixed-Huffman lengths, `range 256`, empty, up to 3000 bytes;
  large run adds 140000, 131072, 131071 bytes of `1` (code wraps mod 2^32 in `nextCodes`: 140000 * 2^15 > 2^32), 70000 and 100000 random.
- Per case: layout `[G in G][out G][pad][G work G]`, G = 16 guard bytes; the output buffer is exactly Lean's result length; the work block
  is exactly the stated size (wa: `8 (A + B n) + 8 (N + 1) + 7`, fx: `8 (slots + 1) + 7`), `sp` = block end; output and work are
  random-filled.
- Checks: output bytes == Lean == Python; `a1 == 64` for `wa_nextcodes` (list result); `gp`, `sp` restored; guards on both sides of the
  input, output and work block; QEMU: the whole memory image outside output + work block + result slots equals the initial image;
  Sail (`--trace-mem`, piped through `grep 'mem\[W'`, work files deleted after each run): every write lies in output, work block, result
  slots or `tohost`.
- Work size: QEMU runs twice, fill A and its bitwise complement. Output identical in both (no read of uninitialised memory); bytes equal
  in both final work blocks were written. Largest fraction of the block written: kraft 0.975, nextcodes 0.985, gcd(wa) 0.873,
  gcd(fx) 0.966, ops(wa) 0.774, ops(fx) 0.970. The only never-written bytes are the 7 of the `+ 7` alignment slack, so the stated sizes
  are nearly exact for these entries (not loose as in FUZZ5) and were sufficient on every case (guards below and above intact, Sail writes all inside).
  Note the kraft/nextcodes `B` is 0: their work is independent of `n`, also on the 140000-byte input.
- Harness sanity: a mutant `wa_ops32.words` (first `divu` changed to `remu`) is rejected at the first affected case.

## Runs
| run | cases per entry | entries | mismatches |
|---|---|---|---|
| QEMU seed 1 (`runall.sh seed1`) | 1184 to 1736 | 10 | 0 |
| QEMU seed 2 | 1184 to 1643 | 10 | 0 |
| QEMU large (`big`, seed 3) | 45 (kraft/nextcodes, up to 140000 bytes) / 1171 to 1729 | 10 | 0 |
| Sail seed 4 (`sail`) | 119 (kraft/nextcodes) / 1185 to 1737 | 10 | 0 |

Reproduce: `bash Testing/asm/fuzz7/runall.sh seed1|seed2|big|sail` (Lean 4.29.0 in `/tmp/leandl/x/*/bin`, `qemu-system-riscv64`,
`riscv64-linux-gnu-gcc`, Sail 0.9 at `/home/user/deps/sailsim/...`, as `Testing/setup/box.sh`); one entry:
`python3 Testing/asm/fuzz7/fuzz7.py FN SEED N qemu|sail`.

## Limits
- Lean ref is a standalone copy of the source functions, not the repo's `Proven` definitions (the repo was not built here); the entry
  glue (`rd32`, `rd64`, `rd32u`, `u64At`) is copied from `WaMul.lean`/`MulExamples.lean`. A divergence between copy and repo would not be seen.
- `Nat` operands are always < 2^64 (the spec's `requires`); `a <<< b` for `Nat` with `b >= 64` is not an entry (NOTES "Not done").
- Input lengths below 2^32 only (kraft/nextcodes), at most 140000 bytes; Sail only on the sample sizes above (no 140000-byte inputs).
- `Nat.lcm` and signed operations are not implemented, so not tested. No `wa_ops` case reached 2^64 for `Nat` results beyond the
  mod-2^64 encoding (Lean's `Nat` result is reduced mod 2^64 by `Res.enc` before comparing).
