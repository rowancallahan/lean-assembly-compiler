# FUZZ10: differential tests of the newest compiled entries against executed Lean

**Result: 0 output mismatches, 0 guard or memory violations, 0 reproducers.** Covered: 55 entries (§26 `Int`, §29 monads, §32 structures, one harvest entry);
QEMU 22 000 cases (seeds 21 and 22, 200 per entry and seed), 1 764 + 1 701 large cases (`big`), Sail 2 200 cases (40 per entry, inputs ≤ 1500 B).
**Not covered** (no run here): §28 `name_beq`, `name_bbeq`, `level_beq`, `level_bbeq` (`indw` entries: the harness has no cell count for them and no Lean decoder
for `NameT.enc2` / `LevelN.enc2` inputs), the harvest entries of `ConLecheS1/S2/S3` (`expr_*`, `conleche_iscompound*`, `s3_*`) and `BookS1`
(`finite_issingleton`, `ind` bound). §28 strings and the three other harvest files are therefore not tested by this branch.

## Method (`Testing/asm/fuzz10/`)
- `ref10.lean`: the Lean reference. It imports the repo's own modules (`Riscv.Frontx.IntExamples`, `WaInt`, `StructExamples`, `WaStruct`, `MonadExamples`,
  `MixHash`, `WaMul`) and applies the same `f` as the emitter of each entry (`emit_int.lean`, `emit_struct.lean`, `emit_frontx.lean`, `emit_wa.lean`).
  It runs the real definitions, not copies. Built with Lean 4.29.0 from the restored build cache (`lake build` of the 11 `Riscv.Frontx` modules completed from the restored cache in about 9 s).
- `xcheck10.py`: the reference reproduces every committed case of the 55 entries (`Testing/asm/frontx-words/<fn>.cases`): **3 271 cases, 0 mismatches**.
- `fuzz10.py`: the QEMU / Sail machinery of `Testing/asm/fuzz6/fuzz6.py` (FUZZ6), without its Python reference: the executed Lean result is the expected output.
  Per case: `[G in G][out R G][G work G]`, `G = 16` guard bytes, output pre-filled random, work block random-filled and **exactly the bound the `.words` header states**:
  plain `N` → `8 (N + 1) + 7`, `wa A N B L` → `8 (A + B n) + 8 (N + 1) + 7` (n = input length). Checks: output = Lean; input, output and work guards; `gp`/`sp` restored;
  `a1` where the header asks; QEMU: the memory image outside output + work is unchanged, with two random fills (a byte is written iff it differs from its fill in either run);
  Sail: every `mem[W` write lies in an output or work block (trace filtered to `mem[W` lines, the full trace is never written).
- Inputs (random, seeded per entry):
  - `int_*`, `wa_int_*` (§26): 8-byte little-endian two's complement words from the edges `0, ±1, ±2, ±255, ±2^31`, `2^32 - 1`, `2^53 + 1`, `±2^63`, `2^63 - 2`, `2^63 - 1`,
    plus random 64-bit words; lengths 0–59 (short inputs are zero-extended by the entry).
  - `st_*`, `wa_entryat/lenat/symat` (§32): random structure bytes from a pool of flag-like values (`0, 0x01, 0x04, 0x08, 0x10, 0x20, 0x40, 0x7F, 0x80, 0xFF`) and random bytes, lengths 0–59 (big: 30 000 and 100 000).
    The `wa` index entries take 0–8 bytes with the index edges `0, 1, 127, 128, 254, 255`.
  - `mon_*` (§29): byte lists from `0, 1, 3, 4, 5, 31, 32, 33, 127, 255, 0xC3` and random bytes, lengths 0–59 (big: 30 000 and 100 000).
  - `wa_mixhash` (harvest `MixHash`): 16-byte `(h, k)` pairs from the 64-bit edges and random pairs.
- Work bounds are the committed header bounds, not measured ones: the slack and the written fractions below are reported from the QEMU double run.

## Results
Per entry: cases per seed (200 + 200), largest input in the QEMU runs, largest fraction of the work block written (the rest is slack), cases of the `big` run (63; for `mon_*`/`st_*` the 30 000 and 100 000 byte cases were added; the `int_*`/`wa_int_*` big run adds only lengths 0, 16, 40), Sail cases (40, inputs ≤ 1500 B), and the number of Lean `PANIC` messages on those runs.

| entry | QEMU seed 21 / 22 (cases each) | max input B | max written fraction | big (cases) | Sail (cases) | Lean PANIC (big / Sail) |
|---|---|---|---|---|---|---|
| `int_abs` | 200 / 200 | 59 | 0.941 | 63 | 40 | 0 / 0 |
| `int_ceil` | 200 / 200 | 59 | 0.951 | 63 | 40 | 0 / 0 |
| `int_clamp` | 200 / 200 | 59 | 0.941 | 63 | 40 | 0 / 0 |
| `int_clampix` | 200 / 200 | 59 | 0.971 | 63 | 40 | 0 / 0 |
| `int_clamplin` | 200 / 200 | 59 | 0.941 | 63 | 40 | 0 / 0 |
| `int_clampto` | 200 / 200 | 59 | 0.971 | 63 | 40 | 0 / 0 |
| `int_fitsi16` | 200 / 200 | 59 | 0.941 | 63 | 40 | 0 / 0 |
| `int_floor` | 200 / 200 | 59 | 0.951 | 63 | 40 | 0 / 0 |
| `int_inrange` | 200 / 200 | 59 | 0.941 | 63 | 40 | 0 / 0 |
| `int_insidew` | 200 / 200 | 59 | 0.973 | 63 | 40 | 0 / 0 |
| `int_lininrange` | 200 / 200 | 59 | 0.941 | 63 | 40 | 0 / 0 |
| `int_max` | 200 / 200 | 59 | 0.970 | 63 | 40 | 0 / 0 |
| `int_min` | 200 / 200 | 59 | 0.970 | 63 | 40 | 0 / 0 |
| `int_morphceil` | 200 / 200 | 59 | 0.970 | 63 | 40 | 0 / 0 |
| `int_mul` | 200 / 200 | 59 | 0.974 | 63 | 40 | 0 / 0 |
| `int_norm2` | 200 / 200 | 59 | 0.972 | 63 | 40 | 0 / 0 |
| `int_ofnat` | 200 / 200 | 59 | 0.945 | 63 | 40 | 0 / 0 |
| `int_round` | 200 / 200 | 59 | 0.951 | 63 | 40 | 0 / 0 |
| `int_round32` | 200 / 200 | 59 | 0.945 | 63 | 40 | 0 / 0 |
| `int_scale16` | 200 / 200 | 59 | 0.974 | 63 | 40 | 0 / 0 |
| `mon_contfindgt3` | 200 / 200 | 59 | 0.873 | 40 | - | 0 / - |
| `mon_countabovere` | 200 / 200 | 59 | 0.889 | 40 | - | 0 / - |
| `mon_countgt3` | 200 / 200 | 59 | 0.873 | 40 | - | 0 / - |
| `mon_countgt3exc` | 200 / 200 | 59 | 0.911 | 40 | - | 0 / - |
| `mon_countnotgt3` | 200 / 200 | 59 | 0.873 | 40 | - | 0 / - |
| `mon_countzerose` | 200 / 200 | 59 | 0.889 | 40 | - | 0 / - |
| `mon_desfindgt3` | 200 / 200 | 59 | 0.873 | 40 | - | 0 / - |
| `mon_firstbige` | 200 / 200 | 59 | 0.873 | 40 | - | 0 / - |
| `mon_loopcountsp` | 200 / 200 | 59 | 0.873 | 40 | - | 0 / - |
| `mon_loopfindgt3` | 200 / 200 | 59 | 0.873 | 40 | - | 0 / - |
| `mon_maxste` | 200 / 200 | 59 | 0.873 | 40 | - | 0 / - |
| `mon_sixe` | 200 / 200 | 59 | 0.533 | 40 | - | 0 / - |
| `mon_splite` | 200 / 200 | 59 | 0.901 | 40 | - | 0 / - |
| `mon_sumnze` | 200 / 200 | 59 | 0.889 | 40 | - | 0 / - |
| `mon_threee` | 200 / 200 | 59 | 0.533 | 40 | - | 0 / - |
| `mon_trysube` | 200 / 200 | 59 | 0.774 | 40 | - | 0 / - |
| `mon_twoe` | 200 / 200 | 59 | 0.533 | 40 | - | 0 / - |
| `st_canvash` | 200 / 200 | 59 | 0.873 | 40 | - | 0 / - |
| `st_compoundvalid` | 200 / 200 | 59 | 0.821 | 40 | - | 0 / - |
| `st_hdr` | 200 / 200 | 59 | 0.956 | 40 | - | 0 / - |
| `st_interlace` | 200 / 200 | 59 | 0.821 | 40 | - | 0 / - |
| `st_isignorable` | 200 / 200 | 59 | 0.920 | 40 | - | 0 / - |
| `st_lignumcomps` | 200 / 200 | 59 | 0.901 | 40 | - | 0 / - |
| `st_rgba` | 200 / 200 | 59 | 0.932 | 40 | - | 0 / - |
| `st_rgbag` | 200 / 200 | 59 | 0.821 | 40 | - | 0 / - |
| `st_rgbahdr` | 200 / 200 | 59 | 0.973 | 40 | - | 0 / - |
| `st_setlig` | 200 / 200 | 59 | 0.969 | 40 | - | 0 / - |
| `wa_entryat` | 200 / 200 | 8 | 0.997 | 63 | 40 | 0 / 0 |
| `wa_int_fxrounds` | 200 / 200 | 59 | - | 63 | 40 | 28 / 12 |
| `wa_int_icmp` | 200 / 200 | 59 | - | 63 | 40 | 73 / 57 |
| `wa_int_iops` | 200 / 200 | 59 | - | 63 | 40 | 70 / 66 |
| `wa_int_sumdev` | 200 / 200 | 59 | 0.901 | 63 | 40 | 0 / 0 |
| `wa_lenat` | 200 / 200 | 8 | 0.997 | 63 | 40 | 0 / 0 |
| `wa_mixhash` | 200 / 200 | 16 | 0.889 | 63 | 40 | 0 / 0 |
| `wa_symat` | 200 / 200 | 8 | 0.997 | 63 | 40 | 0 / 0 |

Every entry passed on every run. Entries marked with a `PANIC` count: Lean's `xs.data[i]!` panicked on the inputs listed (the reference returns the default value; the compiled code returns the same default, which is what the committed `.cases` contain, e.g. the empty input). The seed 21 and 22 runs of `wa_int_iops`, `wa_int_icmp`, `wa_int_fxrounds` were made before the counter was fixed, so their panic count is not recorded (`results/wa_int_rerun.txt`).

## Observations (not failures)
- **`wa_int_*` read past short inputs.** The four `WaInt` entries index the input without zero-extension, unlike the `Int` entries. On short inputs the Lean reference
  panics and returns the default; the compiled code matches it (committed cases include the empty input). Not a mismatch, but the function is only defined by its default on short inputs.
- **Largest slack**: `int_*` and `st_*` use 0.82–0.97 of their work block; `mon_sixe`, `mon_threee`, `mon_twoe` use 0.53 (the bound is a flat frame). `wa_entryat/lenat/symat` use 0.997 (the bound is exact).
  A block 8 bytes smaller fails the `gp/sp` check for `wa_entryat` (`SHORT=8`, see below); the scalar bounds were not tested this way.
- **Harness history**: the first `big` run of `mon_*` / `st_*` failed inside the Lean reference (non-tail-recursive hex decoding of 200 kB inputs). Fixed: tail-recursive decoding and
  `ulimit -s unlimited`; the 27 entries were rerun (`results/big_mon_st.txt`).

## Sanity checks of the harness
- `CORRUPT=1` (one expected byte changed): `int_abs` fails with an OUTPUT mismatch (as required).
- `SHORT=8` (work block 8 bytes below the bound): `wa_entryat` fails the `gp/sp` check (as required).
- `xcheck10.py` on all 55 entries: 0 mismatches.

## Reproduce
- Lean 4.29.0 in `/tmp/leandl/x/*/bin` (the path `fuzz6.py` uses), `qemu-system-riscv64`, `riscv64-linux-gnu-gcc`, Sail at `/home/user/deps/sailsim/...`, the build cache restored as in `origin/build-cache:README.md`.
- `python3 Testing/asm/fuzz10/xcheck10.py $(cat Testing/asm/fuzz10/ALL.txt)`
- `bash Testing/asm/fuzz10/runall10.sh seed21` (also `seed22`, `big` with `BIG=1`, `sail` with `SAILMAX`); one entry:
  `python3 Testing/asm/fuzz10/fuzz10.py FN SEED N qemu|sail [big]`; `CORRUPT=1` / `SHORT=k` for the sanity checks.
- `python3 Testing/asm/fuzz10/summarize10.py` rebuilds the table from `results/*.txt`.

## Not done / limits
- §28 `name_*`, `level_*`, harvest `conleche_*`, `expr_*`, `s3_*`, `BookS1` (see top). Their inputs are Lean `Name` / `Level` / `Expr` encodings and need decoders in `ref10.lean`.
- Sail only on inputs ≤ 1500 B and 40 cases per entry; QEMU runs use the committed work bounds, not the shrunk blocks of FUZZ6 (no shrink pass here).
- The `.words` files were not regenerated; the committed words are tested as they are. No compiler source was changed.
