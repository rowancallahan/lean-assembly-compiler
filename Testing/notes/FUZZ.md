# Fuzz notes

## Setup (Task 1)
`Testing/setup/box.sh` (plus `lake build Arm.CompilerArm Compiler.Front.Reify`, ~6 min, peak memory fine with 12G swap) works as written.
No blocked host: GitHub release downloads (Lean 4.29.0, elan, sail-riscv 0.9) all worked through the proxy; `releases.lean-lang.org` was not used.
Note `Arm.CompilerArm` does not import `Compiler.Front.Reify`, but `Testing/asm/triple-data/triple.lean` does, hence the second build target.
Verified: `lake env lean Testing/asm/triple-data/triple.lean > /tmp/t.txt && python3 Testing/asm/triple.py /tmp/t.txt` prints agreement for all 4 cases
(one_plus_one 1, n_plus_n 100, n_plus_m 10000, demo 300 inputs), 4.4 s.
`Testing/asm/triple.py` changes: `SAIL` env var (same default path), optional `exp` line per case echoed in mismatch assertion.

## Fuzzing (Task 2)
`Testing/asm/fuzz.lean`: `SEED=s NCASES=n K=k lake env lean Testing/asm/fuzz.lean > out.txt` (the Sail model defines a root `main`, so `lean --run` is unusable; it uses `#eval` + env vars).
splitmix64 PRNG, reproducible by seed. Constructors covered: `var`, `const`, `bin` with all 5 `Op`s (add sub and or xor); the generator
must be extended by hand in `genExp` when `Exp` grows. Constants/inputs: 1/3 from an edge list (0,1,2,3,2^63,2^63-1,2^64-1,2^64-2,2^32,...), else uniform 64-bit.
Terms are rejection-sampled for `depth < 5` (and `assert!`ed). RV64 code length per term: 3..509 words (median 9).

Results (Exp as of main 42a74eb):
| seed | cases x inputs | pairs | mismatches | wall |
|---|---|---|---|---|
| 1 | 100 x 100 | 10,000 | 0 | 34 s check + 4.7 s gen |
| 2 | 400 x 250 | 100,000 | 0 | 272 s check + gen ~15 s |

Throughput ~370 pairs/s end to end (checker), 1 core used (sequential). Time split on 40 cases / 10,000 pairs (33.8 s):
Sail C emulator run 25.2 s (74%, instruction-limited trace-mem run), Sail log parse 1.6 s, QEMU RV64 2.7 s, QEMU ARM 2.9 s, both gcc 1.5 s.
Generation (Lean, interpreted): 4.7 s for 10,000 pairs, mostly import/startup. Easy speedups: run cases in parallel (4 cores here), drop `--trace-mem` text parsing.

No mismatches found; nothing to minimise.

## Round 2: main 898126f (shifts, ult/slt/eq, ite; depth < 11)
`genExp` now covers `var`, `const`, `bin` with all 11 ops, and `ite`. Edge constants additionally include 63, 64, 65, 127, 128, 31, 32;
1 in 12 nodes is a shift whose right operand is a constant from {0,1,63,64,65,127,2^64-1,32}; `ite` conditions are biased to
const 0, const 1..3, an ult/slt/eq comparison, or an arbitrary term. Depth limit `< 11`, rejection-sampled and `assert!`ed.
Code length per term: 3..4571 RV64 words (median ~185); 700 of 1,200 terms contain `ite`, each op appears in 550-610.

Checker changes: `Testing/asm/fuzzpar.py cases.txt [J]` splits cases round-robin over J (default: all cores) parallel `triple.py` runs, each with its
own `WORK` dir (new env var of `triple.py`). `triple.py` linker script moved `.tohost`/`.data` to 0x80100000/0x80200000: the old 0x80001000
overlapped the code once a term exceeded ~1000 RV64 words (gcc link error, not a compiler bug).

| seed | cases x inputs | pairs | mismatches | gen | check (4 procs) |
|---|---|---|---|---|---|
| 21 | 300 x 100 | 30,000 | 0 | 34 s | 71 s |
| 22 | 300 x 100 | 30,000 | 0 | 36 s | 88 s |
| 23 | 300 x 100 | 30,000 | 0 | 36 s | 75 s |
| 24 | 300 x 100 | 30,000 | 0 | 38 s | 78 s |

Total 120,000 pairs / 1,200 cases, 0 mismatches. Checker ~390 pairs/s with 4 procs (long terms dominate: Sail emulator
time scales with instructions executed); generation ~850 pairs/s (interpreted Lean, now the larger share per pair than before).
Reproduce: `SEED=21 NCASES=300 K=100 lake env lean Testing/asm/fuzz.lean > x.txt && python3 Testing/asm/fuzzpar.py x.txt 4`.
