# Fuzz notes

## Setup (Task 1)
`setup/box.sh` (plus `lake build Proven.CompilerArm Proven.Reify`, ~6 min, peak memory fine with 12G swap) works as written.
No blocked host: GitHub release downloads (Lean 4.29.0, elan, sail-riscv 0.9) all worked through the proxy; `releases.lean-lang.org` was not used.
Note `Proven.CompilerArm` does not import `Proven.Reify`, but `asm/triple-data/triple.lean` does, hence the second build target.
Verified: `lake env lean asm/triple-data/triple.lean > /tmp/t.txt && python3 asm/triple.py /tmp/t.txt` prints agreement for all 4 cases
(one_plus_one 1, n_plus_n 100, n_plus_m 10000, demo 300 inputs), 4.4 s.
`asm/triple.py` changes: `SAIL` env var (same default path), optional `exp` line per case echoed in mismatch assertion.

## Fuzzing (Task 2)
`asm/fuzz.lean`: `SEED=s NCASES=n K=k lake env lean asm/fuzz.lean > out.txt` (the Sail model defines a root `main`, so `lean --run` is unusable; it uses `#eval` + env vars).
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
