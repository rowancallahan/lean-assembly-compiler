# Whole-program differential fuzzer for B2 (nano)

Unproven glue, like `examples/run_examples.sh`. Not part of the correctness theorem.

## Files

- `nanogen.py SEED N DIR`: random programs in the accepted subset (valid-biased).
- `nanofuzz.py SEED N WORKDIR [MUT=0.5] [INPUTS=4] [SHRINK=1]`: generates, mutates (half of the programs), compiles
  with `B2.bin` under `nanorun`, runs on random inputs, and compares with the reference.
- `semrun_batch.lean`: `semrun.lean` for a manifest of many runs in one Lean process (same pipeline:
  `lexAll → refParse → C.o41 → Sem κC`).
- `results/summary_*.txt`: the summaries of the runs reported below.

Run (Lean 4.29.0 on PATH, `lake build Nano.V2Self.Proof.Main.Sem` done, `../deps/sail-riscv-lean` at opencompl/sail-riscv-lean 51c635c):

```
python3 Testing/nano/v2self/fuzz/nanofuzz.py 2 400 /tmp/work
```

## What is compared

- B2 rejects (empty code) ⇒ the reference must reject too (`REJ …`). Otherwise: `GAP` (completeness, not soundness).
- B2 accepts ⇒ the reference must accept, and on every input: `OK` ⇒ B2 status ok and identical bytes; `STOP` ⇒ B2
  must not produce output. Anything else is an `ALARM`, and the failing program is minimized line by line (`SHRINK=1`).
- `lean` on Prelude + program is recorded but not used as a verdict: nano types numerals as `UInt64`, Lean as `Nat`,
  so some accepted programs are not Lean-valid (e.g. `35 <<< 51`).
- Out of work memory at the default 80 MiB (`-1`) is retried with 1 GiB; it counts as a resource limit when the output
  then equals the reference, and as an `ALARM` otherwise.

## Results

Base `origin/nano-v2-src` 79aa662 (seeds 1–6, B2 sha256 `bb5558a5…`): 2240 programs, 4 inputs each, 0 alarms, 0 gaps.
Base e60e0ce (seeds 7–8, the branch tip when this was pushed; B2 unchanged): 1000 programs, 0 alarms, 0 gaps.
Reference: `semrun_batch.lean` imports `Nano.V2Self.Proof.Main.Sem` (as `semrun.lean` now does).

| outcome (seeds 1–6, 2240 programs) | programs |
|---|---|
| B2 rejects, reference rejects (`lean` fails) | 891 |
| B2 rejects, reference rejects (`lean` ok, outside the subset) | 332 |
| B2 accepts, outputs equal on all inputs | 727 |
| B2 accepts, out of work memory at 80 MiB on some input, equal output at 1 GiB | 290 |

Seeds 7–8 (1000 programs): reject, lean fails 409; reject, lean ok 134; accept and equal 306; accept, oom at 80 MiB then equal 151. Per seed in `results/summary_tip7.txt`, `summary_tip8.txt`.

Notes:
- The out-of-memory cases are a resource limit, not wrong answers. For three of them, 200 MiB of work memory was
  enough; the other cases were not measured.
- Documentation mismatches (both B2 and the reference reject, so no soundness issue): `examples/README.md` lists `^^^`
  and fuel `len' x + k` / `len' x * k` as accepted. Both are rejected (`^^^` by the lexer). Also a bare accumulator in
  a self call (`f n x (i + 1) o`) is rejected by the ownership stage, which the README does not mention.
- Some constructs are rejected by both sides and are not in the generator: a parenthesized condition
  `if (a == 1) then`, the input `x` as a list value (`put x 1`, `x`), a branch without a self call.
- Mid-run, the checkout of a different local branch changed `B2`'s source tree under a running fuzz job; those
  results were discarded and the seeds rerun. Only the reruns are in `results/`.

## Reuse for ARM

The generator and driver only call `nanorun`-style executables: `B2` and the run step are the two places to replace
with an ARM back end (`shim_arm` under qemu-aarch64) and the same reference.
