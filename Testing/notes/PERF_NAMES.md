# PERF_NAMES: compile time linear in the number of defs (branch `perf-names`)

## Diagnosis (B1 = main 935c0ac1, profile of BENCH.md "Follow-up 1")
- `cg_map.lean` misaligned past index 56 because `self_S_ast.bin` was stale. It had 192 defs; C has 234. The fix was to
  regenerate it with `B1 own < self_S_input.txt`. After that all 234 entries land on a prologue. The K^2 entries are:
  - 8055 = `v85`: compares two spellings.
  - 14382 = `v8`: def lookup. It scans every def row from the newest and calls `v85` on each row.
  - 6049–6377 = `d1`…`d11`: the layout constants. Each is compiled as a call, so `d11 = d9 + d10` costs 11 calls.
- Phase: the parser `Par1`. `v8` runs at every def registration (duplicate check in `v127`), at every identifier in an
  expression (`v104`, after the local lookup `v7`) and at every call head (`v126`). For flat_K this gives about 1.5·K^2
  `v85` calls. Each one reads tokens through `bget h (d11 + …)`, so it pays the 11-call constant cascade on every read.

## Change (Par1, +35 −18 lines)
- `v84 n h a s`: hash of the spelling at token position `a` (pairs `(1, b)` until 0). It computes `s := s*33 + b`; the
  bucket is `& 1023`.
- Buckets: 1024 words at `[d9 + d10, d11)`, a new layout region placed before the tokens. A bucket holds its newest row
  (1-based), and slot 7 of each def row (unused before) holds the next older row of the same bucket.
- `v127` (opening a def): after writing slot 0 it sets slot 7 := the bucket head, then the bucket := the new row.
- `v8 h j x = v83 16777216 h j x head`. `v83` walks the chain, skips rows above `j`, compares with `v85`, and sets h[22]
  to the match or 0. Same result as the old scan.
- `gen_layout.py` writes the bases as numerals, so a base costs one call instead of up to 11.
- Not changed: the 512-def cap (def ids 512 + j, rows sized for 512). K = 511 compiles; K = 512 is still rejected
  silently with status 1.

## Proof
- `Proof/Parser/ParInvHash.lean`:
  - `hashL`/`bkt` (v84's value), `topR` (the newest row below m with a property).
  - `HashRep h names`: each bucket cell = `topR (bucket = b) n`, and slot 7 of row i = `topR (same bucket) i`.
  - `v83_walk`: induction on the chain. Rows outside the chain have another bucket, so they cannot match. This gives
    `v8_lookup`, whose conclusion is the old one (`Same 22`, h[22] = `idxOf`).
  - `hashRep_frame`, `hashRep_nil`, `hashRep_snoc` (registration), `hash_ok` (from `DefsRep` to the hypotheses of
    `v8_lookup`).
- `DefsRep` gains `HashRep h ((if inDef then rows st else st.defs).map name)`, which is established or transported in:
  - `rep_init` (zero heap);
  - `rep_open` (registration, `openW` now writes slot 7 and the bucket);
  - `rep_cur` / `asg` (current-row updates keep the name);
  - `defsRep_close`;
  - `defs_frameN` / `defs_frameP` (`defs_frameN` takes the bucket agreement `eb`).
- Layout literal 184384 → 185408 where it means the token base (`d11v`, `OutRep`, `TokAgreeN`, init, top). The frame
  bound `drop 184384` / `TokAgree` (≥ 184384) is kept: it covers buckets and tokens. Registration is the only step that
  writes a bucket, and it uses `drop 185408` (`drop_openW`, `out_frameT`).
- `Cert/` and `SrcLink/` are regenerated. `Tests/SelfInPath.lean` def ids ≥ 61 are shifted by 2 (`v84` and `v83` are
  inserted before `v8`).

## Numbers (exact RISC-V instructions, `run/nanorun.c`; old = B1's B2, new = this branch's B2)

| program | compile old | compile new | Δ | emitted code |
|---|---:|---:|---:|---|
| self-compile | 1,454,349,112 | 641,996,759 | −55.9% | (C itself changed) |
| count | 5,623,980 | 5,625,417 | +0.03% | identical |
| fib | 7,363,302 | 7,016,214 | −4.7% | identical |
| hex | 7,482,090 | 7,136,884 | −4.6% | identical |
| maxbyte | 6,855,630 | 6,611,231 | −3.6% | identical |
| reverse | 6,508,446 | 6,335,825 | −2.7% | identical |
| rle | 8,267,595 | 7,770,887 | −6.0% | identical |
| sum | 6,456,967 | 6,290,437 | −2.6% | identical |
| upper | 6,993,914 | 6,735,760 | −3.7% | identical |

The run costs of the 8 examples are unchanged on 10 B / 1 KiB / 100 KiB / 1 MiB, because the emitted code is identical.

| K | flat old | flat new | chain old | chain new | expr old | expr new |
|---:|---:|---:|---:|---:|---:|---:|
| 10 | 10,671,943 | 9,531,918 | 8,814,342 | 8,038,811 | 6,738,649 | 6,574,199 |
| 20 | 16,861,498 | 13,543,538 | 12,634,253 | 10,459,361 | 7,939,659 | 7,597,509 |
| 40 | 31,829,308 | 21,566,778 | 21,849,975 | 15,300,461 | 10,341,679 | 9,644,129 |
| 80 | 72,119,728 | 37,613,258 | 46,585,019 | 24,982,661 | 15,145,719 | 13,737,369 |
| 160 | 201,564,928 | 69,885,018 | 125,203,318 | 44,525,861 | 24,753,799 | 21,923,849 |
| 320 | 641,852,048 | 134,725,538 | 391,281,136 | 83,802,201 | 43,969,959 | 38,296,809 |

- The new flat increments per doubling are 4.0, 8.0, 16.0, 32.3, 64.8 M, i.e. 0.40 M per def at every K.
- flat_400 = 167.2 M and flat_511 = 212.4 M: still 0.41 M per def up to the cap.
- The emitted code is byte-identical to B1's for all 18 synthetic programs.
- Reproduce: `nanorun OLD_B2 prog prog_old.bin` and `nanorun B2.bin prog prog_new.bin`, with the generators
  `bench/make_inputs.py` and `bench/synth_scaling.py` (on main).
