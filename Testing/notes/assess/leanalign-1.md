# Lean Align — part 1 of 2 (assess-08)

Clone: `rowancallahan/lean-align` (depth 1) worked. Not built. Counts are `grep` over `git ls-files '*.lean' | LC_ALL=C sort`; the regex counts are approximate.

## Slice
306 .lean files, 102,636 lines. Half = 51,318. Part 1 = first 134 files (cumulative 51,027), `Aligner/LeanAlign.lean` … `Aligner/mapper/PairHits.lean`. Part 2 starts at `Aligner/mapper/PairHitsKP.lean`.
Part 1 = `Aligner/{LeanAlign,PairwiseMain,index,io,kernels}` in full + `Aligner/mapper/{BandCellsJProof … PairHits}`. Part 2 = rest of `Aligner/mapper`, `mapper/lemmas`, `Aligner/trimmer`, `Main.lean`, `Proofs/`, `Spec/`, `Testing/`, `lakefile.lean`. (Note: the actually-run `Main`, `Proofs/`, `Spec/` are all in part 2.)

## Program overview (whole repo)
1. Paired-end short-read aligner (BWA-like), with a machine-checked proof that every answer is correct against `Spec/`.
2. Entry: `Main.lean:21` `main (args : List String) : IO UInt32`, only file touching the file system. `lake` exe imports `Proofs.MapFiles` (`Main.lean:2`), NOT `Aligner/LeanAlign/*` (those 4 files, 163 lines, are an old toy CLI, not on the main path).
3. Input: `build GENOME.fa INDEX` or `map INDEX R1.fq R2.fq OUT.sam MIN MAX` (`Main.lean:39,52`). FASTA/FASTQ read in 8 MiB chunks (`Main.lean:9`).
4. Output: SAM text (header from `SamSpec.header`, then lines), written via `out.write`; index is a multi-GB ByteArray on disk.
5. Top theorems: `Spec.alignPairs_correct` (`Spec/Aligner.lean:219`), `alignPairs_end_to_end` (`:236`), `process_correct` (`Spec/MapFiles.lean:84`). Real data target: hg38-scale genomes (README/AGENT_OVERVIEW; "multi-GB index").

## 1. Size (part 1)
| dir | files | lines | defs | theorems/lemmas |
|---|---|---|---|---|
| Aligner/LeanAlign | 4 | 163 | 12 | 0 |
| Aligner/index | 16 | 9,642 | 344 | 505 |
| Aligner/io | 1 | 541 | 23 | 20 |
| Aligner/kernels | 74 | 25,581 | 575 | 1,072 |
| Aligner/mapper (to PairHits) | 38 | 15,069 | 337 | 584 |
| Aligner/PairwiseMain | 1 | 31 | – | – |
| **total** | 134 | 51,027 | ≈1,293 | ≈2,181 |

So ~2/3 of the text is proof. Code part: ≈1,300 defs in part 1 alone; whole repo likely ≈2,500 (uncertain). Largest files: `kernels/wfa/AlignmentWfa.lean` 5131 lines, `index/minimizer/MzBuildOk` 1646, `MzIndex` 1415, `MzWord` 1363, `AlignmentWavefront` 1278.

## 2. Features used (part 1) and 3. needed vs incidental
| feature | count / example | needed? | cheapest encoding |
|---|---|---|---|
| Nat (unbounded) | ~6,800 mentions; positions, lengths, scores (`CsrIndex.lean:93-99`, `FastGenPair.lean:56`) | indices/lengths are ≤2^32 in practice; proofs carry bounds (`hk : k.toNat < 2^30`, `MapperPGen.lean`) | UInt64 + asserts. Many kernels already have a USize/UInt32 twin (`ldwU_eq`, `u32W_eq`, `exFind_eq_exFindF`). |
| Int | ~1,470; scores/diagonals (`Spec/Alignment`, `dst R.size D sh : Int`, `PairHits.lean:35`) | needed (negative diagonals/penalties) | UInt64 biased offset, or two's complement with explicit signed compare/arith. |
| UInt64/32/8/USize | 987/930/140/665 | core, executable kernels | direct (UInt32/UInt8 need mask/trunc ops: check subset). |
| ByteArray | ~1,500; genome, reads, index, buckets | core | one Buf of bytes (or packed 8 bytes/word); `getU32`/`u32` LE helpers are plain shifts+ors. `ByteArray ++`, `extract` need loops. |
| Array / Array (Array Nat) | ~2,800; `Array (List (Array Nat))` in `FastGenPair.lean:68` | needed; nested arrays + lists in mapper | flatten into Bufs + offset tables. |
| List | ~3,400, mostly in specs/proofs (`List Char`), but also executable (`flatMap`/`filterMap` in `hitsC`, `PairHits.lean:30-41`) | spec-only in kernels; executable in mapper hit lists | linked lists = Buf-backed cons cells (tagged nodes) or arrays + counters. |
| Char | spec-only (`xs ys : List Char`); executable kernels take `Array Char`/ByteArray | spec-only | drop (bytes) |
| Option | ~790, `decodeP : … → Option (Placement × Int)` (`FastGenPair.lean:129`) | needed | `(flag,value)` pair / sentinel word. |
| structure | 50 (`CsrIndex`, `PGen`, `GS`, `GW` with 16 UInt64 fields `FastGenWordFilt.lean:44`, `Best`, `Seed`) | needed | tuples / Buf records. Many are `Prop` structures (proof only). |
| inductive | 0 in part 1 (no user ADTs; only structures) | – | – good |
| structural/fuel recursion | many `| 0, … | f+1, …` fuel recursions (`CsrIndex.lean:103`, `MapperPGen.lean:~45 exFind`, `loadW FastGenWordFilt.lean`) | needed | direct match with `loop n`. |
| well-founded recursion | 96 `termination_by` (`stop - i` loops: `MapperMzWords.lean:88,117,176,…`, `MapperFastIndex.lean:568`) | needed (counting loops) | fuel loop with fuel = `stop - i`. |
| `for … in [0:n]`, `let mut`, `Id.run do` | 14 / 44 / 15 (`CsrIndex.lean:88,137,171,179`; `MzIndex.lean:415`) | incidental | desugars to `loop`. Needs a `do`-lite front end or manual rewrite. |
| partial / unsafe / extern / implemented_by / native_decide | 0 (repo rule, audited `Testing/checks/AuditAlignPairs.lean`) | – | good: no escape hatches. `decide +kernel` 4. |
| String | 26, only `LeanAlign/*` (dead toy CLI) | incidental | skip those files. |
| Float / HashMap / RBMap | 0 / 0 | – | good |
| Except | 8, `LeanAlign/*` only | incidental | skip |
| IO / monads | 10 `IO`; `do` 54; no StateM in part 1 | only `Main.lean` + io; kernels pure | byte-in/byte-out wrapper exists in our subset |
| typeclasses | 12 instances, 1 class: `GRead`, `LookG` (`FastGenPair.lean:74,84`), `GPk` (`FastGenWordFilt.lean:28`), `Inhabited` | needed for the mapper's generic code (`{Gt} [GRead Gt] [LookG L Pp]`) | monomorphise by hand: a few concrete instances (ByteArray vs PGen genome; Mz vs Csr index). Without specialisation, ~2x-4x def blow-up in the mapper. |
| `Task.spawn` | 11 (`MzView.lean:83,360`; `WgPacked.lean:36`; `MzCheckPar.lean:55,91`; `FastMapperPar.lean`) | incidental (speed; semantics `(Task.spawn f).get = f ()`) | replace by sequential call. |
| macros | 1: `macro "u32" : tactic` (`BandCellsJProof.lean:48`) | proof-only | erased |
| imports | no Mathlib, no Std; 4 `import Lean`-like (tactic/Std.Legacy.Range only in proofs `MzBuildOk.lean:109`) | – | good: core only |
| `@[csimp]` | 57 (fast def ≡ spec def, e.g. `exFind_eq_exFindF`) | the compiled form is the fast one | we compile the fast def; the spec def is irrelevant at runtime |
| `@[inline]/@[specialize]` | 429 | optimisation | ignore |
| `a[i]!` / `get!` / `uget` | ~940 / ~995 | core | bget with assert (matches our fail-fast policy) |
| `sorry` | 0 real (only comments "never sorryAx") | – | |

## 4. Hard blockers (ranked)
1. **Scale**: ≈1,300 defs in part 1 alone (≈2,500 est. whole) vs the 511 cap; also the 16,384 parser-node cap. Even the *executable-only* closure (without proof/spec defs and without 3-4 alternative kernel generations: `wfa`, `wfa_offsets`, `wfa_u32/*`, `k250`, `mapper_band`…) is likely several hundred defs. Fix: compile only the dependency closure of `Total.process`; measure that first (uncertain until built).
2. **Multi-GB data**: index is read as one ByteArray (`Main.lean:34`), genomes hg38-sized; work memory 1 GiB, input ≤1 MiB. Only a toy genome (chr21 ~46 MB packed, or a synthetic few-MB one) is feasible. Streaming FASTQ with an 8 MiB chunk (`Main.lean:9`) also exceeds the 1 MiB input.
3. **Typeclass-generic code** (`GRead`, `LookG`, `GPk`, `Inhabited`, `[specialize]`) and `deriving Inhabited` across the mapper: needs manual monomorphisation or class support.
4. **Nested containers**: `Array (List (Array Nat))`, `Array ByteArray`, `Option (Placement × Int)`, `List (Window × Nat)`: need Buf-of-Bufs / flattening, i.e. a data-layout redesign of the mapper (big).
5. **Frame size ≤250 words**: `GW` has 16 UInt64 fields + array; the K250 kernels pass many scalars; likely over the limit in places (uncertain).
6. **Int arithmetic** and `UInt32`/`UInt8` ops: depend on what the subset provides.
7. `Task.spawn`, `IO` file handles: replaceable, low.
Not a blocker: no user inductives, strings (outside toy CLI), Float, HashMap, partial/unsafe.

## 5. Runtime needs
Real run: GB-scale genome + index, millions of reads (README speed ≈2× minibwa). Index building (`buildIndex`, minimizer sort, `MzIndex`/`CsrIndex`) is heavy compute: O(genome) with sorts. Toy run: a 100 kb–5 MB genome and ≤10⁵ reads would fit 1 GiB. Output SAM ≈ hundreds of bytes/read.

## 6. Easy wins (close to the subset)
- `Aligner/index/csr/CsrIndex.lean` (350 lines): `getU32` bucket offsets over ByteArray, fuel binary search `locateAux` (`:103`), `lookup` (`:128`); only `structure` + `for _ in [0:64]`.
- `Aligner/index/minimizer/MapperMzWords.lean` (334): word codes, `termination_by stop - i` loops over bytes → fuel loops; UInt64 hashing.
- `Aligner/index/packed_genome/MapperPGen.lean` `exFind`/`u32`/`letter` (`:42-58`): machine-word binary search, LE u32 reads, 2-bit decode via shifts.
- `Aligner/kernels/gapless/MapperGapless.lean`, `MapperOneIndel.lean`, `kernels/mapper_band/BandScore,MapperBandKernel,MapperBandBytes`: banded/gapless Hamming/indel scoring on ByteArray with small Nat scalars: good first compile targets with a test that compares to a reference.
- `kernels/wfa_u32/*` (UInt32 wavefront; arrays of UInt32, scalar loops; large but shaped like the subset) — the `Fill`/`Step`/`Level` loops, but check structures `ULevel`/`BLevel` (arrays inside structs).
- Any one kernel + a tiny main (two byte strings in → score out) makes an end-to-end demo that does not need the 511-def budget (a few dozen defs).

## 7. Proof angle
Heavy and valuable, but tied to Lean's kernel semantics of the *source*, not our compiled code: ≈2,180 theorems in part 1. Pattern: slow spec def + fast def + equality theorem + `@[csimp]`. Key theorems (part 1):
- `wfaAlign_sound` (`kernels/wfa/AlignmentWfa.lean:3527`), `wfaRun_sound` (`:3488`), `wfaLoop_sound` (`:3452`), `wfaAlignU_sound` (`wfa_u32/AlignmentWfaU32.lean:162`), `wfaAlignU2_sound` (`…Kernel2.lean:294`), `wfaAlignU3_sound` (`WfaU3.lean:55`), `checkRuns_sound` (`wfa_runs/AlignmentCigarCheck.lean:126`).
- `hitsC_sound` (`mapper/PairHits.lean:46`), `pairGF_sound` (`PairGuarFast.lean:600`), `pairGQC_sound` (`PairGuarQE.lean:426`), `scanLookup_sound` (`FastGenCover.lean:19`).
- Index: `advance_spec` (`MzBuildOk.lean:1487`), `mem_lookup` (CsrIndex).
- Whole: `Spec.alignPairs_correct`, `alignPairs_end_to_end`, `process_correct` (axioms: propext, Classical.choice, Quot.sound only; five external checkers accepted per AGENT_OVERVIEW).
Inheritance: only if our compiler's semantics-preservation theorem applies to Lean-source defs that we translate 1:1 (same terms in the subset). Rewriting Nat→UInt64 etc. means a *new* equality proof per rewritten def (they already do this: `ldwU_eq`, `u32W_eq`, `exFind_eq_exFindF`, each with a range hypothesis like `hk : k.toNat < 2^30`; these can be reused to justify the encodings). Theorems about `Nat`/`List Char` specs do not transfer automatically to our bounded-UInt64 code.

## Caveats
- Part 1/2 boundary derived from C-locale sort; confirm part 2 begins at `PairHitsKP`.
- Counts are regex-based (e.g. `Char`/`List`/`Nat` include proof text); def/theorem totals ±5%.
- Whole-repo def count and executable-closure size are estimates, not measured. No build was run.
