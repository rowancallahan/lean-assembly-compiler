# Lean Align assessment, part 2 of 2

Source: `rowancallahan/lean-align`, shallow clone, `main` as of 2026-11-20. Nothing built (needs Lean 4.35 + multi-GB genome data). Counts are regex counts (grep), so approximate.

## Slice definition
`git ls-files '*.lean' | LC_ALL=C sort` = 306 files, 102,636 lines; half = 51,318. The cut falls inside `Aligner/mapper/PairHitsKP.lean` (cum. 51,027 → 51,465). I put that straddling file in the SECOND half, so part 2 = `Aligner/mapper/PairHitsKP.lean` .. end (172 files, ~51.6k lines). **Part 1 should end at `PairHits.lean`**; if part 1 included PairHitsKP, overlap is one file.

Part 2 by group (lines / defs / theorems):
| Group | files | lines | defs | thms |
|---|---|---|---|---|
| Aligner/mapper/ (PairHitsKP…TierRouter, + lemmas/) | 52 | 21,971 | ~600 | ~809 |
| Proofs/ (Aligner, Report, Pack, Map*, Sam*, Fastq…, core/) | 52 | 13,674 | ~529 | ~606 |
| Testing/benches | 35 | 10,242 | ~586 | 2 |
| Spec/ | 8 | 982 | 105 | 10 (17 `sorry`: holes, by design) |
| Testing notes/checks/tests/unique | 12 | 1,903 | 75 | 91 |
| Main.lean + lakefile.lean | 2 | 366 | 5 | 0 |

## 1. What the program is
Paired-end short-read aligner (BWA-like), with a proof that every answer is correct against a small spec. Entry: `Main.lean:21` `main`:
- `lean-align build GENOME.fa INDEX` → `buildIndex` (FASTA → index bytes).
- `lean-align map INDEX R1.fq R2.fq OUT.sam MIN MAX` → reads the index as one `ByteArray` (`Main.lean:24-27`, multi-GB for hg38), streams FASTQ in 8 MiB chunks (`chunkSize`, `Main.lean:6`), runs `Spec.Total.process` (`Spec/MapFiles.lean`), writes SAM.
- Pipeline per pair: FASTQ parse → adapter/window trim → tier router (`TierRouter.lean`, tags T0…T3) → index lookup (minimizers / k-mer, packed 2-bit genome) → word-parallel / banded / WFA kernels → SAM text.
- Spec top level: `Spec/Aligner.lean:206-249` (`buildIndex`, `alignPairs` are `sorry` holes; `alignPairs_correct`, `alignPairs_end_to_end`).

The part-2 mapper files are the **search layer** (hit enumeration within caps, pair joining/guarantees, tier routing, parallel scheduling), not the DP kernels (those are in part 1: `Aligner/kernels/*`).

## 2. Lean features used (part 2)
Counts are line-matches over part-2 files. "mapper" = `Aligner/mapper/` slice, "proofs" = `Proofs/`.

| Feature | Count | Examples |
|---|---|---|
| def / theorem | ~1976 / ~1603 | proof-heavy: ~1 theorem per def (mapper 600/809) |
| inductive | 24 (mapper: 4) | `Mate`,`Reason` (`PairReason.lean:36,46`), `Out` (`PairRouter.lean:119`), `Tag` 9 constructors (`TierRouter.lean:349`) |
| structure | 85 (mapper: 19) | `TierOut` 10 fields (`TierRouter.lean:~365`), `TierCfg` with function-valued fields `gate/pref/ceil/heur/xe` |
| class / instance | 3 / 7 | `class Look` (`MapperFastAlgo.lean:712`), `LookG` (`MapperGenLook.lean:45`), `GRead`; used as `[LookG L Pp]` in `PairNear.lean:268`. Decidable instances in proofs |
| partial / unsafe / extern | 8 / 3 / 3 | all in `Testing/` (benches, audit tools). **None in Aligner/ or Proofs/**; repo rule forbids them |
| mutual | 0 | |
| Recursion | structural (default) + `termination_by` 126 (mapper 34) | loops are mostly `Nat`-indexed well-founded recursion or `for … in`/`while` (mapper 63 hits) inside `Id.run do` (21) |
| Nat | ~5100 | the default number type; Nat for all indices/offsets |
| Int | ~1260 (mapper 690) | scores ≤ 0, diagonals `D`, `dst R.size D sh`: signed arithmetic is core |
| UInt64 / USize / UInt32 / UInt8 | 558 / 333 / 297 / 524 | fast kernels use USize/UInt64 words; mapper has 92 UInt64, 146 USize |
| ByteArray | ~2444 (mapper 861) | reads, genome, index, packed words |
| Array | ~3500 (mapper 598) | `Array Nat` seed anchors, `Array PGen`, `Array ByteArray` |
| List | ~3750 (mapper 710) | `flatMap`, `filterMap`, `zipIdx`, `mergeSort`; list-valued hits (`List (Window × Nat)`) |
| Option | ~760 (mapper 290) | `Option Cand`, `Option (Placement × Int)` results |
| String | 440 (mapper 56) | `Tag.str`, tag suffixes (`sfx : String`), SAM text; mostly output formatting |
| Char | 476 | mostly in Proofs/Sam* / Fastq byte specs |
| HashMap | 29 (4 imports `Std.Data.HashMap`) | mostly benches; mapper 13 |
| Task / parallelism | 71 (mapper 102 hits incl. docs) | `ParMap.parMap`, `ParGroup.parMapBins`, `Task.spawn (prio := .dedicated)` (`ParMap.lean`, `ParGroup.lean:29-32`) |
| StateM / Except | 38 / 50 | only in proofs (`MapFiles.lean:76 StateM Files`) and IO in Main |
| IO | ~1350 | benches + Main + LeanAlign/Cli/Run; mapper core is pure |
| Float | 84 | benches only (timing) |
| macro/notation | 0 | |
| Higher-order / closures | 31 `Nat → Nat` args in mapper | `ladderUB (dc : Nat → Nat) … (hf : Bool → Nat → List …)` (`PairNear.lean:97`), config closures in `TierCfg` |
| Imports | `Std.Data.HashMap/HashSet`, `Lean` (2, tooling), no Mathlib | tactics: `simp/omega/decide` ~6250 hits |
| sorry / native_decide / axiom | Spec/ only (17 `sorry`, by design); `native_decide` only in `trimmer/ReadWindowProofAudit.lean` (part 1) | |

## 3. Needed vs incidental, cheapest encoding
- **Nat → UInt64** (needed, core). Genome offsets fit < 2^35 (hg38 ~3.1e9), so UInt64 is fine; need explicit overflow bounds. The code already carries many `< 2^63`/`Fits` side conditions (`Proofs/Aligner.lean:33 heavyTable_size`, `IndexFinal.lean:271 Fits g`), reusable as asserts.
- **Int** (needed). Encode as UInt64 two's complement with offset-biased compare, or store `score+bias` as UInt64. Scores are small (≥ -100 junk, caps ≤ ~16); diagonals ± read length. Medium effort: signed `/` and `min`, `toNat` on guarded values (`(dst …).toNat`).
- **List / flatMap / filterMap / mergeSort / zipIdx** (mostly incidental, but pervasive: list-valued hit sets). Rewrite as Buf accumulation + sort pass (insertion sort for small n, or radix on UInt64 key). Caps (`gaveUpRepeats = 200`, `Spec/Aligner.lean`) keep lists small. Real rewrite, but local.
- **ByteArray** → Buf of UInt64 (one byte per word or 8 packed). Cheap; 2-bit packed genome (`PGen`/`WgPacked`) wants UInt64 shifts, which are in the subset's scalar ops (uncertain: need confirm shifts/and/or exist).
- **Option** (needed for control flow): encode as (flag, value) pair, or sentinel `2^64-1`. Cheap.
- **inductive Tag/Mate/Reason/Out/Strand** (needed): enums → small UInt64 tags; payload variants (`Reason.noPartner m, k`) → tagged tuples. Cheap-medium.
- **structure TierOut/TierCfg** (needed): flatten to tuples or Buf fields; `TierCfg` function fields (`gate`, `pref`, `ceil`, `heur`, `xe`) are higher-order and cannot be passed: specialize with a fixed config (the production cfg is `TierHeur.rtxCfg` in part 1; heuristic is OFF in `alignPairs` per `AGENT_OVERVIEW.md`), so defunctionalize to constants.
- **Type classes `Look`/`LookG`/`GRead`** (incidental abstraction for proofs over index representations): monomorphize to the one used instance (`HIdx`/`PkMz`/`PGen`).
- **String** (incidental): `Tag.str`, `sfx`, SAM text → bytes in Buf.
- **Task/parallelism** (incidental to correctness; `Task.spawn`/`get` are pure `= fn ()`, so `parMap = Array.map` per `ParMap.lean` header): drop, run sequentially.
- **`termination_by` / `for`/`while` in `Id.run`** → fuel loop; the bound is usually the array size or a cap (needs per-loop fuel assert).
- **Float**: none outside benches.
- **Proof-side Prop/theorems** are erased and not compiled.

## 4. Hard blockers (ranked)
1. **Mapper is deeply abstract Lean**: structures with closures, type classes, polymorphic `{L Pp : Type}`, `Option`/`List`/`Array (Array Nat)` nested containers. The subset has no user data types at all; this layer needs a monomorphizing, defunctionalizing front end (or a manual rewrite of ~22k lines of mapper). Largest cost.
2. **Memory model**: index is a single multi-GB `ByteArray` (`Main.lean:25`); hg38 index ≫ the 1 GiB work memory limit. Only a toy genome (chr21 ~46M bases, 2-bit ≈ 12 MB + minimizer table) plausible, and then only with raised limits. Also 8 MiB FASTQ chunks vs 1 MiB input cap.
3. **Scale vs 511 defs / 16,384 nodes**: mapper alone ~600 defs, whole runtime stack several thousand (see §5). Even a "subset" mapper (no heuristics, one index kind) is > 511.
4. **Proof coupling**: the real correctness theorem (`alignPairs_correct`) is about the Lean-semantics `alignPairs` with Nat/Int/List; compiled nano code would only inherit it through a refinement proof (nano def ≡ original def) that does not exist and would be large (~13k lines of Proofs/ show how big the original is).
5. **Streaming/IO**: Main uses file handles, `rename`, `IO`; compiler offers byte in/out only. Trusted shell can stay outside.
6. Function-valued config (`TierCfg`) and `instance`/`class` dispatch (see §3): language-feature work if kept, rewrite if not.

## 5. Runtime needs
- Input: FASTQ pair files (GBs for real data; Testing has chr21 / hg38 / HG002 fetch scripts, `Testing/data/fetch.sh`) + a prebuilt index (up to multi-GB). 1 MiB input cap ⇒ only a micro test (tiny genome, few reads) fits. Output: SAM lines, ~300-500 B per pair.
- Memory: index loaded wholesale; mapper holds per-read `Array (Array Nat)` anchors, lists of hits (capped by `gaveUpRepeats = 200`).
- Defs: part 2 ≈ 1,976 defs total (≈ 600 in mapper, ≈ 530 in Proofs, ≈ 590 in benches); only the mapper ~600 + Aligner/index part-1 + kernels count toward a compiled program. Estimate whole runtime path ≈ 1,500-2,500 defs (uncertain), i.e. 3-5× the 511 cap. Node count 16,384 certainly exceeded (single file `TierRouter.lean` is 2,001 lines).
- Heavy compute: seed lookup, word-filter, banded/WFA DP over candidate windows, per-read; compute-bound, would need native-speed output.
- Frame ≤ 250 words: structures like `TierOut` (10 fields) and function args with 8-10 params (`hitsCKN` has 8) are close to the limit.

## 6. Easy wins in part 2
- `Aligner/mapper/PairHitsKP.lean` core `hitsCK` (`:22-35`): array/ByteArray + `Nat` arithmetic over a filter then a kernel call; once `diags`/`shapesAt` are lowered to Buf loops it is a plain scalar loop.
- `Aligner/mapper/TierRouter.lean` `Tag` enum + `Tag.str` (`:349-355`): trivial tag table.
- `Proofs/Fastq.lean` / `Proofs/SamBytes.lean`-style byte routines (FASTQ record validity, SAM line formatting, 641/366 lines): pure byte loops, closest to "byte in → byte out". `Testing/notes/byte_specs/*` give clean byte specs (no sorry).
- `Aligner/mapper/ReadTrim.lean` (668 lines), `PairExact.lean` (133), `PairInterleave.lean` (153), `FastGenCover*` (small): short, mostly arrays and Nat (not inspected in detail; uncertain).
- `Main.lean`'s `chunk/process` loop is exactly a fuel-bounded loop (`fuel = 2^64`, `Spec/MapFiles.lean process`), same shape as our `loop n`.
- Best strategy for the project: take a **small kernel-level slice** (e.g. a gapless/banded score function from part 1 or `hitsCK`), not the router.

## 7. Proof angle
Yes, a great deal. The repo ships machine-checked proofs, no Mathlib, only `propext, Classical.choice, Quot.sound`:
- `Spec/Aligner.lean:219 alignPairs_correct`, `:236 alignPairs_end_to_end` (statements); proved in `Proofs/Aligner.lean:777`, `:837`. Key lemma `alignOne_correct` (`:618`), `alignPairs_eq_map` (`:536`).
- `Proofs/MapFiles.lean:87 process_correct`: streaming `process` equals `mapReads` on the concatenated FASTQ; `Proofs/MapCorrect.lean:52 process_correct'`.
- `Proofs/IndexFinal.lean:271 buildIndex_eq_saveIndex`, `Proofs/Aligner.lean:561 readIndex_buildIndex`, `:91 indexOk_sound`.
- Mapper: `mem_hitsAtKP_mz` (hits within cap ↔ `hitsBoth`, doc in `PairHitsKP.lean:1-14`), `hitsAtKP_eq`, `tierPair_sound` (`TierRouter.lean`), `ParMap` `parMap_eq`-style results (Task = pure).
- Audit: `Testing/checks/AuditAlignPairs.lean` checks no unsafe/extern/partial behind the theorems.
Inheritance is not free: proofs are about the Lean definitions over Nat/Int/List; our compiled UInt64/Buf version needs a refinement bridge. But the repo's own pattern ("fast version + equality proof + `@[csimp]`", `AGENT_OVERVIEW.md` Rules) is the same shape: write nano-subset defs, prove them equal to the original, reuse the top theorem.

## Uncertain / not checked
Counts are grep-based (double counts on comments). I did not open most of `TierRouter`, `TierHeur`, `FastGenWordFilt`, or build anything. Whether UInt64 shifts/bitops exist in the nano subset not verified here.
