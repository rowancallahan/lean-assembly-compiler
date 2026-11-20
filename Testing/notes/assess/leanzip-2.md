# LeanZip assessment, part 2 of 2 (assess-05)

Repo: rowancallahan/lean-zip, depth-1 clone, toolchain `leanprover/lean4:v4.34.0`. Not built. Counts come from grep, so treat them as approximate.

## 0. Slice
`git ls-files '*.lean' | LC_ALL=C sort` gives 98 files and 73,911 lines. Half is 36,955. The cumulative count is 36,910 after `Zip/Spec/DeflateStoredCorrect.lean` and 37,718 after `DeflateSuffix.lean`. `DeflateSuffix.lean` straddles the cut and its midpoint is past half, so **slice 2 starts at `Zip/Spec/DeflateSuffix.lean`**. That is 65 files and 37,001 lines (the order is bytewise, so `Zip/Spec/D…` through `Zip/Spec/Z…`, then `ZipTest*`, `conformance/*`, `lakefile.lean`):
- Spec files (proofs): about 31.5k lines.
- `ZipTest/*` and `ZipTest.lean`: about 1.9k lines.
- `conformance/*` and `conformance/lakefile.lean`: about 4.1k lines.
- Root `lakefile.lean`: 157 lines.

**Slice 2 contains no executable algorithm.** It is almost entirely proofs about the code in `Zip/Native/*`, which is in part 1. Compile-ability of the algorithms belongs to the part-1 note. This note covers what the proofs mean for us.

## 1. Size and entry points
- Slice 2 has about 1,051 theorems and lemmas and about 267 defs/abbrevs, most of them proof helpers. It has 1 `sorry` mention: `Zip/Spec/InflateFastCorrect.lean:33` is the docstring "this file is `sorry`-free". There are no `axiom`s.
- The program is a library with these entry points: `Zip.Native.Inflate.inflate`, `Zip.Native.Deflate.deflateRaw` (data, level), and the gzip/zlib/checksum wrappers.
  - Input → output: `ByteArray` → `ByteArray` (compressed to raw, and the reverse), plus CRC32 and Adler32.
- There is no CLI. The only `main`s are test drivers: `ZipTest.lean:10` and `conformance/Conformance.lean:12`, plus `conformance/FuzzInflateMain.lean:31`.
- The `conformance/` sub-package needs `lean-zlib` (git, FFI to system zlib) and a second git dependency. We cannot compile it, and it is not needed.

## 2. Lean features in slice 2
Counts are for slice 2 only.

| Feature | Count / example | Role |
|---|---|---|
| Mathlib | none. Imports are only `Zip.*`, `ZipForStd.*`, `ZipCommon.*` (a git dependency) and `Lean`/`Std` core | n/a |
| Tactics | `simp`/`omega`/`native_decide`/`bv_decide`: about 5.4k occurrences; `native_decide` once at most | proofs |
| `termination_by` / `decreasing_by` | 107 / 45 | well-founded recursion in specs and proof helpers |
| `partial def` | 7, all in `ZipTest/*` (`ZipTest/Wide.lean:30,50,106`; `ZipTest/ExtendWithin.lean:68`) | tests only |
| `inductive` / `structure` | 12 (e.g. `Zip/Spec/LZ77.lean:16` `LZ77Symbol`, `HuffmanEncode.lean:33` `BuildTree`, `HuffmanCorrect.lean:113` `TreeHasLeaf` (a Prop), `LZ77NativeCorrect.lean:793` `ValidDecomp` (Prop), `InflateBufCorrect.lean:32` `BufCorr` (Prop structure)) | spec-side |
| `mutual` | 4 (`LZ77ChainLazyCorrect.lean:42,180,330`, `LZ77PackedCorrect.lean:100`) | proof-side |
| `instance` | 1 (`Zip/Spec/Huffman.lean:172`, `Decidable ValidLengths`) | spec-side |
| `@[extern]` / `implemented_by` | slice 2 only mentions them in docs, e.g. `InflateFastCorrect.lean:93`. The real externs are in part 1 and `c/*.c` (496 C lines: wide loads/stores, `copyWithin`, `extendWithin`, `inflate_fast`) | see §3 |
| `Float` | 10, benchmarks only (`Conformance/BenchHelpers.lean:37`, `ZipTest/Helpers.lean:119`) | incidental |
| `ByteArray` | about 1,000 uses, `List Bool` spec bitstreams | core data type |
| `IO` / do / `Id.run` | about 157, tests and bench only | incidental |
| macros / notation | 0 | n/a |
| `HashMap` | 0 | n/a |

The specs are written over `List Bool`, `List UInt8`, `Nat` and `Option`. Examples:
- `Deflate.Spec.decode : List Bool → Option (List UInt8)` at `Zip/Spec/Deflate.lean:392`.
- `bytesToBits : ByteArray → List Bool` at `Zip/Spec/Deflate.lean:30`.

None of this is executed. It exists only to state theorems.

## 3. Needed vs incidental, and the cheapest encoding
- **Needed in the algorithm (part 1, noted here for the proofs' sake).** The proofs mention these ideas, which any compiled version would need:
  - `ByteArray` with push, get and set: this is `Buf`, with one byte per UInt64 word.
  - `UInt64` bit buffer: native.
  - Huffman tables: a flat table Buf. The "tree-free" decoder (`InflateTreeFreeCorrect.lean`) is the right shape here, since it avoids the `HuffTree` inductive.
  - Overlapping match copy: a byte loop, with fuel = output length.
  - Nat → UInt64 with an assert that values stay below 2^32. The proofs already track bounds (`InflateLoopBounds.lean`, `maxOutputSize` zip-bomb limit).
- **Incidental in slice 2.** List/Bool specs, Props, mutual proof defs, test and bench IO, Float, `partial` test loops. None of it needs compiling.
- **`List Bool` bitstream specs.** These are not needed at runtime. We could only reuse them as the statement of correctness.

## 4. Hard blockers (ranked)
Mostly in part 1; recorded here because the proofs depend on them.
1. **Proof transfer.** The theorems are about Lean terms of `Zip.Native.*` over `ByteArray`, `Except String`, `Nat`, `Array`. Our verified compiler's source is a different, restricted language, so we need either (a) a rewritten UInt64/Buf port plus a refinement proof to the Lean version, or (b) a translator whose correctness covers those types. Neither exists. Without it, the compiled code carries no inheritance of the theorems.
2. **`Except String` and error paths.** `inflate` returns `Except`. We need an error-code encoding (UInt64 status plus output Buf) and an agreed correspondence for the `.error` case.
3. **Well-founded and structural recursion.** The compiler only accepts fuel-bounded loops. Each recursive production function needs a fuel argument and a proof that fuel is sufficient. Fuel bounds probably exist implicitly in the `termination_by` proofs (107 uses), though they are not in a reusable form (uncertain).
4. **Structures/inductives in the native code**, e.g. `BuildTree` and token arrays. Encode them as tagged Buf nodes.
5. **Externs**: `copyWithin`, `extendWithin`, wide loads/stores, `inflate_fast`. All have a "pure-Lean reference body" plus a correspondence proof (lakefile comment), so we can compile the reference bodies as plain loops. This is slow but correct.

## 5. Runtime needs
- Input and output sizes are set by the caller (`maxOutputSize`). Our 1 MiB input limit and 1 GiB work memory are fine for any reasonable test input.
- The compressor works over a hash chain (`LZ77Chain…`), so it wants a large `Array`. This is fine as a Buf.
- Def count: unclear. Part 1 has about 14k lines of Native code across `Deflate*`/`Inflate*`/`Huffman*`/`LZ77*`. This will blow the 511-def cap and the 16,384-node cap if compiled whole. A minimal subset (raw inflate + crc32) is likely to fit, and the full encoder at all levels will not (estimate, not measured).
- Heavy computation: LZ77 matching at levels 5–9 (lazy, optimal), and dynamic Huffman construction (package-merge or similar, `HuffmanEncode`). Inflate is cheap.
- Frame ≤ 250 words: `inflate_fast` and the Deflate matchers pass many state variables; we may have to split them into tuples (uncertain).

## 6. Easy wins
From slice 2 evidence (names and docstrings), the closest to the subset:
- CRC32 and Adler32 (`Zip/Spec/Crc32.lean`, `Adler32.lean`, native files are small: 138 and 153 lines): a table loop over bytes with UInt32 arithmetic.
- Stored-block deflate (`DeflateStoredCorrect.lean`): byte copying only.
- Fixed-Huffman deflate (`DeflateFixedCorrect.lean`, `DeflateFixedTables.lean`).
- Raw inflate via the tree-free canonical table path (`InflateTreeFreeCorrect.lean`, `InflateTable.lean`).
- The `ZipTest/Wide.lean` and `ExtendWithin.lean` "pure-Lean references" are tiny byte loops.

## 7. Proof angle
The project is a verified library, and there is a large proof corpus:
- **Capstone roundtrip**: `Zip.Native.Deflate.inflate_deflateRaw` at `Zip/Spec/DeflateRoundtripProduction.lean:~23`. For every `data`, `level` and `maxOutputSize ≥ data.size`, `inflate (deflateRaw data level) maxOutputSize = .ok data`.
- **Decoder is spec-correct and complete**: `Zip.Native.Inflate.inflate_ok_iff_decodesTo` at `Zip/Spec/InflateProductionCorrect.lean`. `inflate … = .ok output ↔ Deflate.Spec.DecodesTo compressed output` (given `output.size ≤ maxOutputSize`). Also `decodesTo_of_inflate_eq_ok` and `inflate_of_isValidStreamFor`.
- **Reference vs production**: `inflate_ok_iff_reference` (tree-free production decoder = reference decoder; `InflateTreeFreeCorrect.lean`, 3.9k lines).
- Reference decoder correctness: `Deflate.Correctness.inflate_correct'` (`InflateCorrect.lean:693`) and `inflate_correct` (`InflateCorrect.lean:660`).
- Others:
  - The Huffman spec: `HuffmanKraft.lean`, `HuffmanCorrect*.lean`.
  - Suffix invariance (`DeflateSuffix.lean`: `decode_go_suffix`, etc.).
  - LZ77 spec roundtrips (`LZ77Lazy.lean:136,299`, `LZ77ChainCorrect.lean`).
  - Per-level encoders (`LZ77*Correct.lean`).
  - The gzip and zlib wrappers (`GzipCorrect.lean`, `ZlibCorrect.lean`).
- The proofs are sorry-free and axiom-free. Trust gaps are only the C externs, each with a pure-Lean reference body and a correspondence proof.

**Inheritance for our compiled code.** None automatic. The proofs bind `Zip.Native.*` as Lean terms, not our compiler's input language. The cheapest route is probably a UInt64/Buf port of a small kernel (CRC32 or raw inflate), proven equal to the Lean function through a refinement lemma, and then reuse of the `inflate_ok_iff_decodesTo` and roundtrip statements. This is real proof work, since the Lean originals use `Nat`, `Array` and `Except`.

## Uncertainties
- The slice cut between `DeflateStoredCorrect` and `DeflateSuffix` is a judgment call on a straddling file.
- Counts are grep-based and include lines in docstrings and comments.
- Nothing was built or run, and the part-1 code was not read in detail. Native-side feature claims are from the lakefile and docstrings.
