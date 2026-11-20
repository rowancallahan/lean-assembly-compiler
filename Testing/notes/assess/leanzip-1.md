# LeanZip assessment, part 1 of 2 (assess-04)

Repo: `lean-zip` (rowancallahan fork of kim-em/lean-zip), shallow clone, toolchain `leanprover/lean4:v4.34.0`. Clone worked; nothing built (lakefile needs a git dep `zipCommon` and C `extern_lib`s).
Uncertain items are marked (?). Counts are by grep, so approximate.

## 0. Split and program overview

Split rule: `git ls-files '*.lean' | LC_ALL=C sort`, 99 files, 73,911 lines total, half = 36,955. Part 1 = files whose cumulative end ≤ half:
`Zip.lean` … `Zip/Spec/DeflateStoredCorrect.lean` (cum. 36,910), 49 files. Part 2 starts at `Zip/Spec/DeflateSuffix.lean`.
Part 1 = **all 19 `Zip/Native/*.lean` (16,967 lines, the executable code)** + 29 `Zip/Spec/*.lean` (19,872 lines, proofs/specs, A…DeflateStoredCorrect) + `Zip.lean` (imports).

Whole-program overview:
1. Pure-Lean verified DEFLATE (RFC 1951), zlib (1950) and gzip (1952) codec, plus CRC-32 and Adler-32. It is a **library**, not a CLI.
2. Entry points are API functions: `Zip.Native.GzipEncode.compress data level` (`Native/Gzip.lean:151`), `GzipDecode.decompress` (`Gzip.lean:~35`), `ZlibEncode/ZlibDecode`, `Deflate.deflateRaw`, `InflateBuf.inflate`.
   The only `main`s are test and conformance harnesses (`ZipTest.lean:10`, `conformance/Conformance.lean:12`, `conformance/FuzzInflateMain.lean:31`).
3. Input is a `ByteArray` (plus level 0–10 / `maxOutputSize`). Output is a `ByteArray`, or `Except String ByteArray` on decode.
4. Levels: 0 stored, 1 fixed Huffman, 2–4 lazy LZ77, 5+ dynamic Huffman, 10 an optimal parse via DP.
5. Dependency outside the repo: `lean-zip-common` (`ZipCommon.Binary`, `ZipCommon.BitReader`, `ZipForStd.*`). Those files are not in this clone, and the Native code uses them (`BitReader`, `Binary.readUInt16LE`). The pieces we need would have to be inlined or re-implemented.
6. C code: 4 `@[extern]` stopgaps in `c/*.c`, each with a Lean reference body. Part of the hot path runs through them.

## 1. Size (slice)

| | Native (16,967 l) | Spec (19,872 l) |
|---|---|---|
| defs/abbrevs | **582** | 84 |
| theorems/lemmas | 215 | 661 (total slice: 876) |
| `termination_by` | 163 | 32 |
| `decreasing_by` | 110 | 10 |
| `sorry` / `native_decide` / `partial` / `unsafe` | 0 / 0 / 0 / 0 | 0 / 0 / 0 / 0 |

Per-file (lines, defs, theorems, wf-recursions) for Native:

| file | lines | defs | thms | wf |
|---|---|---|---|---|
| DeflateDynamic | 4081 | 198 | 24 | 25 |
| Deflate | 3789 | 103 | 36 | 54 |
| DeflateFreqsFused | 1651 | 36 | 3 | 10 |
| Inflate | 1643 | 60 | 38 | 21 |
| DeflateParse | 1301 | 53 | 17 | 25 |
| InflateFast | 831 | 23 | 3 | 7 |
| InflateTreeFree | 652 | 24 | 4 | 11 |
| BitWriter | 565 | 21 | 18 | 1 |
| HuffmanEncode | 412 | 9 | 14 | 1 |
| DeflateFreqs | 380 | 9 | 10 | 3 |
| TokenArray | 367 | 10 | 22 | 0 |
| DeflateL5 | 335 | 7 | 0 | 2 |
| Gzip | 297 | 9 | 0 | 1 |
| Wide | 196 | 9 | 4 | 0 |
| Adler32 / Crc32 | 153 / 138 | 3 / 3 | 9 / 12 | 0 |
| InflateBuf / CopyWithin / ExtendWithin | 68 / 41 / 67 | 2 / 1 / 2 | 1 / 0 / 0 | 1 / 0 / 1 |

Biggest Spec files in the slice:
- `DeflateFreqsFusedCorrect` 3509 l
- `DeflateBlockSplit` 2038 l
- `DeflateRoundtrip` 1242 l
- `Deflate` (the spec) 1031 l
- `DecodeCorrect` 999 l

## 2. Lean features used (Native, slice)

| feature | count / examples | needed? | cheapest encoding |
|---|---|---|---|
| **Nat (unbounded)** | ~2985 mentions Native, 3133 Spec. Positions, lengths, sizes, loop indices, `Array Nat` hash tables (`Deflate.lean`, 74 `Array Nat` mentions) | Needed as quantity, never genuinely big (bounded by input size, ≤ 2^32 in practice; code assumes `data.size < USize.size`) | UInt64 + asserts. Subtraction is truncated in Lean (`maxOutputSize - result.size`, `Gzip.lean:~78`), so keep the saturating `sub`. |
| UInt8/16/32/64/USize | UInt32 648, USize 1109, UInt8 349, UInt64 303, UInt16 94. Shifts/masks `<<< >>>` 340 | Core (bit I/O, CRC, hash) | All widen to UInt64 with an explicit mask. Overflow of UInt32 add/mul must be re-masked (`& 0xFFFFFFFF`). Narrow-type semantics (UInt8 wraparound, shift mod width) must be reproduced exactly. |
| **ByteArray** | 636 Native (push, extract, `++`, `data[i]`, `uget/uset`, `copySlice`) | Core: input and output are ByteArrays | Buf of UInt64, one byte per word. `bpush` = push. `extract`/`++` become copy loops. Memory is 8× larger than bytes: 1 MiB input → 8 MiB, which is fine against 1 GiB. |
| **Array** (of Nat / UInt32 / UInt8 / structures) | 756 | Core: Huffman tables, hash heads, `prev` chain (32 K), frequency counts | Buf. Arrays of structures need struct-of-arrays or packed words. |
| **List** | 195 Native, 1316 Spec | Native: incidental (mostly Spec-side; `lz77Greedy` etc. return `List LZ77Token`, with `…Iter` and `…P` array twins used in production) | Use the Array/packed-token variants (`TokenArray`: UInt32-packed tokens, `Native/TokenArray.lean`). Drop List variants. |
| **Option** | 20 Native, 284 Spec | Mostly incidental | `(flag, value)` pair. |
| **Except String** | 68 Native (`Except String (ByteArray × Nat)`, `throw s!"…"`) | Needed as an error channel. The message text is incidental (`s!` interpolation: 61 `String` mentions) | Return a status UInt64 (0 = ok, k = error code). Messages are dropped. This changes the theorem statements: `.ok data` is kept, but `.error msg` loses its payload. |
| **String / Char** | 61 / 0, only in `throw` messages | Incidental | Delete or error codes. |
| **inductive** (8) | `HuffTree` (leaf/node/empty, `Inflate.lean:45`), `LZ77Token` (literal/reference, `Deflate.lean:418`), `CompressFormat` (`Gzip.lean:248`), `L7Profile`, `L7OutputRoute`, `L3/4/5AdaptiveRoute` (`DeflateDynamic.lean:1418–1681`) | HuffTree/LZ77Token: needed. Routes/Profile: enums, tuning, rewritable as UInt64 tags | `HuffTree` → flat Buf `[sym, zero, one]` triples (or drop it for the `DecodeTable`). `LZ77Token` → packed UInt32 (already `packTok`, `Deflate.lean:~440`). Enums → numbers. |
| **structure** (8) | `BitWriter` (`BitWriter.lean:31`: ByteArray + UInt64 + UInt8), `DecodeTable` (`Inflate.lean:221`: packed Array UInt32), `TokenArray` (`TokenArray.lean:157`, carries a Prop field `aligned`), `DynHeaderPlan`, `L7MatchConfig`, `WideRefillState`, `LongDecode`, `LZ77ChainIterPNext` | Needed as grouping | Tuples, or a Buf with fixed field offsets. Prop fields vanish. |
| **Recursion, structural** | a few (`HuffTree.insert.go`, `flushAcc`) | | Fuel loop. |
| **Recursion, well-founded** | 163 `termination_by`, 110 `decreasing_by` (mostly `data.size - pos`, `dataSize*8 - bitPos`; `Deflate.lean` 54, Inflate 21, DeflateParse 25, DeflateDynamic 25) | Core: every loop is a WF recursion | Fuel loop `loop n` with `n = data.size` (or a bound derived from the measure). Gaps: the interleaved measure `2*(data.size-mp)+1` in the mutual block (`Deflate.lean:1775`) and loops where the measure is only bounded by input size (e.g. the 1000-iteration member loop, `for _ in [:1000]`, `Gzip.lean:~70`). |
| `partial` / `unsafe` | 0 / 0 | | none |
| **mutual** (3 blocks) | `Deflate.lean:1679` (`lz77ChainLazy.mainLoop` …), `:1871`, `:2110` | LZ77 lazy matcher (levels 2–4): tangled | Inline into one fuel loop with a state tuple. |
| **do-notation / `let mut` / `for` / `while`** | do 89, `let mut` 37, `for … in` 21, `while` 49, `Id.run` 10 (`Deflate.lean:28 deflateStored`) | Surface syntax only | Desugars to let/loop; needs front-end support or a manual rewrite. `while` has no termination argument (it is `Loop.mk`, i.e. partial under the hood), so it needs an explicit fuel bound. |
| Typeclasses/instances | instance 0 in Native (1 in Spec); but implicit class use everywhere: `Inhabited`, `BEq`, `GetElem` (`data[i]'h`, `arr[i]!`: 85 `[]!`), `deriving BEq, Inhabited` | `[]!` and `data[i]'h` are the access path (proof-carrying index) | Inline as `bget` plus an assert (the user preference is fail-fast, which matches `[]!` panics). |
| HashMap / Std data | 0 | | none (hash tables are hand-built `Array Nat`) |
| IO / monads (StateM/ST/Task/IO.Ref) | 0 | | None in Native. The only monad is `Except` and `Id.run`. |
| **Float** | 3 (`histEntropy`, `DeflateDynamic.lean:3618`, uses `Float.log2`) | Incidental: used only to pick a block-split profile for levels 3–5 (route heuristic) | Replace with an integer approximation, or fix the route. Changes the compressed bytes, not roundtrip correctness. |
| `@[extern]` (36 mentions, 8 real decls) | `lean_zip_uget_u32le/u64le`, `uset_*`, `push_u64le`, `uint32_log2_clz`, `ctz64`, `copy_within(_at)`, `extend_within`, `presize` (`Wide.lean`, `CopyWithin.lean`, `ExtendWithin.lean`, `InflateFast.lean:54,83,91`) | Incidental: each has a Lean reference body ("trusted specification") | Compile the reference body and ignore the `@[extern]` attribute. We have no FFI. |
| `@[implemented_by]` (4 real: `Deflate.lean:346,3159,3189`, …) / `@[csimp]` | `distCodeWord`, `lz77ChainLazyIterPMergedH3Native` … | Incidental perf | Take the reference body. (?) which of the pair is the semantic one: the `implemented_by` target is the fast unverified twin, so the compiler should take the **logical** definition. |
| Attributes `@[inline]`, `@[specialize]`, `@[noinline]` | 121 | Incidental | Ignore. |
| macros/notation | 0 Native (1 `instance`, 0 macro in Spec) | | none |
| Imports | `Std.Tactic.BVDecide` (5 Native, 2 Spec), `ZipCommon.*`, `ZipForStd.*`; no Mathlib, no `Lean.*` | | `BVDecide` is proofs only (CRC `bv_decide`, `Crc32.lean:~33`). |
| Comments | very heavy (`/-- … -/`, `--`; docstrings are > 40% of Native lines) | | Must be stripped, since the compiler input accepts no comments. |

## 3. Per-feature verdict (summary)

Needed: bounded Nat, fixed-width UIntN, ByteArray/Array as Buf, well-founded loops (→ fuel), one tuple/struct for the bit reader/writer, a Huffman table as a flat Buf.
Incidental: Strings, Floats, Lists (in the production path), the externs and `implemented_by` twins, mutual blocks that could be merged, most of the 10 levels. A minimal LeanZip needs only {stored, fixed, one dynamic} on the encode side and a single inflate.

## 4. Hard blockers (ranked)

1. **Dependency on `ZipCommon.BitReader` and `ZipForStd`**, which live in another repo and are not in this slice. They would need to be vendored or re-implemented. (?) Size unknown, probably a few hundred lines.
2. **Def count**: 582 defs in Native alone, versus the 511 cap. This is the first hard stop for the *whole* program. A trimmed build (inflate + level 0/1 + CRC/Adler + gzip/zlib framing, see §6) would be roughly 150–200 defs.
3. **No recursion except fuel loop**: 163 WF recursions, 3 mutual blocks. Each must be turned into `loop n …` with an explicit bound. Mechanical for the `pos`-indexed loops (`scanToZero`, `inflateLoop`: measure is `dataSize*8 - bitPos`). Hard for the lazy-LZ77 mutual group and the DP optimal parse (`DeflateParse.lean`).
4. **Proof-carrying code**: `if h : i < a.size then a[i]'h`, `have hmaxLenP : pos + maxLen ≤ data.size := by omega`, `TokenArray.aligned`. The accepted subset has no proofs. All of these have to be erased to asserts, which makes the theorems about the *source* program not directly about the compiled one (see §7).
5. **`Except`/`do`/`for`/`while` front-end**: needs either compiler-side desugaring or a manual rewrite of ~90 do-blocks, plus fuel bounds for every `while`.
6. **Unbounded `Nat` semantics**: truncated subtraction and `Nat → UInt32` wrap (`n.toUInt32`, `Gzip.lean:159`, `isize := data.size.toUInt32`) must be matched exactly. For UIntN (N < 64), a UInt64 encoding needs masks after every add/mul/shift-left.
7. **Frame limit ≤ 250 words**: functions with large argument lists. `lz77ChainLazy.mainLoop` takes ~14 args plus lets (`Deflate.lean:1681`), `lz77LazyMergedLoop*` similar. They will need a state Buf.
8. **Tuple-heavy returns**: `Except String (ByteArray × Nat)`, `(UInt32 × BitReader)`, `(litTree, distTree, br₃)`: tuples are accepted, but nested tuple-of-struct returns will pressure the frame limit.

## 5. Runtime needs

- Input size: any (gzip streams up to 1 GiB by default, `maxOutputSize := 1024*1024*1024`). Compiler cap is 1 MiB input, so only small tests are possible. Part of the code is tuned for 200 MB inputs (presize cap 64 MiB, `Gzip.lean:~25`), which is irrelevant if we only target ≤ 1 MiB.
- Output: up to `maxOutputSize`. Output buffer limits in the compiler apply.
- Memory: LZ77 hash table + prev chain (`Array Nat`, 32 K entries each, plus `h3tab`) ≈ 0.5 MiB at 8 B per word. Token buffer ≈ 4 B × n tokens, 8 B × n as Buf words. Output Buf is 8 B per byte. Within 1 GiB for ≤ 1 MiB inputs.
- Def count: whole Native 582 (> 511). Realistic minimal inflate-only core is ~60 defs (`Inflate.lean`) + 20 helpers.
- Node count vs 16,384: not measurable without running the parser (?). Rough estimate: a 1,643-line Inflate with docstrings stripped is perhaps ~900 code lines, likely 10–20 K nodes, so it probably exceeds the cap unless split. `DeflateDynamic` (4081 l) is certainly over. Treat the cap as binding.
- Heavy computation: LZ77 match search (chain walk, up to 4096 steps per position at L7+), the DP optimal parse (L10), block splitting, entropy (Float). All are loops over input with per-position state. Fuel `n` = data.size × maxChain is large but fine.

## 6. Easy wins (already close to the subset)

- **`Crc32.Native`** (`Crc32.lean:15–28`, 3 defs): a `table : Array UInt32` + `foldl`. Table-driven, UInt32 xor/shift only. Needs a bit-by-bit table construction (`Spec.mkTable`) and a fold → fuel loop. **Best first target.**
- **`Adler32.Native`** (3 defs): two UInt32 sums modulo 65521. Same shape.
- **`deflateStored`** (`Deflate.lean:28`): `Id.run` + `while` + push. Trivial after a fuel bound.
- **`GzipEncode.compress` level 0** (`Gzip.lean:151`): header ++ stored ++ CRC trailer. Gives an end-to-end "gzip a buffer" without Huffman, using only push/extract/arith. Round-trip is checkable with a matching `decompressSingle`.
- **`scanToZero`**, header parsing in `GzipDecode.decompress`: byte scans.
- **Inflate (reference path)**, `Inflate.lean` (1643 l, 60 defs): the only non-trivial data structure is `HuffTree`/`DecodeTable`; `inflateRawReference` (`:1603`) is the spec-level decoder that the proofs target. Medium effort, and the best "real" target (decompress gzip → bytes).
- **Fixed-Huffman encode** (L1): needs `BitWriter` (21 defs, UInt64 accumulator, already scalar-shaped) + greedy LZ77.

Hard / defer: DeflateDynamic, DeflateParse (optimal parse), DeflateFreqsFused, InflateFast/TreeFree (perf variants of inflate, replaceable by the reference decoder).

## 7. Proof angle

Yes, heavily. The repo proves the key properties and has **no sorry** (README, CI-checked):
- `zlib_decompressSingle_compress` (`Spec/ZlibCorrect.lean:147`) and `gzip_decompressSingle_compress` (`Spec/GzipCorrect.lean:210`): decompress ∘ compress = id for every input and level.
- `inflate_deflateRaw` (`Spec/DeflateRoundtripProduction.lean:28`), via `inflateReference_deflateRaw`; per-component: `inflate_deflateRawBase` (`DeflateRoundtrip.lean:143`).
- `inflate_correct` (`Spec/InflateCorrect.lean:660`): native decoder result = `Deflate.Spec.decode` (soundness); `inflateRaw_complete` (`Spec/InflateLoopBounds.lean:564`): completeness against the spec.
- `crc32_append`, `adler32_append`, `adler32_combine_eq_concat` (native files).
- In this slice: `Spec/Deflate.lean` (RFC 1951 reference decoder `Deflate.Spec.decode`), `DeflateStoredCorrect`, `DeflateFixedCorrect`, `BitWriterCorrect`, `Bitstream*`, `Huffman*`.

Caveat for "inherit": these theorems are about the Lean source (`Nat`, `ByteArray`, `Except String`, WF recursion). Our compiled code runs the UInt64/Buf/fuel rewrite. Inheritance needs one more theorem per rewritten function (translation of the rewrite = original, under bounds) — that is new proof work, not free reuse. Where the rewrite is a verbatim copy with erased proofs and fuel ≥ the measure, the argument is mechanical. The proofs also depend on `native_decide`-free but `bv_decide` (SAT) steps (`Crc32.lean`, 5 files import `Std.Tactic.BVDecide`), and `decide_cbv` / the Lean `Std` library. These are not our compiler's concern, as we only compile the programs, not the proofs.

## 8. Recommended order

1. `Crc32` + `Adler32` (proof of concept, ≤ 10 defs).
2. `deflateStored` + `GzipEncode.compress level 0` + a stored-only decompress (end-to-end gzip without Huffman).
3. `Inflate` reference path (fixed + dynamic), with `BitReader` vendored; flatten `HuffTree`.
4. Fixed-Huffman encode + greedy LZ77 (L1), using `BitWriter`.
5. Everything else (lazy matcher, dynamic encode, optimal parse) only if the def and node caps are raised.
