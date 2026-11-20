# Lean SVG assessment, part 1 (SONNET-ASSESS-06)

Repo: rowancallahan/lean-svg (`git clone --depth 1`, succeeded; nothing built). Line numbers refer to that repo.

## 0. Overview of the whole program
- Entry: `Main.lean:30` `def main (args : List String) : IO UInt32`. It reads one file (`IO.FS.readBinFile`), checks that the output path does not exist, calls the pure `renderWithWarnings`, then writes with `.writeNew`.
- Input: SVG text bytes plus argv (`--width/--zoom/--background/--viewport/--threads/--warnings`). Output: a PNG file, plus an optional `<out>.warnings.txt`. Exit codes 0/1/2.
- Pipeline (pure): `Xml` -> `Css` -> `Svg` tree -> `Geom`/`Shape` paths -> `Raster`/`Canvas` -> `Filter`/`Mask`/`Clip`/`Pattern`, with `Text`/`Font`/`Bidi` for text and `Png`/`Jpeg`/`Gif`/`Woff`/`Brotli` for embedded images and fonts, then PNG encode. A resvg clone. Design is `Int`-based fixed-point and has no Float.
- Whole repo: 35,306 lines of .lean in 119 files. `LeanSvg/Svg.lean` (5,050 lines) is the largest and falls in the second half.
- Proofs: `spec/` holds about 10 files and 1,300 lines. They are about I/O locality and size bounds, not about rendering (section 7).

## 1. My slice (split rule applied)
Sorted `.lean` files; the cumulative-line crossing of half (17,653) lands inside `PatternRender.lean` (cum. 17,528 -> 17,925). I took the first 81 files, up to and including `LeanSvg/PatternRender.lean`, about 17.9k lines. This includes `Main.lean`-adjacent dump tools (`FontDump`, `JpegDump`), `LeanSvg.lean`, `Baseline`..`Pattern*`, and 35 `Fonts/*.lean` data modules. The 2nd half starts at `Png.lean`.
- Counts in slice (grep, approximate): 1,021 `def`/`abbrev`; 29 `inductive`; 60 `structure`; 0 `theorem`; 0 `partial`; 0 `mutual`; 0 `unsafe`/`extern`; 0 macros.
- Many files are tiny; the logic is concentrated in `Bidi` (847), `Brotli` (551), `Canvas` (840), `Css` (575), `Filter` (1144), `Font` (1154), `Geom` (1043), `Clip` (393), `BasicShape` (467), `Inflate` (229), `JpegDecode` (657), `Marker` (514), `Lighting` (547).
- Per-file def counts: Font 65, Canvas 63, Geom 61, Filter 59, Lighting 46, FilterApply 35. **Whole-program def count is plausibly 2,000+ (slice alone ~1,000)**, so it is far over the 511 cap even after the cap is raised several-fold.

## 2. Lean features used (slice; counts are grep line counts, upper bounds)
| Feature | Count | Examples |
|---|---|---|
| `Nat` | ~890 lines | `Canvas.lean:23` pixels are `Array Nat`, one packed `r<<24|g<<16|b<<8|a` per pixel; `Bytes.lean:13` `at' (bs) (i : Nat)` |
| `Int` (unbounded) | ~600 | `Fixed.lean:17` `abbrev Fx := Int`, all coordinates; `Int.ediv`, `Nat.sqrt` (`Fixed.lean:49`, `Canvas.lean:511`) |
| `ByteArray` | 337 | all parsing is over `ByteArray` (`Bytes.lean:3`) |
| `Array` | 550 | `Array Nat`, `Array (Array ..)`, `Array String` |
| `String` | 255 | `Css.lean:48` `eq (v : String)`; `Filter.lean:298` `HashMap String Nat`; `FontFace.lean:53` family names |
| `Option` | 307 | `Inflate.lean:49` `build ... : Option Huff` |
| `Except` | 6 (slice; Render/Main use more) | `Render.lean` `Except String ..` |
| `List` | 22 | rare, mostly in Main/Cli (2nd half) |
| `Std.HashMap` | 8 | `Clip.lean:265` `abbrev Cache := Std.HashMap Key Res`; `Filter.lean:8,298,331` |
| `do` notation | ~625 | `Id.run do` with `let mut` |
| `for ... in [a:b]` | ~390 | `Bytes.lean:27-60`; nearly every loop |
| `while`/`repeat` | 27 (grep also matches prose) | uncertain; check |
| structural fuel recursion (`fuel + 1`) | present | `Inflate.lean:119,145,193` (`codes`, `readLens`, `blocks`) |
| `inductive` | 29 | `Geom.lean:148 PathCmd`, `Geom:478 Cap`, `Geom:482 Join`, `Css.lean:46 AttrOp`, `Css:67 Combinator`, `Filter.lean:159-193` (Input, CMKind, TF, CompOp, Kind), `Filter:847 Outcome` |
| `structure` | 60 | `Canvas.lean:16 Rgba`, `Canvas:23 Canvas`, `Brotli.lean:62 Code`, `Brotli:241 Blocks` |
| typeclass / instance | 1 / 2 | `FontFace.lean:53` `instance : Repr Face` (debug only). `deriving Repr, Inhabited, BEq` used on structures |
| UInt8 / UInt32 / Int32,Int64 | 63 / 21 / 57 | `Bytes.lean` `UInt8` predicates; Int64 in hot paths (`Mat.apply`, `Fixed.lean:22` `inRange`) |
| UInt64 | ~1 | essentially unused |
| `Float` | 1 (a comment, `Oklab.lean:13`) | the program is Float-free by design (`Fixed.lean:3`) |
| `partial` / `mutual` / `unsafe` / `extern` / macros / `termination_by` | 0 | confirmed absent in slice |
| `IO` | 30 | only in `FontDump.lean`/`JpegDump.lean` (dump tools) plus `Main` |
| `Task.spawn` | in `Render.lean:1034` (2nd half) | band-parallel render, `--threads` |
| imports | `Std.Data.HashMap` only; no Lean/Mathlib | "TCB is Lean core only" (`lakefile.toml`) |

## 3. Needed vs incidental, and cheapest encoding
- **`Nat`/`Int` unbounded**: Mostly incidental. `Fx` is explicitly clamped to ±2^30 and products stay below 2^62, so signed 64-bit values suffice (`Fixed.lean:20-26` states the range reason). Encode as UInt64 holding two's-complement, with explicit signed `ediv`/compare helpers (floor division semantics are needed: `Fx.mul/floor/ceil/round` use `Int.ediv`). Risk: some intermediates (`a * b` before clamp, transform 16.16 matrices times 2^30 coords = 2^46 OK; `Fx.hypot` squares up to 2^60 each, sum can reach 2^61, OK). Colour/ε-free; `Nat.sqrt` needs an integer sqrt routine (fuel loop). Marked uncertain: other modules (Oklab with 10^-6 decimals, `Filter.lean:57` mentions 2^120 and 50-digit operands via `Nat.log2`) deliberately use big ints for parsing; those need a bounded-saturation rewrite.
- **`ByteArray`/`Array Nat`**: needed, maps 1:1 to `Buf` (one UInt64 per byte/element). `Canvas.px` packs RGBA in one Nat -> one Buf word per pixel fits. Easiest mapping in the whole slice.
- **`String`**: mostly incidental (names, ASCII literals like `startsWith bs i "<svg"` at `Bytes.lean:52`). Encode as Buf of bytes; literals need either a string-literal-to-Buf feature or hand-expanded byte lists. `Css` selectors/properties are string-keyed throughout -> needs interning to small ints.
- **`inductive` (29)**: needed. Mostly enums (`Cap`, `Join`, `CMKind`, `CompOp`, ...: encode as UInt64 tags) and a few with payload (`PathCmd`, `Css.AttrOp (v : String)`, `Filter.Kind`). Payload ones need tagged Buf nodes. Pattern `match` must be rewritten as `if` chains.
- **`structure` (60)**: needed, but flat-record: encode as fixed-offset Buf slices or as tuples. Large nested ones (Canvas record, Brotli `Code`, `Filter` configs with `HashMap` field `ids`) need design.
- **`Option`/`Except`**: pervasive, partly incidental. Encode as (tag, value) pairs or sentinel + error flag.
- **`for i in [a:b]` loops**: needed; the program has "no `partial`" and "every scan is a `for` loop over a finite range" (`Bytes.lean:3-6`). This is the cheapest feature: each maps to `loop n` with early `break`/`return` (`findByte` at `Bytes.lean:36` uses early `return`; `break` at `:30`). Needs early-exit semantics in the fuel loop, or flag-guarded bodies.
- **`let mut` + `Id.run do`**: needed everywhere; translate to loop-carried tuples. Wide state tuples (10-20 mutable vars in rasterizers/decoders) stress the 250-word frame limit and tuple arity (uncertain).
- **fuel recursion** (`Inflate.codes/readLens/blocks`, `Inflate.lean:119-215`): already in fuel shape, so it maps directly to `loop`.
- **`Std.HashMap`** (`Clip` cache, `Filter` id table): incidental. Replace with Buf linear scan or open-addressing in a Buf.
- **`Task.spawn`**: incidental; run single-threaded.
- **`IO`**: only `Main` (read one file, write one/two files). The compiler's byte input/output replaces it; file naming/exists checks and exit-code 2 would go away or be redefined.
- **embedded fonts**: see blockers.

## 4. Hard blockers (ranked)
1. **Embedded font data: ~24 MB of font bytes, ~32 MB source** in `LeanSvg/Fonts/*.lean` (35 modules; headers like `-- 140270 bytes of embedded, subsetted TrueType font data`, `Arimo.lean:2`) plus `BrotliData.lean` (122,784-byte static dictionary as base64 string chunks, `BrotliData.lean:5-7`) and `StixNonUnicodeTable.lean`. Compiler input is limited to 1 MiB and there are no strings. These cannot be inlined. Options: pass fonts as runtime input bytes (concatenated blob after the SVG), or drop to a few small fonts; Brotli dict as input too. Needs a design decision; changes the "program" contract (not purely SVG-in).
2. **Program size**: ≥2,000 defs total vs a 511 cap; the slice alone (~1,000 defs) is double. Also parser node cap 16,384 will be exceeded by single files: `Filter.lean` (1,144 lines, 59 defs) and `Font.lean` (1,154) are each plausibly 10k+ nodes (estimate; uncertain). Needs either raised caps or large-scale modular compilation.
3. **Unbounded `Nat`/`Int`**: pervasive, with places that rely on bignum (`Filter.lean:57`, decimal parsing in `Fixed.lean`). Each module needs a bound analysis; a few semantic changes (saturation) could change output bytes versus the verified-against-resvg golden images. Not a compiler blocker, but a large rewrite.
4. **Inductives with payload, `String`, `Option`, `Except`, `structure`, `match`**: none accepted today; this is the same compiler-feature gap as the other targets. Pervasive, so it must be supported in the compiler rather than hand-rewritten.
5. **`for`/`break`/`return` inside `Id.run do`**: needs the loop feature to support early exit and mutable-state tuples of high arity; 389 loops in this slice.
6. **Frame ≤ 250 words and call arity**: rasterizer/decoder functions with many parameters and let-bound intermediates (JpegDecode, Font glyph outlines, Brotli) may exceed it (uncertain; needs per-function measurement).
7. Typeclass-dependent library calls (`Array.push`, `ByteArray.push`, `HashMap.insert`, `Nat.sqrt`) are used implicitly; each needs a Buf/UInt64 primitive.

## 5. Runtime needs (slice)
- Input: SVG up to `maxInput` = 64 MiB per `spec/SizeBound.lean` (render rejects larger); realistic test SVGs are KB to MB. The compiler's 1 MiB input limit fits typical ones but not the 64 MiB limit; the embedded font ~24 MB would not fit either way.
- Output: PNG; a canvas is `w*h` words in a Buf (e.g. 800x600 = 480k words ~ 3.8 MB; 4000 px wide tiles are bigger). Work memory 1 GiB should allow it. Per-pixel/filter loops (`Filter`, `Lighting`, `Turbulence`) are heavy: README quotes 26-240 ms per image in native Lean; a verified-compiler's code will be slower, and fuel counts must be sized per pixel loop (up to 10^7-10^8 iterations).
- Heavy computation: JPEG IDCT/Huffman, Inflate, Brotli (for WOFF2 fonts), Bidi, Gaussian blur/morphology/turbulence, path flattening and anti-aliased rasterization.

## 6. Easy wins (closest to the subset)
- `Bytes.lean` (111 lines, 18 defs): byte predicates, `skipWhile`, `findByte`, `startsWith`, `findSeq`. Pure `ByteArray`/`Nat` + `for`; strings appear only as literals in `startsWith`/`findSeq`.
- `Inflate.lean` (229 lines): fuel recursion over `ByteArray`/`Array Nat`, with `Option` results. Already the "fuel loop" shape; Huffman table building is plain array code. Strong candidate for a first real module (Gzip/PNG-zlib decode).
- `Fixed.lean` (264 lines, 26 defs): small `Int` arithmetic helpers; map to signed UInt64 ops.
- `Oklab.lean` (133), `Units.lean` (124, 2nd half), `Gzip.lean` (72), `Jpeg/Idct.lean` (137), `Filter/Gamma.lean` (106), `Filter/Tile.lean` (66), `Filter/DisplacementMap.lean` (64): small numeric array kernels with few inductives. (From def counts and line counts; I did not read all of them.)
- `Canvas.lean`: packed-pixel integer blend math (`div255`, `Canvas.lean:35`), structure with just w/h/`Array Nat`; blend functions are straight UInt64 arithmetic.

## 7. Proof angle
- **No theorems in `LeanSvg/` at all** (`spec/README.md`: "There are no theorems under `LeanSvg/`"; slice grep: 0 `theorem`). Only a few `example`s next to code in `FamilyMatch`, `Synth`, `StixNonUnicode` (second half).
- Proofs live in `spec/` and are about the I/O shell and bounds: `Cli.parse_paths_mem`, `parse_paths_ne_empty`, `parse_warnings_iff`, `warnPath_ne` (`spec/Cli.lean:19,60-72`); `render_rejects_large` / `renderWithWarnings_size_le` (`spec/SizeBound.lean:261`); locality/`GifDecode`/`Gzip`/`JpegDecode`/`PngDecode` files (small, ~30 lines each; contents not read, so uncertain); `Svg.use_maxDepth_le` (`spec/Svg.lean:15`, by `decide`).
- Our compiler would not inherit anything useful: the theorems mention Lean `String`/`List`/`IO` semantics of the source functions and most are about the Main shell, which we replace. No correctness theorems about rendering, so the verified-compiler value is the compilation correctness alone.
- Positive: the code uses no `sorry`, no `partial`, no `unsafe`/`extern`, and has no Mathlib dependency; so the semantics are plain core Lean.

## Summary ranking (feasibility)
Hardest of the four targets on size alone. A realistic path is incremental: the Inflate+PNG-decode / Gzip subset (+`Bytes`), then Canvas/Raster/Geom, then Css/Xml/Svg; leave fonts, Brotli, JPEG, Filters for last. Fonts must become runtime input. The `Int`->UInt64 bound analysis and inductive/`Option`/`structure` encodings are the cross-cutting compiler work.

Uncertain/unchecked: exact node counts, frame sizes, `while` usage, contents of the `spec/*Locality` files, whether the 64 MiB input cap is reached in practice.
