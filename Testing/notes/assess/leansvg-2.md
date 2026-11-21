# Lean SVG assessment, part 2 of 2 (assess-07)

Repo: https://github.com/rowancallahan/lean-svg (shallow clone, HEAD at time of reading; not built).
Toolchain: Lean core only, no Mathlib/Std/FFI (`lakefile.toml:1-3`; only `import Std.Data.HashMap` twice).

## Split
`git ls-files '*.lean' | LC_ALL=C sort`: 119 files, 35,306 lines; half = 17,653. Cumulative line count
is 17,528 after `LeanSvg/Pattern.lean`, so part 2 = **`LeanSvg/PatternRender.lean` .. `tests/UnitsTests.lean`**
(43 files, 17,778 lines). Cut is by nearest file boundary (my reading; part 1 may differ by one file).
Contents: Png/PngDecode/Raster/Render/RootFit/Shader/Shape/ShapeData/ShapeRun/ShapeText/Svg/SvgImage/Synth/
Text/TextPath/Units/Use/VertOrient/Viewport/Warn/Woff/Xml, Fonts/* tail (Tinos*, STIX*), Main, ShapeDump,
PngDump, docs/learn, spec/*, tests/*.

## 1. Size and purpose
- Whole program: `lean-svg in.svg out.png [--width N --zoom Z --background C --viewport X Y W H --threads N --warnings]`
  (`Main.lean:3-6`). Input: SVG bytes (≤ 64 MiB, `Render.lean:50`). Output: PNG bytes (stored/uncompressed deflate,
  `spec/SizeBound.lean`), up to 16384 px/side, 16.7 M px (`Render.lean:46-48`).
- Entry: `main : List String → IO UInt32` (`Main.lean:36`) → pure `renderWithWarnings : Options → ByteArray → Except String (ByteArray × warnings)` (`Render.lean:1072`).
  Pipeline: `Xml.parse` (`Xml.lean:208`) → `Use.expand` (`Use.lean:309`) → `Svg` doc build (CSS, paint, clip, mask, filter, text, markers) → `Render.renderRgba` (`Render.lean:967`) → `Png.encode`.
- Part-2 counts (grep, approximate): ~726 `def/abbrev`, 59 `theorem` (all in `spec/`; none under `LeanSvg/`), 24 inductives, 65 structures,
  0 mutual, 0 `partial`, 0 instances/classes, 3 `macro/notation` hits (likely comments), 1 `unsafe|implemented_by` hit (a comment, `Render.lean:17`: "no unsafe").
- Largest: `Svg.lean` 5050 lines/142 defs, `Shape.lean` 1540/122, `ShapeRun.lean` 1250/80, `Text.lean` 1503, `Render.lean` 1102, `Shader.lean` 1071.
  Whole-repo def count is well over 1,500; part 2 alone is ~726 vs the 511 cap.
- Embedded font data: `LeanSvg/Fonts/*.lean`, 32 MB total of base64 `Array String` literals (e.g. `NotoSansSC.lean` ≈ 10 MB). Part 2 holds only the small Tinos/STIX ones, but the pipeline cannot do text without them.

## 2. Lean features, counts (part 2) and classification
| Feature | Count / example | Needed? | Cheapest encoding |
|---|---|---|---|
| `Nat` | ~1190 mentions | core | UInt64 + asserted bounds (coordinates are clamped to 2^30, `Fixed.lean:11-17`) |
| `Int` | ~583; `abbrev Fx := Int`, 8 fractional bits (`Fixed.lean:15-30`) | core | signed fixed point in UInt64 two's-complement; need signed div/shift ops (floor `Int.ediv` is used, `Fixed.lean:33-37`). Bounds make overflow impossible if asserted; the code states "Int is arbitrary precision, so overflow is impossible by construction" and relies on the clamp only as a cost bound, so a proof of no-overflow on products (2^30 × 2^16 = 2^46 fits) is feasible but must be done per op |
| `Array` | ~779 | core | Buf (but arrays of structures/arrays are nested, see below) |
| `ByteArray` | ~267 | core (I/O, PNG, fonts) | Buf of bytes (one word per byte, or packed) |
| `String` | ~210 (Svg 75, Css 23, Xml 19) | partly incidental: attribute names/values, element names, CSS selectors, font family names | Buf of bytes + interned tag ids; string compare = bytewise loop |
| `Char` | 24 | incidental | UInt64 |
| `Option` | ~328 | pervasive | tag word + payload; or sentinel values |
| `Except` | 31 | error paths | status word; compiler has no error channel, so use "output empty/flag" |
| `List` | 121 | mostly incidental (args, small lists) | Buf |
| `HashMap` | 12 (`Std.Data.HashMap`) | ids → elements for `use`/clip/mask/pattern lookups | open-addressing table in a Buf, or sorted Buf + binary search |
| `inductive` | 24, e.g. `Svg.Node` (`Svg.lean:492`), `Paint` (`:39`), `PaintSpec` (`:923`), `Shader.Shape/Kind/Geom/Built` (`Shader.lean:327-878`), `Text.Face/Ev/Anchor`, `Shape.Pause`, `Xml.Event` (`Xml.lean:41`) | core | tagged Buf nodes (tag word + fields); several are enums (`Spread`, `Skip`, `Match`, `Anchor`) → plain UInt64 |
| `structure` | 65 (Options, Canvas, Rgba, GroupInfo, Doc, ...) | core | field offsets in a Buf; records with arrays inside (Canvas pixel arrays, Doc node arrays) need Buf-of-Buf or a single arena |
| Recursion | 0 `partial`, 0 `mutual`, 0 `termination_by`. Loops are `for … in [0:n]` or structural recursion on explicit fuel (104 `fuel` hits in repo; `PatternRender.lean:21,238`, `Png.lean:47`, `Inflate.lean:15`) | core | `for` over range → `loop n` directly; fuel recursion → fuel loop. Genuine recursion over trees (`Svg.Node`, nested groups, `Use.expand` depth `maxDepth`, CSS) needs an explicit stack in a Buf |
| `do`/`for`/`while`/`let mut` | 686 `do`, 446 `for`, 26 `while` | pervasive | `Id.run do` loops become fuel loops with tuple state; `mut` vars → loop-carried tuples (very wide tuples; frame ≤ 250 words may bite) |
| `IO` | 31 hits, essentially only `Main.lean` | incidental | byte input/output already supported; CLI parsing (`Cli.lean`, part 1) and file existence checks can be dropped |
| Float | 0 (explicitly forbidden, `Render.lean:17`) | n/a | good: no float emulation needed |
| `UInt8/32/64` | 27/20/9 | hot paths (`Mat.apply` "fixed width", `Fixed.lean:36-40` comment) | UInt64 with masks |
| `Task.spawn` | 1 (`Render.lean:1042`, `--threads`) | incidental | drop; serial path is "the reference" (`Render.lean:30-35`) |
| typeclasses / monads | no user instances; uses `Except`/`Id.run` monads | incidental | desugar by hand |
| `native_decide`/`decide` | 29 hits, mostly in specs/tests | proofs only | n/a |

## 3. Hard blockers (ranked)
1. **Scale**: >1,500 defs repo-wide (~726 in part 2) vs 511 cap; `Svg.lean` alone is 5050 lines. Node cap 16,384 will be exceeded by the full renderer (rough estimate, uncertain).
2. **Data-structure layer**: nested structures/arrays/inductives (Doc, Node streams, Canvas layers, shaders `Shader.Built`) require a systematic memory/arena encoding plus a translation tool; no user inductives/structures today. This is the single biggest compiler/translator task.
3. **Strings and parsing**: XML, CSS (`Css.lean` part 1), attribute/number/path/color/transform parsing all work on `String`/`Char`/`List`; need byte-level rewrite. Large mechanical work, little conceptual work.
4. **Signed fixed-point ops**: `Int` floor division, `Int.toNat`, signed compare/shift on UInt64. Check whether the IR has signed ops; if not, needs added ops with proofs.
5. **Tree recursion** (`Use.expand`, nested groups/layers with `maxLayerDepth`, clip/mask/pattern/filter recursion, `use` → symbol) needs explicit stack encoding; fuel-bounded by design (`maxDepth`), so no termination proof gap.
6. **Embedded fonts (32 MB base64 in source)**: can't be in the compiler input (≤ 1 MiB). Text rendering would require fonts passed as input bytes (the repo's design already parses fonts from bytes: `Font.parseEmbedded`, `Woff.lean`). Without text, a large part is droppable.
7. **Output/work sizes**: canvas up to 16.7 M px × 4 bytes ≈ 67 MB RGBA plus layers up to `4 × maxPixels` (`Render.lean:374`) ≈ 268 MB; fits in 1 GiB only with low `--width`. Tests would use small images.
8. Frame ≤ 250 words: functions with many `let mut` (the rasterizers) may need splitting.

## 4. Runtime needs
- Input: SVG ≤ 64 MiB nominal; realistic test SVGs ≪ 1 MiB (also fits our input cap). Output: PNG; stored-block encoding so PNG size ≈ raw RGBA + small overhead (`spec/SizeBound.lean:355`, `renderWithWarnings_size_le`).
- Compute: scanline rasterization, filters (blur/lighting/turbulence in part 1 `Filter/*`), per-pixel loops; O(pixels × shapes). With a 256×256 target, fuel counts are modest; at 16 M px this is heavy.
- Def count: ~726 (part 2) before dropping fonts/filters/JPEG/GIF/Woff. A core subset (Xml, Use, Svg shapes+paint, Shape, Raster, Render, Png encode) is likely ~250-350 defs (estimate).

## 5. Easy wins (already close to the subset)
- `Fixed.lean` (part 1 file but relevant): pure arithmetic on bounded integers.
- `Png.lean` (240 lines, 20 defs, part 2): encoder with stored deflate, CRC, Adler, `be32`; loops over `ByteArray` with fuel (`Png.lean:47`); output only. Also `Gzip.lean`/`Inflate.lean` are tail-recursive-on-fuel, bit-twiddling code over bytes: near-subset after Option/ByteArray → Buf.
- `Raster.lean` (713), `Viewport.lean` (94), `Units.lean` (124), `RootFit.lean` (65), `VertOrient.lean` (63), `Synth.lean` (52): numeric, few structures.
- `PngDecode.lean`, `Woff.lean`: byte-stream decoders with Option results; fuel-bounded.
- `Xml.lean` (344, 14 defs): byte-driven with explicit caps `maxDepth`/`maxElements`; "every loop is bounded by the input size" (`Xml.lean` header); good first parsing target after rewriting `String` outputs as Buf slices.

## 6. Proof angle
- **All proofs live in `spec/`** (59 theorems, no `sorry`, only the 3 standard axioms; `spec/README.md:3-5`). `LeanSvg/` contains none (only 5 `example`s: `FamilyMatch`, `Synth`, `StixNonUnicode`).
- They are properties of the Lean source, not of our compiled code: they carry over only if we prove our translation equivalent to the original definitions, which is not practical for 700+ defs. They would be *specifications to re-check* against the compiled program, not free inherited proofs.
- Key theorems:
  - `renderWithWarnings_size_le`, `renderWithWarnings_rejects_large`, `render_output_size_bound`, `render_size_le_const`, `encode_size_le` (`spec/SizeBound.lean:216-362`): output size bound; reusable as the memory-bound spec.
  - `fillMask_local`, `compositeNormal_local`, `compositeBlend_local`, `fillMaskShader_local` (+ `_count`) (`spec/Locality.lean:94-233`): writes only inside the shape's box.
  - `svgImage_in_box`, `composite_local`, `layerBox_sub` (`spec/SvgImageLocality.lean`), `fillMaskImage_local` (`spec/ImageLocality.lean`).
  - `decode_size` (`spec/PngDecode.lean:18`), `gunzip_size_le` (`spec/Gzip.lean:16`), `parse_paths_mem` etc. (`spec/Cli.lean`), `use_maxDepth_le` (`spec/Svg.lean:14`).
  - Generic helpers `forIn_invariant`, `forIn_measure_le` (`spec/SizeBound.lean:37,60`): loop-invariant lemmas over `for` loops; conceptually the same shape as our fuel `loop`.
- None states functional correctness of rendering (no "matches resvg" theorem); correctness is checked by tests/oracle (`harness/`, `tests/`), not by proof.

## Uncertain
- Exact def totals (grep-based, counts `private def` and `abbrev`; fonts data excluded from reasoning).
- Whether part 1 ends exactly at `Pattern.lean` (nearest-boundary cut).
- Frame sizes and node counts not measured; no build attempted.
