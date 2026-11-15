# lean-svg depth probe: `render` call graph vs the front ends

Branch `leansvg-depth` (from `leansvg-verbatim`; no compiler source touched). Source: `rowancallahan/lean-svg` @ `df8e663`.

**Method.** lean-svg was built under Lean 4.29 (the compiler's toolchain) in a scratch copy with 3 edits for the 4.34→4.29 gap: a `Nat.sqrt` placeholder shim (Fixed.lean:47 `hypot` calls it; core has it only in 4.34, so `hypot` was not meaningfully tested), Css.lean:213 (`let (a, b) : T ← …` rewritten as two lets), Shape.lean:239 (`for tag in (… : Array Nat)` ascription). No other body was edited.
The call graph is **type-checked**: constants used by each elaborated definition, aux definitions folded into their parent, root `LeanSvg.render`.
`frontx_compile LeanSvg.<f>` was run on the imported definition itself (verbatim by construction), one attempt per function, `maxHeartbeats 300000`, `--tstack=4000000`.
Scripts and raw results: `Testing/leansvg/depth/` (`Graph.lean` call graph, `run1.sh`/`run2.sh` attempts, `ana.py`/`mk.py`/`gen.py` analysis, `res.json` raw per-function results).

**Numbers.** `render` reaches 3 466 constants; 2 598 are functions; **2247 are user definitions** (the rest are generated matchers/recursors). **43 compile**, all leaves: `Bytes.at'`, `Bytes.isAlpha`, `Bytes.isDigit`, `Bytes.isNameChar`, `Bytes.isWs`, `Bytes.toLower`, `ConvolveMatrix.cA`, `ConvolveMatrix.cB`, `ConvolveMatrix.cG`, `ConvolveMatrix.cR`, `Css.isIdentChar`, `Css.isIdentStart`, `F32.expo`, `F32.mant`, `FamilyMatch.suite`, `Filter.isKnownUnsupported`, `FilterApply.chA`, `FilterApply.chB`, `FilterApply.chG`, `FilterApply.chR`, `FilterApply.dispChan`, `Font.b64Digit`, `Font.cmapScore`, `Font.u8`, `ForeignObject.isWs`, `Image.b64Val`, `Image.isAsciiWs`, `Image.isTabNl`, `Image.isToken`, `Jpeg.byteAt`, `PngDecode.channels`, `PngDecode.validDepth`, `Shape.GInfo.isUnicodeMark`, `Shape.GInfo.ligId`, `Shape.Layout.base`, `Shape.Layout.hasClasses`, `Shape.isDefaultIgnorable`, `Shape.maxLenFor`, `Shape.opsFor`, `ShapeText.utf8Len`, `Synth.realWorld`, `Text.isHan`, `Text.isWordSep`.
All others are blocked (or no verdict, see §4). Only the **first** failure per function is recorded (the front end stops there), so a function's first failure is usually its signature and hides later blockers. "Transitive" = functions whose callee closure contains a function with that first failure.
Only `frontx_compile` was tried: `wa_compile` is not on this branch and `frontx_ind` needs a hand-declared `frontx_ind_type` per structure. The `ByteArray`/`Array`/structure rows are exactly what those two target, so they are not attempted here, not hopeless.

## 1. Blocker table (sorted by transitive impact)

| feature (first-failure class) | blocked directly | blocked transitively | example (file:line — message) |
|---|---|---|---|
| structure ctor / field projection / instance (user structure values) | 299 | 1709 | `BasicShape.Env.mk` BasicShape.lean:81 — frontx: no unfolding equation for LeanSvg.BasicShape.Env.mk |
| user structure / inductive as parameter or result | 517 | 1176 | `BasicShape.LP.fromEnd` BasicShape.lean:48 — frontx: unsupported result type LeanSvg.BasicShape.LP |
| Array (of scalars, tuples or structures) as value | 371 | 786 | `BasicShape.Env.pathData` BasicShape.lean:83 — frontx: unsupported result type Array LeanSvg.PathCmd |
| Int / Fx scalar (also Int tuples, Option Int) | 403 | 748 | `BasicShape.Env.len` BasicShape.lean:82 — frontx: unsupported result type Option LeanSvg.Fx |
| step proof fails (front-end limit; e.g. u8/shift facts) | 83 | 625 | `BasicShape.closeParen` BasicShape.lean:307 — frontx: could not prove i + 1 < 2 ^ 64 |
| body shape not a scalar (do-block / join point) | 34 | 323 | `Css.skipAtRule` Css.lean:182 — frontx: not a scalar: have i := i0; |
| match shape (multi-scrutinee, Bool-pair, literal patterns, Decidable.rec) | 35 | 279 | `Canvas.clipColor` Canvas.lean:636 — frontx: unsupported Bool match g.isNeg, b.isNeg with |
| Option of structure / tuple | 95 | 274 | `BasicShape.boxKeyword` BasicShape.lean:87 — frontx: unsupported result type Option LeanSvg.BasicShape.RefBox |
| recursion shape | 61 | 223 | `Grad.RtStop.a` Shader.lean:622 — frontx: recursive call not in tail position self.a |
| function-typed value (closure) | 4 | 181 | `Bytes.skipWhile` Bytes.lean:25 — frontx: unsupported parameter type UInt8 → Bool |
| String / Std.Format / Char | 41 | 180 | `BasicShape.instReprLP.repr` BasicShape.lean:44 — frontx: unsupported result type Std.Format |
| `have`/`let` binding inside a term (Nat/Bool value) | 24 | 180 | `Brotli.readVarLen8` Brotli.lean:215 — frontx: unsupported term have i := bp / 8; |
| resource: simp/whnf depth or heartbeats | 73 | 136 | `BasicShape.polygonOf` BasicShape.lean:285 — Tactic `simp` failed with a nested error: (deterministic) timeout at ` |
| variable x variable `*` (Nat), nonlinear bound | 32 | 133 | `Canvas.blendLerp` Canvas.lean:77 — frontx: unsupported term instHMul.1 (dst >>> 24 &&& 255) (255 - cov) |
| projection of non-constructor term (tuple/structure values) | 5 | 129 | `Filter.sinCosF32` Filter.lean:127 — frontx: projection of a term that is not a constructor application (ha |
| `/` `%` by a non-2^k constant (side condition not discharged) | 2 | 120 | `Font.format12Cap` Font.lean:243 — frontx: `(bs.size - (so + 16)) / 12` is translated by one conditional  |
| resource: memory/time in the front end | 18 | 107 | `Bidi.matchedBracket` Bidi.lean:335 — RESOURCE: killed (memory) |
| mutable local of structure type | 1 | 103 | `Font.scanTables` Font.lean:181 — frontx: unsupported mutable local of type LeanSvg.Font.Tables |
| indexing Array of tuples/structures (`a[i]!` default value) | 14 | 100 | `Filter.f32All` Filter.lean:398 — failed to synthesize OfNat (LeanSvg.F32 × Nat) 0 |
| monadic type (Shape.M / StateM / Except result) | 61 | 85 | `ForeignObject.breakLines` ForeignObject.lean:257 — frontx: unsupported result type Except String (Array LeanSvg.ForeignOb |
| `Option` locals with several components | 5 | 79 | `Css.lastIndexOf` Css.lean:117 — frontx: `Option` locals with a result of several components |
| `/` `%` by a variable or non-2^k expression | 6 | 77 | `Canvas.unpremul` Canvas.lean:49 — frontx: unsupported term instHDiv.1 (c * 510 + a) (2 * a) |
| loops other than `for i in [a:b]` over Id (for over Array/List, several foldl) | 11 | 60 | `Clip.chainBox` Clip.lean:173 — frontx: only `for i in [a:b]` in `Id` is supported forIn chain none fu |
| other: invalid instantiateForall, too many parameters | 2 | 24 | `Filter.Parsers.color` Filter.lean:304 — invalid instantiateForall, too many parameters |
| other: frontx: unsupported term LeanSvg.Png.crcRun4 bs (start.min ( | 1 | 19 | `Png.crc32Range` Png.lean:86 — frontx: unsupported term LeanSvg.Png.crcRun4 bs (start.min (stop.min b |
| other: frontx: unsupported term instHashableString.1 s | 2 | 19 | `Grad.hashId` Shader.lean:425 — frontx: unsupported term instHashableString.1 s |
| other: frontx: unsupported Bool (LeanSvg.FontSet.styles.getD k (400 | 1 | 14 | `Synth.oblique` Synth.lean:32 — frontx: unsupported Bool (LeanSvg.FontSet.styles.getD k (400, false, 5 |
| other: frontx: unsupported Bool String.Slice.Pattern.ForwardSliceSe | 1 | 10 | `ForeignObject.isHtml` ForeignObject.lean:399 — frontx: unsupported Bool String.Slice.Pattern.ForwardSliceSearcher.ins |
| tuple result | 2 | 8 | `Clip.build` Clip.lean:298 — frontx: unsupported result type LeanSvg.Clip.Res × LeanSvg.Clip.Cache |

## 2. Call tree of `render` (stage level; "defs below" counts include accessors)

- `render` — blocked: resource: simp/whnf depth or heartbeats — `simp` failed: maximum number of steps exceeded [Render.lean:1097]; 2247 defs below
  - `renderWithWarnings` — blocked: resource: simp/whnf depth or heartbeats — `simp` failed: maximum number of steps exceeded [Render.lean:1066]; 2246 defs below
    - `Xml.parse` — blocked: resource: simp/whnf depth or heartbeats — Tactic `simp` failed with a nested error: maximum recursion  [Xml.lean:207]; 29 defs below
      - `Xml.resolveNs` — blocked: monadic type — frontx: unsupported result type Except String LeanSvg.Xml.Sc [Xml.lean:93]; 10 defs below
      - `Xml.decodeText` — blocked: Array — frontx: unsupported result type ByteArray [Xml.lean:162]; 8 defs below
      - `Xml.decodeValue` — blocked: resource: simp/whnf depth or heartbeats — Tactic `simp` failed with a nested error: maximum recursion  [Xml.lean:136]; 7 defs below
      - `Bytes.skipWhile` — blocked: function-typed value — frontx: unsupported parameter type UInt8 → Bool [Bytes.lean:25]; 2 defs below
      - `Bytes.findByte` — blocked: step proof fails — frontx: could not prove (BExp.denote σ.env (BExp.var 7)).toN [Bytes.lean:37]; 2 defs below
      - `Bytes.skipWs` — blocked: step proof fails — frontx: could not prove (BExp.denote σ.env (BExp.var 6)).toN [Bytes.lean:32]; 4 defs below
      - `Bytes.startsWith` — blocked: step proof fails — frontx: could not prove BExp.denote (σ.env.set 8 (rN (i✝ + s [Bytes.lean:45]; 2 defs below
      - `Bytes.at'` — compiles [Bytes.lean:14]; 1 defs below
      - `Bytes.isNameChar` — compiles [Bytes.lean:21]; 3 defs below
    - `Svg.interpretWith` — blocked: resource: simp/whnf depth or heartbeats — `simp` failed: maximum number of steps exceeded [Svg.lean:3913]; 1710 defs below
      - `Svg.strokeBoxOf` — blocked: Option of structure / tuple — frontx: unsupported result type Option LeanSvg.Box [Svg.lean:3748]; 1041 defs below
      - `Svg.parseHexColor` — blocked: match shape — frontx: unsupported term match (if (bs.size - 1 != 3 && bs.s [Svg.lean:696]; 4 defs below
      - `Css.parseCompound` — blocked: structure ctor / field projection / instance — unknown free variable `_fvar.60312` [Css.lean:248]; 25 defs below
      - `Svg.resolveRootSize` — blocked: Int / Fx scalar — frontx: unsupported result type Option (LeanSvg.Fx × LeanSvg [Svg.lean:1464]; 9 defs below
    - `Marker.expand` — blocked: user structure / inductive as parameter or result — frontx: unsupported result type LeanSvg.Svg.Doc [Marker.lean:498]; 285 defs below
    - `RootFit.apply` — blocked: user structure / inductive as parameter or result — frontx: unsupported result type LeanSvg.Svg.Doc [RootFit.lean:55]; 148 defs below
    - `Render.canvasSetup` — blocked: monadic type — frontx: unsupported result type Except String (Nat × Nat × L [Render.lean:95]; 35 defs below
    - `Render.bandCount` — blocked: step proof fails — frontx: could not prove BExp.denote (σ.env.set 6 (rN (2 * th [Render.lean:1002]; 1 defs below
    - `Render.renderRgba` — blocked: resource: simp/whnf depth or heartbeats — (deterministic) timeout at `whnf`, maximum number of heartbe [Render.lean:959]; 2226 defs below
      - `Render.renderNodes` — blocked: resource: simp/whnf depth or heartbeats — (deterministic) timeout at `whnf`, maximum number of heartbe [Render.lean:558]; 2222 defs below
      - `Canvas.new` — blocked: user structure / inductive as parameter or result — frontx: unsupported result type LeanSvg.Canvas [Canvas.lean:71]; 9 defs below
      - `Canvas.toRgbaBytes` — blocked: Array — frontx: unsupported result type ByteArray [Canvas.lean:266]; 6 defs below
      - `Render.drawShape` — blocked: tuple result — frontx: unsupported result type LeanSvg.Canvas × LeanSvg.Cli [Render.lean:234]; 493 defs below
        - `Raster.rasterize` — blocked: Option of structure / tuple — frontx: unsupported result type Option LeanSvg.Raster.Mask [Raster.lean:147]; 13 defs below
        - `Canvas.fillMask` — blocked: user structure / inductive as parameter or result — frontx: unsupported result type LeanSvg.Canvas [Canvas.lean:204]; 20 defs below
        - `Mat.mul` — blocked: Int / Fx scalar — frontx: unsupported result type LeanSvg.Mat [Geom.lean:118]; 11 defs below
        - `flatten` — blocked: Array — frontx: unsupported result type Array LeanSvg.Poly [Geom.lean:290]; 33 defs below
        - `strokePoly` — blocked: Array — frontx: unsupported result type Array (Array LeanSvg.Pt) [Geom.lean:732]; 41 defs below
        - `dashPath` — blocked: Array — frontx: unsupported result type Array LeanSvg.Poly [DashSeg.lean:90]; 50 defs below
        - `Clip.resolve` — blocked: Array — frontx: unsupported result type Option (Array LeanSvg.Clip.M [Clip.lean:372]; 180 defs below
        - `Grad.build` — blocked: user structure / inductive as parameter or result — frontx: unsupported result type LeanSvg.Grad.Built [Shader.lean:924]; 83 defs below
    - `Render.renderBands` — blocked: resource: simp/whnf depth or heartbeats — (deterministic) timeout at `whnf`, maximum number of heartbe [Render.lean:1012]; 2227 defs below
    - `Png.encode` — blocked: Array — frontx: unsupported result type ByteArray [Png.lean:223]; 16 defs below
      - `Png.zlibStoredRows` — blocked: Array — frontx: unsupported result type ByteArray [Png.lean:206]; 11 defs below
      - `Png.crc32Range` — blocked: other: frontx: unsupported term LeanSvg.Png.crcRun4 bs — frontx: unsupported term LeanSvg.Png.crcRun4 bs (start.min ( [Png.lean:86]; 4 defs below
      - `Png.zlibLen` — blocked: variable x variable `*` — frontx: unsupported term instHMul.1 h (rowBytes + 1) [Png.lean:162]; 1 defs below
      - `Png.chunk` — blocked: Array — frontx: unsupported result type ByteArray [Png.lean:158]; 7 defs below
      - `Png.be32` — blocked: Array — frontx: unsupported result type ByteArray [Png.lean:154]; 1 defs below

The big stages (`render`, `renderWithWarnings`, `Xml.parse`, `interpretWith`, `renderRgba`, `renderNodes`) hit the front end's own limits (simp steps, whnf heartbeats, memory) before a feature message. Their blockers are in their signatures: structure parameters (`Options`, `Svg.Doc`, `Mat`), `Array` of structures, `Except String` of tuples/structures.

## 3. Smallest feature set to compile `render` end to end

The first-failure classes in `render`'s closure number 29 (§1, every row with a non-zero transitive count). Greedy order by functions newly unlocked (first-failure data only, so a lower bound):

1. structure ctor / field projection / instance (user structure values) — +169 (cumulative 207 of 2247)
2. user structure / inductive as parameter or result — +472 (cumulative 679 of 2247)
3. Int / Fx scalar (also Int tuples, Option Int) — +360 (cumulative 1039 of 2247)
4. Array (of scalars, tuples or structures) as value — +250 (cumulative 1289 of 2247)
5. recursion shape — +76 (cumulative 1365 of 2247)
6. step proof fails (front-end limit; e.g. u8/shift facts) — +93 (cumulative 1458 of 2247)
7. Option of structure / tuple — +88 (cumulative 1546 of 2247)
8. String / Std.Format / Char — +59 (cumulative 1605 of 2247)
9. body shape not a scalar (do-block / join point) — +54 (cumulative 1659 of 2247)
10. function-typed value (closure) — +46 (cumulative 1705 of 2247)
11. match shape (multi-scrutinee, Bool-pair, literal patterns, Decidable.rec) — +44 (cumulative 1749 of 2247)
12. variable x variable `*` (Nat), nonlinear bound — +44 (cumulative 1793 of 2247)

Needed beyond first failures, read from deeper messages: `Nat` `>>>`, variable×variable `*` and `/` by variables (`Canvas.premul/unpremul/blendLerp`, `PngDecode.to8/passLen`, `Lighting.*`), `"…".toUTF8` literals (`Bytes.findSeq`, `Svg.paintOrderKindOf`), `Shape.M` (StateM-like), closures (`Bytes.skipWhile`).
Verdict: not one or two features. Three structural gates: (a) user structures/inductives as values with `Int`/`Fx` fields, (b) `Array`/`ByteArray` results, (c) `Int` arithmetic. The Svg element tree plus `interpretWith` (~1 700 defs below) is the larger half. The nearest end-to-end subtree is the PNG encoder (`Png.encode` → `zlibStoredRows`, `crc32Range`, `zlibLen`), blocked by `ByteArray` results, var×var `*` and the `crcRun4` shape.

**Floats.** No `Float` type in the code (the only occurrence is a comment, Oklab.lean:13). Floating point is a software binary32 on `Nat` (`abbrev F32 := Nat`, Canvas.lean:343; ~40 reachable `F32.*`, plus `Lighting.*`, `Filter.f32*`, Oklab). It is integer-only but needs `>>>`, var×var `*`, `/` by variables, `have` bindings and a `bitLen` loop. **Flag:** if "floats out of scope" includes this soft-float, its users (filters, lighting, gradients, Oklab) are excluded. Fixed-point `Fx := Int` (Fixed.lean:16) carries the geometry.

## 4. Caveats
- Some functions have no verdict: the front end was killed for memory (15 chunks exited 137 and were re-run singly) and a few runs were lost when a background watcher ended. These count as blocked/"resource".
- A function is counted blocked even when only a callee blocks it; `frontx_compile` does not report the callee chain.
- Classes come from regexes over message text; rare messages remain as "other: …" rows.
